/***********************/
/* par.c               */
/* for Par 1.52-i18n.4 */
/* Copyright 2001 by   */
/* Adam M. Costello    */
/* Modified by         */
/* Jérôme Pouiller     */
/***********************/

/* This is ANSI C code (C89). */


#include "charset.h"   /* Also includes "errmsg.h". */
#include "buffer.h"    /* Also includes <stddef.h>. */
#include "reformat.h"

#include <langinfo.h>
#include <wchar.h>
#include <wctype.h>
#include <locale.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

#undef NULL
#define NULL ((void *) 0)

#ifdef DONTFREE
#define free(ptr)
#endif

static const char * const usagemsg =
"\n"
"Options for par:\n"
"\n"
"help       print option summary      "
                                 "  ---------- Boolean parameters: ---------\n"
"version    print version number      "
                                 "  b<body>   let non-trailing body chars in\n"
"B<op><set> as <op> is =/+/-,         "
                                 "            prefix, non-leading in suffix\n"
"           replace/augment/diminish  "
                                 "  c<cap>    count all words as capitalized\n"
"           body chars by <set>       "
                                 "  d<div>    use indentation as a delimiter\n"
"P<op><set> ditto for protective chars"
                                 "  E<Err>    send messages to stderr\n"
"Q<op><set> ditto for quote chars     "
                                 "  e<expel>  discard superfluous lines\n"
"-------- Integer parameters: --------"
                                 "  f<fit>    narrow paragraph for best fit\n"
"h<hang>    skip IP's 1st <hang> lines"
                                 "  g<guess>  preserve wide sentence breaks\n"
"           in scan for common affixes"
                                 "  i<invis>  hide lines inserted by <quote>\n"
"p<prefix>  prefix length             "
                                 "  j<just>   justify paragraphs\n"
"r<repeat>  if not 0, force bodiless  "
                                 "  l<last>   treat last lines like others\n"
"           lines to length <width>   "
                                 "  q<quote>  supply vacant lines between\n"
"s<suffix>  suffix length             "
                                 "            different quote nesting levels\n"
"T<Tab>     tab stops every <Tab> cols"
                                 "  R<Report> print error for too-long words\n"
"w<width>   max output line length    "
                                 "  t<touch>  move suffixes left\n"
"\n"
"See par.doc or par.1 (the man page) for more information.\n"
"\n"
;


/* Structure for recording properties of lines within segments: */

typedef unsigned char lflag_t;

typedef struct lineprop {
  short p, s;     /* Length of the prefix and suffix of a bodiless */
                  /* line, or the fallback prelen and suflen       */
                  /* of the IP containing a non-bodiless line.     */
  lflag_t flags;  /* Boolean properties (see below).               */
  wchar_t rc;     /* The repeated character of a bodiless line.    */
} lineprop;

/* Flags for marking boolean properties: */

static const lflag_t L_BODILESS = 1,  /* Bodiless line.             */
                     L_INVIS    = 2,  /* Invisible line.            */
                     L_FIRST    = 4,  /* First line of a paragraph. */
                     L_SUPERF   = 8;  /* Superfluous line.          */

#define isbodiless(prop) ( (prop)->flags & 1)
#define    isinvis(prop) (((prop)->flags & 2) != 0)
#define    isfirst(prop) (((prop)->flags & 4) != 0)
#define   issuperf(prop) (((prop)->flags & 8) != 0)
#define   isvacant(prop) (isbodiless(prop) && (prop)->rc == ' ')


static int digtoint(wchar_t c)

/* Returns the value represented by the digit c, or -1 if c is not a digit. */
{
  const wchar_t *p, * const digits = L"0123456789";

  if (!c) return -1;
  p = wcschr(digits,c);
  return  p  ?  p - digits  :  -1;

  /* We can't simply return c - '0' because this is ANSI C code,  */
  /* so it has to work for any character set, not just ones which */
  /* put the digits together in order.  Also, an array that could */
  /* be referenced as digtoint[c] might be bad because there's no */
  /* upper limit on CHAR_MAX.                                     */
}


static int strtoudec(const wchar_t *s, int *pn)

/* Converts the longest prefix of string s consisting of decimal   */
/* digits to an integer, which is stored in *pn.  Normally returns */
/* 1.  If *s is not a digit, then *pn is not changed, but 1 is     */
/* still returned.  If the integer represented is greater than     */
/* 9999, then *pn is not changed and 0 is returned.                */
{
  int n = 0, d;

  d = digtoint(*s);
  if (d < 0) return 1;

  do {
    if (n >= 1000) return 0;
    n = 10 * n + d;
    d = digtoint(*++s);
  } while (d >= 0);

  *pn = n;

  return 1;
}


static void parsearg(
  const wchar_t *arg, int *phelp, int *pversion, charset *bodychars, charset
  *protectchars, charset *quotechars, int *phang, int *pprefix, int *prepeat,
  int *psuffix, int *pTab, int *pwidth, int *pbody, int *pcap, int *pdiv, int
  *pErr, int *pexpel, int *pfit, int *pguess, int *pinvis, int *pjust, int
  *plast, int *pquote, int *pReport, int *ptouch, errmsg_t errmsg
)
/* Parses the command line argument in *arg, setting the objects pointed to */
/* by the other pointers as appropriate.  *phelp and *pversion are boolean  */
/* flags indicating whether the help and version options were supplied.     */
{
  const wchar_t *savearg = arg;
  charset *chars, *change;
  wchar_t oc;
  int n;

  *errmsg = '\0';
  
  if (*arg == L'-') ++arg;

  if (!wcscmp(arg, L"help")) {
    *phelp = 1;
    return;
  }

  if (!wcscmp(arg, L"version")) {
    *pversion = 1;
    return;
  }

  if (*arg == L'B' || *arg == L'P' || *arg == L'Q' ) {
    chars =  *arg == L'B'  ?  bodychars    :
             *arg == L'P'  ?  protectchars :
          /* *arg == L'Q' */  quotechars   ;
    ++arg;
    if (*arg != L'='  &&  *arg != L'+'  &&  *arg != L'-') goto badarg;
    change = parsecharset(arg + 1, errmsg);
    if (change) {
      if      (*arg == L'=')   csswap(chars,change);
      else if (*arg == L'+')   csadd(chars,change,errmsg);
      else  /* *arg == L'-' */ csremove(chars,change,errmsg);
      freecharset(change);
    }
    return;
  }

  if (iswdigit(*arg)) {
    if (!strtoudec(arg, &n)) goto badarg;
    if (n <= 8) *pprefix = n;
    else *pwidth = n;
  }

  for (;;) {
    while (iswdigit(*arg)) ++arg;
    oc = *arg;
    if (!oc) break;
    n = -1;
    if (!strtoudec(++arg, &n)) goto badarg;
    if (   oc == L'h' || oc == L'p' || oc == L'r'
        || oc == L's' || oc == L'T' || oc == L'w') {
      if      (oc == L'h')   *phang   =  n >= 0 ? n :  1;
      else if (oc == L'p')   *pprefix =  n;
      else if (oc == L'r')   *prepeat =  n >= 0 ? n :  3;
      else if (oc == L's')   *psuffix =  n;
      else if (oc == L'T')   *pTab    =  n >= 0 ? n :  8;
      else  /* oc == L'w' */ *pwidth  =  n >= 0 ? n : 79;
    }
    else {
      if (n < 0) n = 1;
      if (n > 1) goto badarg;
      if      (oc == L'b') *pbody   = n;
      else if (oc == L'c') *pcap    = n;
      else if (oc == L'd') *pdiv    = n;
      else if (oc == L'E') *pErr    = n;
      else if (oc == L'e') *pexpel  = n;
      else if (oc == L'f') *pfit    = n;
      else if (oc == L'g') *pguess  = n;
      else if (oc == L'i') *pinvis  = n;
      else if (oc == L'j') *pjust   = n;
      else if (oc == L'l') *plast   = n;
      else if (oc == L'q') *pquote  = n;
      else if (oc == L'R') *pReport = n;
      else if (oc == L't') *ptouch  = n;
      else goto badarg;
    }
  }

  return;

badarg:

  swprintf(errmsg, errmsg_size, L"Bad argument: %.*s\n", errmsg_size - 16, savearg);
  *phelp = 1;
}


static wchar_t **readlines(
  lineprop **pprops, const charset *protectchars,
  const charset *quotechars, int Tab, int invis, int quote, errmsg_t errmsg
)
/* Reads lines from stdin until EOF, or until a line beginning with a   */
/* protective character is encountered (in which case the protective    */
/* character is pushed back onto the input stream), or until a blank    */
/* line is encountered (in which case the newline is pushed back onto   */
/* the input stream).  Returns a NULL-terminated array of pointers to   */
/* individual lines, stripped of their newline characters.  Every NUL   */
/* character is stripped, and every white character is changed to a     */
/* space unless it is a newline.  If quote is 1, vacant lines will be   */
/* supplied as described for the q option in par.doc.  *pprops is set   */
/* to an array of lineprop structures, one for each line, each of whose */
/* flags field is either 0 or L_INVIS (the other fields are 0).  If     */
/* there are no lines, *pprops is set to NULL.  The returned array may  */
/* be freed with freelines().  *pprops may be freed with free() if      */
/* it's not NULL.  On failure, returns NULL and sets *pprops to NULL.   */
{
  buffer *cbuf = NULL, *lbuf = NULL, *lpbuf = NULL;
  wint_t c;
  int empty, blank, firstline, qsonly, oldqsonly = 0, vlnlen, i;
  wchar_t *ln = NULL, nullchar = L'\0', *nullline = NULL, *qpend, 
    *oldln = NULL, *oldqpend = NULL, *p, *op, *vln = NULL, **lines = NULL;
  lineprop vprop = { 0, 0, 0, '\0' }, iprop = { 0, 0, 0, '\0' };

  /* oldqsonly, oldln, and oldquend don't really need to be initialized.   */
  /* They are initialized only to appease compilers that try to be helpful */
  /* by issuing warnings about unitialized automatic variables.            */

  iprop.flags = L_INVIS;
  *errmsg = '\0';

  *pprops = NULL;

  cbuf = newbuffer(sizeof (wchar_t), errmsg);
  if (*errmsg) goto rlcleanup;
  lbuf = newbuffer(sizeof (wchar_t *), errmsg);
  if (*errmsg) goto rlcleanup;
  lpbuf = newbuffer(sizeof (lineprop), errmsg);
  if (*errmsg) goto rlcleanup;

  for (empty = blank = firstline = 1;  ;  ) {
    c = getwchar();
    if (c == WEOF) {
      if (errno == EILSEQ) {
      	wcscpy(errmsg, L"Invalid multibyte sequence in input\n");
	goto rlcleanup;
      }
      break;
    }
    if (c == L'\n') {
      if (blank) {
        ungetwc(c,stdin);
        break;
      }
      additem(cbuf, &nullchar, errmsg);
      if (*errmsg) goto rlcleanup;
      ln = copyitems(cbuf,errmsg);
      if (*errmsg) goto rlcleanup;
      if (quote) {
        for (qpend = ln;  *qpend && csmember(*qpend, quotechars);  ++qpend);
        for (p = qpend;  *p == L' ' || csmember(*p, quotechars);  ++p);
        qsonly =  (*p == L'\0');
        while (qpend > ln && qpend[-1] == L' ') --qpend;
        if (!firstline) {
          for (p = ln, op = oldln;
               p < qpend && op < oldqpend && *p == *op;
               ++p, ++op);
          if (!(p == qpend && op == oldqpend)) {
            if (!invis && (oldqsonly || qsonly)) {
              if (oldqsonly) {
                *op = L'\0';
                oldqpend = op;
              }
              if (qsonly) {
                *p = L'\0';
                qpend = p;
              }
            }
            else {
              vlnlen = p - ln;
              vln = malloc((vlnlen + 1) * sizeof (wchar_t));
              if (!vln) {
                wcscpy(errmsg,outofmem);
                goto rlcleanup;
              }
              wcsncpy(vln, ln, vlnlen);
              vln[vlnlen] = L'\0';
              additem(lbuf, &vln, errmsg);
              if (*errmsg) goto rlcleanup;
              additem(lpbuf,  invis ? &iprop : &vprop,  errmsg);
              if (*errmsg) goto rlcleanup;
              vln = NULL;
            }
          }
        }
        oldln = ln;
        oldqpend = qpend;
        oldqsonly = qsonly;
      }
      additem(lbuf, &ln, errmsg);
      if (*errmsg) goto rlcleanup;
      ln = NULL;
      additem(lpbuf, &vprop, errmsg);
      if (*errmsg) goto rlcleanup;
      clearbuffer(cbuf);
      empty = blank = 1;
      firstline = 0;
    }
    else {
      if (empty) {
        if (csmember(c, protectchars)) {
          ungetwc(c,stdin);
          break;
        }
        empty = 0;
      }
      if (!c) continue;
      if (c == L'\t') {
        c = L' ';
        for (i = Tab - numitems(cbuf) % Tab;  i > 0;  --i) {
          additem(cbuf, &c, errmsg);
          if (*errmsg) goto rlcleanup;
        }
        continue;
      }
      if (iswspace(c)) 
        c = L' ';
      else 
        blank = 0;
      additem(cbuf, &c, errmsg);
      if (*errmsg) 
        goto rlcleanup;
    }
  }
  
  if (!blank) {
    additem(cbuf, &nullchar, errmsg);
    if (*errmsg) goto rlcleanup;
    ln = copyitems(cbuf,errmsg);
    if (*errmsg) goto rlcleanup;
    additem(lbuf, &ln, errmsg);
    if (*errmsg) goto rlcleanup;
    ln = NULL;
    additem(lpbuf, &vprop, errmsg);
    if (*errmsg) goto rlcleanup;
  }

  additem(lbuf, &nullline, errmsg);
  if (*errmsg) goto rlcleanup;
  *pprops = copyitems(lpbuf,errmsg);
  if (*errmsg) goto rlcleanup;
  lines = copyitems(lbuf,errmsg);

rlcleanup:

  if (cbuf) freebuffer(cbuf);
  if (lpbuf) freebuffer(lpbuf);
  if (lbuf) {
    if (!lines)
      for (;;) {
        lines = nextitem(lbuf);
        if (!lines) break;
        free(*lines);
      }
    freebuffer(lbuf);
  }
  if (ln) free(ln);
  if (vln) free(vln);

  return lines;
}


static void compresuflen(
  const wchar_t * const *lines, const wchar_t * const *endline,
  const charset *bodychars, int body, int pre, int suf, int *ppre, int *psuf
)
/* lines is an array of strings, up to but not including endline.  */
/* Writes into *ppre and *psuf the comprelen and comsuflen of the  */
/* lines in lines.  Assumes that they have already been determined */
/* to be at least pre and suf.  endline must not equal lines.      */
{
  const wchar_t *start, *end, *knownstart, * const *line, *p1, *p2, *knownend,
             *knownstart2;
           
  start = *lines;
  end = knownstart = start + pre;
  if (body)
    while (*end) ++end;
  else
    while (*end && !csmember(*end, bodychars)) ++end;
  for (line = lines + 1;  line < endline;  ++line) {
    for (p1 = knownstart, p2 = *line + pre;
         p1 < end && *p1 == *p2;
         ++p1, ++p2);
    end = p1;
  }
  if (body)
    for (p1 = end;  p1 > knownstart;  )
      if (*--p1 != L' ') {
        if (csmember(*p1, bodychars))
          end = p1;
        else
          break;
      }
  *ppre = end - start;

  knownstart = *lines + *ppre;
  for (end = knownstart;  *end;  ++end);
  knownend = end - suf;
  if (body)
    start = knownstart;
  else
    for (start = knownend;
         start > knownstart && !csmember(start[-1], bodychars);
         --start);
  for (line = lines + 1;  line < endline;  ++line) {
    knownstart2 = *line + *ppre;
    for (p2 = knownstart2;  *p2;  ++p2);
    for (p1 = knownend, p2 -= suf;
         p1 > start && p2 > knownstart2 && p1[-1] == p2[-1];
         --p1, --p2);
    start = p1;
  }
  if (body) {
    for (p1 = start;
         start < knownend && (*start == L' ' || csmember(*start, bodychars));
         ++start);
    if (start > p1 && start[-1] == L' ') --start;
  }
  else
    while (end - start >= 2 && *start == L' ' && start[1] == L' ') ++start;
  *psuf = end - start;
}


static void delimit(
  const wchar_t * const *lines, const wchar_t * const *endline,
  const charset *bodychars, int repeat, int body, int div,
  int pre, int suf, lineprop *props
)
/* lines is an array of strings, up to but not including     */
/* endline.  Sets fields in each lineprop in the parallel    */
/* array props as appropriate, except for the L_SUPERF flag, */
/* which is never set.  It is assumed that the comprelen     */
/* and comsuflen of the lines in lines have already been     */
/* determined to be at least pre and suf, respectively.      */
{
  const wchar_t * const *line, *end, *p, * const *nextline;
  wchar_t rc;
  lineprop *prop, *nextprop;
  int anybodiless = 0, status;

  if (endline == lines) return;

  if (endline == lines + 1) {
    props->flags |= L_FIRST;
    props->p = pre, props->s = suf;
    return;
  }

  compresuflen(lines, endline, bodychars, body, pre, suf, &pre, &suf);

  line = lines, prop = props;
  do {
    prop->flags |= L_BODILESS;
    prop->p = pre, prop->s = suf;
    for (end = *line;  *end;  ++end);
    end -= suf;
    p = *line + pre;
    rc =  p < end  ?  *p  :  L' ';
    if (rc != L' ' && (!repeat || end - p < repeat))
      prop->flags &= ~L_BODILESS;
    else
      while (p < end) {
        if (*p != rc) {
          prop->flags &= ~L_BODILESS;
          break;
        }
        ++p;
      }
    if (isbodiless(prop)) {
      anybodiless = 1;
      prop->rc = rc;
    }
    ++line, ++prop;
  } while (line < endline);

  if (anybodiless) {
    line = lines, prop = props;
    do {
      if (isbodiless(prop)) {
        ++line, ++prop;
        continue;
      }

      for (nextline = line + 1, nextprop = prop + 1;
           nextline < endline && !isbodiless(nextprop);
           ++nextline, ++nextprop);

      delimit(line,nextline,bodychars,repeat,body,div,pre,suf,prop);

      line = nextline, prop = nextprop;
    } while (line < endline);

    return;
  }

  if (!div) {
    props->flags |= L_FIRST;
    return;
  }

  line = lines, prop = props;
  status = ((*lines)[pre] == L' ');
  do {
    if (((*line)[pre] == L' ') == status)
      prop->flags |= L_FIRST;
    ++line, ++prop;
  } while (line < endline);
}


static void marksuperf(
  const wchar_t * const * lines, const wchar_t * const * endline, lineprop *props
)
/* lines points to the first line of a segment, and endline to one  */
/* line beyond the last line in the segment.  Sets L_SUPERF bits in */
/* the flags fields of the props array whenever the corresponding   */
/* line is superfluous.  L_BODILESS bits must already be set.       */
{
  const wchar_t * const *line, *p;
  lineprop *prop, *mprop, dummy;
  int inbody, num, mnum;

  for (line = lines, prop = props;  line < endline;  ++line, ++prop)
    if (isvacant(prop))
      prop->flags |= L_SUPERF;

  inbody = mnum = 0;
  mprop = &dummy;
  for (line = lines, prop = props;  line < endline;  ++line, ++prop)
    if (isvacant(prop)) {
      for (num = 0, p = *line;  *p;  ++p)
        if (*p != L' ') ++num;
      if (inbody || num < mnum)
        mnum = num, mprop = prop;
      inbody = 0;
    } else {
      if (!inbody) mprop->flags &= ~L_SUPERF;
      inbody = 1;
    }
} 


static void setaffixes(
  const wchar_t * const *inlines, const wchar_t * const *endline,
  const lineprop *props, const charset *bodychars,
  const charset *quotechars, int hang, int body, int quote,
  int *pafp, int *pfs, int *pprefix, int *psuffix
)
/* inlines is an array of strings, up to but not including endline,    */
/* representing an IP.  inlines and endline must not be equal.  props  */
/* is the the parallel array of lineprop structures.  *pafp and *pfs   */
/* are set to the augmented fallback prelen and fallback suflen of the */
/* IP.  If either of *pprefix, *psuffix is less than 0, it is set to a */
/* default value as specified in "par.doc".                            */
{
  int numin, pre, suf;
  const wchar_t *p;

  numin = endline - inlines;

  if ((*pprefix < 0 || *psuffix < 0)  &&  numin > hang + 1)
    compresuflen(inlines + hang, endline, bodychars, body, 0, 0, &pre, &suf);

  p = *inlines + props->p;
  if (numin == 1 && quote)
    while (*p && csmember (*p, quotechars))
      ++p;
  *pafp = p - *inlines;
  *pfs = props->s;

  if (*pprefix < 0)
    *pprefix  =  numin > hang + 1  ?  pre  :  *pafp;

  if (*psuffix < 0)
    *psuffix  =  numin > hang + 1  ?  suf  :  *pfs;
}


static void freelines(wchar_t **lines)
/* Frees the elements of lines, and lines itself. */
/* lines is a NULL-terminated array of strings.   */
{
  wchar_t **line;

  for (line = lines;  *line;  ++line)
    free(*line);

  free(lines);
}

int main(int argc, const char * const *argv)
{
  int help = 0, version = 0, hang = 0, prefix = -1, repeat = 0, suffix = -1,
      Tab = 1, width = 72, body = 0, cap = 0, div = 0, Err = 0, expel = 0,
      fit = 0, guess = 0, invis = 0, just = 0, last = 0, quote = 0, Report = 0,
      touch = -1;
  int prefixbak, suffixbak, sawnonblank, oweblank, n, i, afp, fs;
  charset *bodychars = NULL, *protectchars = NULL, *quotechars = NULL;
  wint_t c;
  wchar_t *state;
  wchar_t *parinit = NULL, *arg, **inlines = NULL, **endline, **firstline, *end,
    **nextline, **outlines = NULL, **line;
  const char *env;
  wchar_t *wenv = NULL;
  const wchar_t * const whitechars = L" \f\n\r\t\v";
  errmsg_t errmsg = { '\0' };
  lineprop *props = NULL, *firstprop, *nextprop;
  FILE *errout;
  char *langinfo;

/* Set the current locale from the environment: */

  setlocale(LC_ALL,"");
  langinfo = nl_langinfo(CODESET);
  if (!strcmp(langinfo, "ANSI_X3.4-1968")) {
    // We would like to fallback in an 8 bits encoding, but it is not easily possible.
    //setlocale(LC_CTYPE, "C");
    //langinfo = nl_langinfo(CODESET);
    fwprintf( Err ? stderr : stdout, 
        L"Warning: Locale seems not configured\n");
  }

/* Process environment variables: */

  env = getenv("PARBODY");
  if (!env) env = "";
  wenv = malloc((strlen(env) + 1) * sizeof (wchar_t));
  if (!wenv) {
    wcscpy(errmsg,outofmem);
    goto parcleanup;
  }
  if (0 > mbstowcs(wenv,env, strlen(env) + 1)) {
    wcscpy(errmsg, L"Invalid multibyte sequence in PARBODY\n");
    goto parcleanup;
  }
  bodychars = parsecharset(wenv,errmsg);
  if (*errmsg) {
    help = 1;
    goto parcleanup;
  }
  free(wenv);
  wenv = NULL;

  env = getenv("PARPROTECT");
  if (!env) env = "";
  wenv = malloc((strlen(env) + 1) * sizeof (wchar_t));
  if (!wenv) {
    wcscpy(errmsg,outofmem);
    goto parcleanup;
  }
  if (0 > mbstowcs(wenv,env, strlen(env) + 1)) {
    wcscpy(errmsg, L"Invalid multibyte sequence in PARPROTECT\n");
    goto parcleanup;
  }
  protectchars = parsecharset(wenv,errmsg);
  if (*errmsg) {
    help = 1;
    goto parcleanup;
  }
  free(wenv);
  wenv = NULL;

  env = getenv("PARQUOTE");
  if (!env) env = "> ";
  wenv = malloc((strlen(env) + 1) * sizeof (wchar_t));
  if (!wenv) {
    wcscpy(errmsg,outofmem);
    goto parcleanup;
  }
  if (0 > mbstowcs(wenv,env, strlen(env) + 1)) {
    wcscpy(errmsg, L"Invalid multibyte sequence in PARQUOTE\n");
    goto parcleanup;
  }
  quotechars = parsecharset(wenv,errmsg);
  if (*errmsg) {
    help = 1;
    goto parcleanup;
  }
  free(wenv);
  wenv = NULL;

  env = getenv("PARINIT");
  if (env) {
    parinit = malloc((strlen(env) + 1) * sizeof (wchar_t));
    if (!parinit) {
      wcscpy(errmsg,outofmem);
      goto parcleanup;
    }
    if (0 > mbstowcs(parinit,env, strlen(env) + 1)) {
      wcscpy(errmsg, L"Invalid multibyte sequence in PARINIT\n");
      goto parcleanup;
    }    
    arg = wcstok(parinit, whitechars, &state);
    while (arg) {
      parsearg(arg, &help, &version, bodychars, protectchars,
               quotechars, &hang, &prefix, &repeat, &suffix, &Tab,
               &width, &body, &cap, &div, &Err, &expel, &fit, &guess,
               &invis, &just, &last, &quote, &Report, &touch, errmsg );
      if (*errmsg || help || version) goto parcleanup;
      arg = wcstok(NULL, whitechars, &state);
    }
    free(parinit);
    parinit = NULL;
  }

/* Process command line arguments: */

  while (*++argv) {
    arg = malloc((strlen(*argv) + 1) * sizeof (wchar_t));
    if (0 > mbstowcs(arg, *argv, strlen(*argv) + 1)) {
      wcscpy(errmsg, L"Invalid multibyte sequence in argument\n");
      goto parcleanup;
    }
    parsearg(arg, &help, &version, bodychars, protectchars,
             quotechars, &hang, &prefix, &repeat, &suffix, &Tab,
             &width, &body, &cap, &div, &Err, &expel, &fit, &guess,
             &invis, &just, &last, &quote, &Report, &touch, errmsg );
    free(arg);
    if (*errmsg || help || version) goto parcleanup;
  }

  if (Tab == 0) {
    wcscpy(errmsg, L"<Tab> must not be 0.\n");
    goto parcleanup;
  }

  if (touch < 0) touch = fit || last;
  prefixbak = prefix;
  suffixbak = suffix;
  
  /* Main loop: */
  for (sawnonblank = oweblank = 0;  ;  ) {
    for (;;) {
      c = getwchar();
      if (c == WEOF) {
        if (errno == EILSEQ) {
          wcscpy(errmsg, L"Invalid multibyte sequence in input\n");
          goto parcleanup;
        }
        break;
      }
      if (expel && c == L'\n') {
        oweblank = sawnonblank;
        continue;
      }
      if (csmember(c, protectchars)) {
        sawnonblank = 1;
        if (oweblank) {
          fputwc(L'\n', stdout);
          oweblank = 0;
        }
        while (c != L'\n') {
          putwchar(c);
          c = getwchar();
          if (c == WEOF) {
            if (errno == EILSEQ) {
              wcscpy(errmsg, L"Invalid multibyte sequence in input\n");
              goto parcleanup;
            }
            break;
          }
        }
      }
      if (c != L'\n') break;  /* subsumes the case that c == EOF */
      putwchar(c);
    }
    if (c == WEOF) break;
    ungetwc(c,stdin);

    inlines =
      readlines(&props, protectchars, quotechars, Tab, invis, quote, errmsg);
    if (*errmsg) goto parcleanup;
    for (endline = inlines;  *endline;  ++endline) ;
    if (endline == inlines) {
      free(inlines);
      inlines = NULL;
      continue;
    }

    sawnonblank = 1;
    if (oweblank) {
      fputwc(L'\n', stdout);
      oweblank = 0;
    }

    delimit((const wchar_t * const *) inlines,
            (const wchar_t * const *) endline,
            bodychars, repeat, body, div, 0, 0, props);

    if (expel)
      marksuperf((const wchar_t * const *) inlines,
                 (const wchar_t * const *) endline, props);

    firstline = inlines, firstprop = props;

    do {
      if (isbodiless(firstprop)) {
        if (!isinvis(firstprop) && !(expel && issuperf(firstprop))) {
          for (end = *firstline;  *end;  ++end);
          if (!repeat || (firstprop->rc == L' ' && !firstprop->s)) {
            while (end > *firstline && end[-1] == L' ') --end;
            *end = L'\0';
            fwprintf(stdout, L"%ls\n", *firstline);
          }
          else {
            n = width - firstprop->p - firstprop->s;
            if (n < 0) {
              swprintf(errmsg,errmsg_size,impossibility,5);
              goto parcleanup;
            }
            fwprintf(stdout, L"%.*ls", firstprop->p, *firstline);
            for (i = n;  i;  --i)
              fputwc(firstprop->rc, stdout);
            fwprintf(stdout, L"%ls\n", end - firstprop->s);
          }
        }
        ++firstline, ++firstprop;
        continue;
      }

      for (nextline = firstline + 1, nextprop = firstprop + 1;
           nextline < endline && !isbodiless(nextprop) && !isfirst(nextprop);
           ++nextline, ++nextprop);
      
      prefix = prefixbak, suffix = suffixbak;
      setaffixes((const wchar_t * const *) firstline,
                 (const wchar_t * const *) nextline, firstprop, bodychars,
                 quotechars, hang, body, quote, &afp, &fs, &prefix, &suffix);
      if (width <= prefix + suffix) {
        swprintf(errmsg,errmsg_size,
                L"<width> (%d) <= <prefix> (%d) + <suffix> (%d)\n",
                width, prefix, suffix);
        goto parcleanup;
      }

      outlines =
        reformat((const wchar_t * const *) firstline,
                 (const wchar_t * const *) nextline,
                 afp, fs, hang, prefix, suffix, width, cap,
                 fit, guess, just, last, Report, touch, errmsg);
      if (*errmsg) goto parcleanup;
      for (line = outlines;  *line;  ++line)
        fwprintf(stdout, L"%ls\n", *line);
      freelines(outlines);
      outlines = NULL;

      firstline = nextline, firstprop = nextprop;
    } while (firstline < endline);

    freelines(inlines);
    inlines = NULL;

    free(props);
    props = NULL;
  }

parcleanup:
  if (wenv) free(wenv);
  if (bodychars) freecharset(bodychars);
  if (protectchars) freecharset(protectchars);
  if (quotechars) freecharset(quotechars);
  if (parinit) free(parinit);
  if (inlines) freelines(inlines);
  if (props) free(props);
  if (outlines) freelines(outlines);

  errout = Err ? stderr : stdout;
  if (*errmsg) fwprintf(errout, L"par error:\n%.*ls", errmsg_size, errmsg);
#ifdef NOWIDTH
  if (version) fputws(L"par 1.52-i18n.4 (without wcwidth() support)\n",errout);
#else
  if (version) fputws(L"par 1.52-i18n.4\n",errout);
#endif
  if (help)    fputs(usagemsg,errout);

  return *errmsg ? EXIT_FAILURE : EXIT_SUCCESS;
}
