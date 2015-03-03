/*% clang -g -std=c99 -Wall -Wextra % -o #
 * miniyacc - port of ninja.ml, LALR(1) grammars.
 */
#include <assert.h>
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef int Sym;
typedef struct Rule Rule;
typedef struct Info Info;
typedef struct Term Term;
typedef struct Item Item;
typedef struct Row Row;

#define S ((Sym) -1)
#define NulItem (Item){0,0,0,0}
#define Red(n) (- (n+2)) /* involutive, Red(Red(x)) == x */

enum {
	IdntSz = 64,
	MaxRhs = 32,
	MaxTk = 500,
	MaxNt = 500,
	MaxRl = 1000,

	Start = MaxTk,
};

struct Rule {
	Sym lhs;
	Sym rhs[MaxRhs];
	char *act;
	int actln;
	int prec;
};

struct Info {
	int nul;
	Sym *fst;
	int prec;
	enum {
		ANone,
		ALeft,
		ARight,
		ANonassoc,
	} assoc;
	char name[IdntSz];
	char type[IdntSz];
};

struct Term {
	Rule *rule;
	int dot;
	Sym *look;
};

struct Item {
	Term *ts;
	int nt;
	Item **gtbl;
	int id;
};

struct Row {
	int def;
	int ndef;
	int *t;
};

char srs[] = "shift/reduce conflict state %d token %s\n";
char rrs[] = "reduce/reduce conflict state %d token %s\n";

int nrl, nsy, nst, ntk;
Rule rs[MaxRl]; /* grammar rules (ordered, rcmp) */
Info is[MaxTk+MaxNt]; /* symbol information */
Item **st; /* LALR(1) states (ordered, icmp) */
Row *as;   /* action table [state][tok] */
Row *gs;   /* goto table   [sym][state] */
Sym sstart;/* start symbol */
Item *ini; /* initial state */
int doty;  /* type-checking enabled */

int srconf, rrconf;
int actsz;
int *act;
int *chk;
int *adsp;
int *gdsp;

int lineno = 1;
char *fins;
FILE *fin;
FILE *fout;
FILE *fgrm;

void
die(char *s)
{
	fprintf(stderr, "%s (on line %d)\n", s, lineno);
	exit(1);
}

void *
yalloc(size_t n, size_t o)
{
	void *p;

	p = calloc(n, o);
	if (!p)
		die("out of memory");
	return p;
}

int
rcmp(const void *a, const void *b)
{
	return ((Rule *)a)->lhs - ((Rule *)b)->lhs;
}

Rule *
rfind(Sym lhs)
{
	Rule *r;
	Rule k;

	k.lhs = lhs;
	r = bsearch(&k, rs, nrl, sizeof *r, rcmp);
	if (r != 0)
		while (r > rs && r[-1].lhs == lhs)
			r--;
	return r;
}

Sym *
salloc(int n)
{
	Sym *s;

	s = yalloc(n+1, sizeof s[0]);
	s[n] = S;
	return s;
}

int
smem(Sym *l, Sym s)
{
	int n;

	for (n=0; *l!=s && *l!=S; n++, l++);
	return n;
}

int
sunion(Sym **pa, Sym *b)
{
	Sym *l, *p, *a;
	int ch;

	a = *pa;
	l = salloc(smem(a, S) + smem(b, S));
	p = l;
	ch = 0;
	while (*a!=S || *b!=S) {
		if (*a==S || (*b!=S && *b<*a)) {
			*p++ = *b++;
			ch = 1;
		}
		else {
			if (*a==*b)
				b++;
			*p++ = *a++;
		}
	}
	*p = S;
	if (ch) {
		free(*pa);
		*pa = l;
	} else
		free(l);
	return ch;
}

Sym *
first(Sym *stnc, Sym last)
{
	Sym f, *s;

	f = stnc[0];
	if (f == S) {
		assert(last==S || last<ntk);
		f = last;
	}
	if (f < ntk) {
		s = salloc(1);
		s[0] = f;
		return s;
	}
	if (is[f].nul)
		s = first(stnc+1, last);
	else
		s = salloc(0);
	sunion(&s, is[f].fst);
	return s;
}

/* Note: this requires that i->nul is initially false
 * for all entries in the information table. i->fst
 * can be garbage for tokens.
 */
void
ginit()
{
	int chg;
	Rule *r;
	Info *i;
	Sym *s;

	for (i=&is[MaxTk]; i-is<nsy; i++)
		i->fst = salloc(0);
	do {
		chg = 0;
		for (r=rs; r-rs<nrl; r++) {
			i = &is[r->lhs];
			for (s=r->rhs; *s!=S; s++)
				if (!is[*s].nul)
					goto nonul;
			chg |= i->nul == 0;
			i->nul = 1;
		nonul:
			s = first(r->rhs, S);
			chg |= sunion(&i->fst, s);
			free(s);
		}
	} while (chg);
}

int
tcmp(Term *a, Term *b)
{
	int c;

	c = a->rule - b->rule;
	if (c==0)
		c = a->dot - b->dot;
	return c;
}

int
iadd(Item *i, Term *t1)
{
	Term *t;
	int n, c;

	for (n=0, t=i->ts; n<i->nt; n++, t++) {
		c = tcmp(t, t1);
		if (c==0)
			return sunion(&t->look, t1->look);
		if (c>0)
			break;
	}
	i->nt++;
	i->ts = realloc(i->ts, i->nt * sizeof *t1);
	if (!i->ts)
		die("out of memory");
	t = &i->ts[n];
	memmove(t+1, t, (i->nt - (n+1)) * sizeof *t1);
	*t = *t1;
	t1->look = 0;
	return 1;
}

void
iclose(Item *i)
{
	Rule *r;
	Term *t, t1;
	Sym s, *rem, *l;
	int chg, n;

again:
	for (n=0, t=i->ts; n<i->nt; n++, t++) {
		rem = &t->rule->rhs[t->dot];
		s = *rem++;
		if (s < ntk || s == S)
			continue;
		r = rfind(s);
		if (!r)
			die("some non-terminals are not defined");
		l = t->look;
		assert(*l!=S);
		do {
			t1.rule = r;
			t1.dot = 0;
			t1.look = first(rem, *l);
			chg = iadd(i, &t1);
			free(t1.look);
			if (chg)
				goto again;
			if (*++l==S) {
				l = t->look;
				r++;
			}
		} while (r->lhs == s);
	}
}

Item
igoto(Item *i, Sym s)
{
	Term *t, t1;
	Item i1;
	int n;

	i1 = NulItem;
	for (n=0, t=i->ts; n<i->nt; n++, t++) {
		if (t->rule->rhs[t->dot] != s)
			continue;
		t1.rule = t->rule;
		t1.dot = t->dot + 1;
		t1.look = salloc(0);
		sunion(&t1.look, t->look);
		iadd(&i1, &t1);
	}
	iclose(&i1);
	return i1;
}

int
icmp(Item *a, Item *b)
{
	int n, c;

	c = b->nt - a->nt;
	for (n=0; !c && n<a->nt; n++)
		c = tcmp(&a->ts[n], &b->ts[n]);
	return c;
}

void
stadd(Item **pi)
{
	Item *i, *i1;
	int lo, hi, mid, n;

	/* http://www.iq0.com/duffgram/bsearch.c */
	i = *pi;
	lo = 0;
	hi = nst - 1;
	if (hi<0 || icmp(i, st[hi])>0)
		hi++;
	else if (icmp(i, st[lo])<=0)
		hi = lo;
	else
		while (hi-lo!=1) {
			mid = (lo+hi)/2;
			if (icmp(st[mid], i)<0)
				lo = mid;
			else
				hi = mid;
		}
	if (hi<nst && icmp(st[hi], i)==0) {
		i1 = st[hi];
		for (n=0; n<i->nt; n++) {
			sunion(&i1->ts[n].look, i->ts[n].look);
			free(i->ts[n].look);
		}
		free(i->ts);
		free(i);
		*pi = i1;
	} else {
		st = realloc(st, ++nst * sizeof st[0]);
		if (!st)
			die("out of memory");
		memmove(&st[hi+1], &st[hi], (nst-1 - hi) * sizeof st[0]);
		st[hi] = i;
	}
}

void
stgen()
{
	Sym *eof, s;
	Rule *r;
	Item *start, *i, *i1;
	int n;

	ini = i = yalloc(1, sizeof *start);
	*i = NulItem;
	r = rfind(Start);
	assert(r);
	eof = salloc(1);
	eof[0] = 0;
	iadd(i, &(Term){ r, 0, eof });
	iclose(i);
	stadd(&i);
	for (;;) {
		for (n=0;; n++) {
			if (n>=nst)
				return;
			i = st[n];
			if (!i->gtbl)
				break;
		}
		i->gtbl = yalloc(nsy, sizeof i->gtbl[0]);
		for (s=0; s<nsy; s++) {
			i1 = yalloc(1, sizeof *i1);
			*i1 = igoto(i, s);
			if (!i1->nt) {
				free(i1);
				i->gtbl[s] = 0;
				continue;
			}
			stadd(&i1);
			i->gtbl[s] = i1;
		}
	}
}

int
resolve(Rule *r, Sym s, int st)
{
	if (!r->prec || !is[s].prec) {
	conflict:
		if (fgrm)
			fprintf(fgrm, srs, st, is[s].name);
		srconf++;
		return ARight;
	}
	if (r->prec==is[s].prec) {
		if (is[s].assoc == ANone)
			goto conflict;
		return is[s].assoc;
	} else
		if (r->prec<is[s].prec)
			return ARight;
		else
			return ALeft;
}

void
tblset(int *tbl, Item *i, Term *t)
{
	int act;
	Sym s, *l;

	s = t->rule->rhs[t->dot];
	if (s!=S) {
		/* shift */
		if (s>=ntk)
			return;
		assert(i->gtbl[s]);
		act = ARight;
		if (tbl[s] && tbl[s] != i->gtbl[s]->id) {
			assert(tbl[s]<=0);
			act = resolve(&rs[Red(tbl[s])], s, i->id-1);
		}
		switch (act) {
		case ARight:
			tbl[s] = i->gtbl[s]->id;
			break;
		case ANonassoc:
			tbl[s] = -1;
			break;
		}
	} else
		/* reduce */
		for (l=t->look; (s=*l)!=S; l++) {
			/* default to shift if conflict occurs */
			if (!tbl[s])
				act = ALeft;
			else if (tbl[s]<0) {
				if (fgrm)
					fprintf(fgrm, rrs, i->id-1, is[s].name);
				rrconf++;
				act = ARight;
			} else
				act = resolve(t->rule, s, i->id-1);
			switch (act) {
			case ALeft:
				tbl[s] = Red(t->rule-rs);
				break;
			case ANonassoc:
				tbl[s] = -1;
				break;
			}
		}
}

void
setdef(Row *r, int w, int top)
{
	int n, m, x, cnt, def, max;

	max = 0;
	def = -1;
	r->ndef = 0;
	for (n=0; n<w; n++) {
		x = r->t[n];
		if (x==0)
			r->ndef++;
		if (x>=top || x==0)
			continue;
		cnt = 1;
		for (m=n+1; m<w; m++)
			if (r->t[m]==x)
				cnt++;
		if (cnt>max) {
			def = x;
			max = cnt;
		}
	}
	r->def = def;
	if (max!=0)
		/* zero out the most frequent entry */
		for (n=0; n<w; n++)
			if (r->t[n]==def) {
				r->t[n] = 0;
				r->ndef++;
			}
}

void
tblgen()
{
	Row *r;
	Item *i;
	int n, m;

	for (n=0; n<nst; n++)
		st[n]->id = n+1;
	as = yalloc(nst, sizeof as[0]);
	gs = yalloc(nsy-MaxTk, sizeof gs[0]);
	/* fill action table */
	for (n=0; n<nst; n++) {
		r = &as[n];
		r->t = yalloc(ntk, sizeof r->t[0]);
		for (i=st[n], m=0; m<i->nt; m++)
			tblset(r->t, i, &i->ts[m]);
		setdef(r, ntk, -1);
		r->def = Red(r->def); /* Red(-1) == -1 */
	}
	/* fill goto table */
	for (n=MaxTk; n<nsy; n++) {
		r = &gs[n-MaxTk];
		r->t = yalloc(nst, sizeof r->t[0]);
		for (m=0; m<nst; m++)
			if (st[m]->gtbl[n])
				r->t[m] = st[m]->gtbl[n]->id;
		setdef(r, nst, nst+1);
	}
}

int
prcmp(const void *a, const void *b)
{
	return (*(Row **)a)->ndef - (*(Row **)b)->ndef;
}

void
actgen()
{
	Row **o, *r;
	int n, m, t, dsp, nnt;

	actsz = 0;
	o = yalloc(nst+nsy, sizeof o[0]);
	act = yalloc(nst*nsy, sizeof act[0]);
	chk = yalloc(nst*nsy, sizeof chk[0]);
	adsp = yalloc(nst, sizeof adsp[0]);
	for (n=0; n<nst*nsy; n++)
		chk[n] = -1;
	/* fill in actions */
	for (n=0; n<nst; n++)
		o[n] = &as[n];
	qsort(o, nst, sizeof o[0], prcmp);
	for (n=0; n<nst; n++) {
		r = o[n];
		dsp = 0;
		for (m=0; m<ntk && r->t[m]==0; m++)
			dsp--;
	retrya:
		/* The invariant here is even
		 * trickier than it looks.
		 */
		for (t=0; t<ntk; t++)
			if ((m=dsp+t)>=0 && chk[m]>=0)
			if ((r->t[t] && (chk[m]!=t || act[m]!=r->t[t]))
			|| (!r->t[t] && chk[m]==t)) {
				dsp++;
				goto retrya;
			}
		adsp[r-as] = dsp;
		for (t=0; t<ntk; t++)
			if (r->t[t]) {
				chk[dsp+t] = t;
				act[dsp+t] = r->t[t];
				if (dsp+t>=actsz)
					actsz = dsp+t+1;
			}
	}
	/* fill in gotos */
	nnt = nsy-MaxTk;
	gdsp = yalloc(nnt, sizeof gdsp[0]);
	for (n=0; n<nnt; n++)
		o[n] = &gs[n];
	qsort(o, nnt, sizeof o[0], prcmp);
	for (n=0; n<nnt; n++) {
		r = o[n];
		dsp = 0;
		for (m=0; m<nst && r->t[m]==0; m++)
			dsp--;
	retryg:
		for (t=m; t<nst; t++)
			if (chk[dsp+t]>=0 && r->t[t]) {
				dsp++;
				goto retryg;
			}
		gdsp[r-gs] = dsp;
		for (t=m; t<nst; t++)
			if (r->t[t]) {
				chk[dsp+t] = ntk+(r-gs);
				act[dsp+t] = r->t[t];
				if (dsp+t>=actsz)
					actsz = dsp+t+1;
			}
	}
	free(o);
	if (fgrm) {
		n = nst*(nsy-MaxTk + ntk);
		fprintf(fgrm, "\nOptimizer report\n");
		fprintf(fgrm, "  Tables size: %d\n", n);
		fprintf(fgrm, "  Space savings: %.2g\n", (float)(n-actsz)/n);
	}
}

void
aout(char *name, int *t, int n)
{
	int i;

	fprintf(fout, "short %s[] = {", name);
	for (i=0; i<n; i++) {
		if (i % 10 == 0)
			fprintf(fout, "\n");
		fprintf(fout, "%4d", t[i]);
		if (i == n-1)
			fprintf(fout, "\n};\n");
		else
			fprintf(fout, ",");
	}
}

void
tblout()
{
	int *o, n, m;

	fprintf(fout, "short yyini = %d;\n", ini->id-1);
	fprintf(fout, "short yyntoks = %d;\n", ntk);
	o = yalloc(nrl+nst+nsy, sizeof o[0]);
	for (n=0; n<nrl; n++)
		o[n] = smem(rs[n].rhs, S);
	aout("yyr1", o, nrl);
	for (n=0; n<nrl; n++)
		o[n] = rs[n].lhs-MaxTk;
	aout("yyr2", o, nrl);
	for (n=0; n<nst; n++)
		o[n] = as[n].def;
	aout("yyadef", o, nst);
	for (n=0; n<nsy-MaxTk; n++) {
		o[n] = gs[n].def;
		assert(o[n]>0 || o[n]==-1);
		if (o[n]>0)
			o[n]--;
	}
	aout("yygdef", o, nsy-MaxTk);
	aout("yyadsp", adsp, nst);
	aout("yygdsp", gdsp, nsy-MaxTk);
	for (n=0; n<actsz; n++)
		if (act[n]>=0) {
			/* assert(act[n]!=0); I think, this is wrong. */
			act[n]--;
		}
	aout("yyact", act, actsz);
	aout("yychk", chk, actsz);
	for (n=0; n<128; n++) {
		o[n] = 0;
		for (m=0; m<ntk; m++)
			if (is[m].name[0]=='\'')
			if (is[m].name[1]==n)
				assert(!o[n]), o[n] = m;
	}
	m = 128;
	for (n=1; n<ntk; n++) {
		if (is[n].name[0]=='\'')
			continue;
		fprintf(fout, "#define %s %d\n", is[n].name, m);
		o[m++] = n;
	}
	aout("yytrns", o, m);
	free(o);
}

void
stdump()
{
	Term *t;
	Sym *s;
	int n, m, d;
	Rule *r;
	Info *i;

	if (!fgrm)
		return;
	for (i=&is[MaxTk]; i-is<nsy; i++) {
		fprintf(fgrm, "Symbol %s\n", i->name);
		fprintf(fgrm, "  Nullable: %s\n", i->nul ? "yes" : "no");
		fprintf(fgrm, "  First:   ");
		for (s=i->fst; *s!=S; s++)
			fprintf(fgrm, " %s", is[*s].name);
		fprintf(fgrm, "\n");
	}
	for (m=0; m<nst; m++) {
		fprintf(fgrm, "\nState %d:\n", m);
		for (t=st[m]->ts; t-st[m]->ts<st[m]->nt; t++) {
			n = 0;
			r = t->rule;
			d = t->dot;
			n += fprintf(fgrm, "  %s ->", is[r->lhs].name);
			for (s=r->rhs; *s!=S; s++, d--)
				n += fprintf(fgrm, " %s%s", d ? "" : ". ", is[*s].name);
			if (!d)
				n += fprintf(fgrm, " .");
			while (n++<50)
				fputc(' ', fgrm);
			fprintf(fgrm, " [");
			for (s=t->look; *s!=S; s++)
				fprintf(fgrm, " %s", is[*s].name);
			fprintf(fgrm, " ]\n");
		}
	}
	fprintf(fgrm, "\n");
}

enum {
	TIdnt,
	TTokchr, /* 'c' */
	TPP, /* %% */
	TLL, /* %{ */
	TLangle, /* < */
	TRangle, /* > */
	TSemi, /* ; */
	TBar, /* | */
	TColon, /* : */
	TLBrack, /* { */
	TUnion,
	TType,
	TToken,
	TRight,
	TLeft,
	TNonassoc,
	TPrec,
	TStart,
	TEof,
};

struct {
	char *name;
	int tok;
} words[] = {
	{ "%%", TPP },
	{ "%union", TUnion },
	{ "%type", TType },
	{ "%token", TToken },
	{ "%right", TRight },
	{ "%left", TLeft },
	{ "%nonassoc", TNonassoc },
	{ "%prec", TPrec },
	{ "%start", TStart },
	{ 0, 0 }
};

char idnt[IdntSz];

int
istok(int c)
{
	return isalnum(c) || c=='_' || c=='%';
}

int
nexttk()
{
	int n;
	char c, *p;

	while (isspace(c=fgetc(fin)))
		if (c == '\n')
			lineno++;
	switch (c) {
	case '<':
		return TLangle;
	case '>':
		return TRangle;
	case ';':
		return TSemi;
	case '|':
		return TBar;
	case ':':
		return TColon;
	case '{':
		return TLBrack;
	case EOF:
		return TEof;
	case '\'':
		idnt[0] = '\'';
		idnt[1] = fgetc(fin);
		idnt[2] = '\'';
		idnt[3] = 0;
		if (fgetc(fin)!='\'')
			die("syntax error, invalid char token");
		return TTokchr;
	}
	p = idnt;
	while (istok(c)) {
		*p++ = c;
		if (p-idnt >= IdntSz-1)
			die("identifier too long");
		c = fgetc(fin);
	}
	*p = 0;
	if (strcmp(idnt, "%")==0)
	if (c=='{')
		return TLL;
	ungetc(c, fin);
	for (n=0; words[n].name; n++)
		if (strcmp(idnt, words[n].name) == 0)
			return words[n].tok;
	return TIdnt;
}

char *
cpycode()
{
	int c, nest, len, pos;
	char *s;

	len = 64;
	s = yalloc(len+1, 1);
	s[0] = '{';
	pos = 1;
	nest = 1;

	while (nest) {
		c = fgetc(fin);
		if (c == '{')
			nest++;
		if (c == '}')
			nest--;
		if (c == EOF)
			die("syntax error, unclosed code block");
		if (c == '\n')
			lineno++;
		if (pos>=len)
		if (!(s=realloc(s, len=2*len+1)))
			die("out of memory");
		s[pos++] = c;
	}
	s[pos] = 0;
	return s;
}

int
gettype(char *type)
{
	int tk;

	tk = nexttk();
	if (tk==TLangle) {
		if (nexttk()!=TIdnt)
			die("syntax error, ident expected after <");
		strcpy(type, idnt);
		if (nexttk()!=TRangle)
			die("syntax error, unclosed <");
		return nexttk();
	} else {
		type[0] = 0;
		return tk;
	}
}

Sym
findsy(char *name, int add)
{
	int n;

	for (n=0; n<nsy; n++) {
		if (n == ntk) {
			if (name[0]=='\'') {
				if (ntk>=MaxTk)
					die("too many tokens");
				ntk++;
				strcpy(is[n].name, name);
				return n;
			}
			n = MaxTk;
		}
		if (strcmp(is[n].name, name)==0)
			return n;
	}
	if (add) {
		if (nsy>=MaxTk+MaxNt)
			die("too many non-terminals");
		strcpy(is[nsy].name, name);
		return nsy++;
	} else
		return nsy;
}

void
getdecls()
{
	int tk, prec, p, a, c, c1, n;
	Info *si;
	char type[IdntSz], *s;

	strcpy(is[0].name, "$");
	ntk = 1;
	strcpy(is[Start].name, "@start");
	nsy = MaxTk+1;
	sstart = S;
	prec = 0;
	tk = nexttk();
	for (;;)
	switch (tk) {
	case TStart:
		tk = nexttk();
		if (tk!=TIdnt)
			die("syntax error, ident expected after %start");
		sstart = findsy(idnt, 1);
		if (sstart<ntk)
			die("%start cannot specify a token");
		tk = nexttk();
		break;
	case TUnion:
		tk = nexttk();
		if (tk!=TLBrack)
			die("syntax error, { expected after %union");
		fprintf(fout, "#line %d \"%s\"\n", lineno, fins);
		s = cpycode();
		fprintf(fout, "typedef union %s YYSTYPE;\n", s);
		free(s);
		doty = 1;
		tk = nexttk();
		break;
	case TLeft:
		p = ++prec;
		a = ALeft;
		goto addtoks;
	case TRight:
		p = ++prec;
		a = ARight;
		goto addtoks;
	case TNonassoc:
		p = ++prec;
		a = ANonassoc;
		goto addtoks;
	case TToken:
		p = 0;
		a = ANone;
	addtoks:
		tk = gettype(type);
		while (tk==TIdnt || tk==TTokchr) {
			si = 0;
			n = findsy(idnt, 0);
			if (n>=MaxTk && n<nsy)
				die("non-terminal redeclared as token");
			if (n==nsy) {
				if (ntk>=MaxTk)
					die("too many tokens");
				n = ntk++;
			}
			si = &is[n];
			strcpy(si->name, idnt);
			strcpy(si->type, type);
			si->prec = p;
			si->assoc = a;
			tk = nexttk();
		}
		break;
	case TType:
		tk = gettype(type);
		if (type[0]==0)
			die("syntax error, type expected");
		while (tk==TIdnt) {
			si = 0;
			n = findsy(idnt, 1);
			if (n<ntk)
				die("token redeclared as non-terminal");
			if (n==nsy) {
				nsy++;
			}
			si = &is[n];
			strcpy(si->name, idnt);
			strcpy(si->type, type);
			tk = nexttk();
		}
		break;
	case TLL:
		fprintf(fout, "#line %d \"%s\"\n", lineno, fins);
		for (;;) {
			c = fgetc(fin);
			if (c == EOF)
				die("syntax error, unclosed %{");
			if (c == '%') {
				c1 = fgetc(fin);
				if (c1 == '}') {
					fputs("\n", fout);
					break;
				}
				ungetc(c1, fin);
			}
			if (c == '\n')
				lineno++;
			fputc(c, fout);
		}
		tk = nexttk();
		break;
	case TPP:
		if (!doty)
			fprintf(fout, "typedef int YYSTYPE;\n");
		return;
	case TEof:
		die("syntax error, unfinished declarations");
	default:
		die("syntax error, declaration expected");
	}
}

void
getgram()
{
	extern char *retcode;
	int tk;
	Sym hd, *p, s;
	Rule *r;

	for (;;) {
		tk = nexttk();
		if (tk==TPP || tk==TEof) {
			if (sstart==S)
				die("syntax error, empty grammar");
			r = &rs[nrl++];
			r->lhs = Start;
			r->rhs[0] = sstart;
			r->rhs[1] = 0;
			r->rhs[2] = S;
			r->act = retcode;
			qsort(rs, nrl, sizeof rs[0], rcmp);
			return;
		}
		if (tk!=TIdnt)
			die("syntax error, production rule expected");
		if (nexttk()!=TColon)
			die("syntax error, colon expected after production's head");
		hd = findsy(idnt, 1);
		if (sstart==S)
			sstart = hd;
		do {
			if (nrl>=MaxRl-1)
				die("too many rules");
			r = &rs[nrl++];
			r->lhs = hd;
			r->act = 0;
			p = r->rhs;
			while ((tk=nexttk())==TIdnt || tk==TTokchr || tk==TPrec) {
				if (tk==TPrec) {
					tk = nexttk();
					if (tk!=TIdnt
					|| (s=findsy(idnt, 0))>=ntk)
						die("token expected after %prec");
					r->prec = is[s].prec;
					continue;
				}
				s = findsy(idnt, 1);
				*p++ = s;
				if (s<ntk && is[s].prec>0)
					r->prec = is[s].prec;
				if (p-r->rhs >= MaxRhs-1)
					die("production rule too long");
			}
			*p = S;
			if (tk==TLBrack) {
				r->actln = lineno;
				r->act = cpycode();
				tk = nexttk();
			}
		} while (tk==TBar);
		if (tk!=TSemi)
			die("syntax error, ; or | expected");
	}
}

void
actout(Rule *r)
{
	long l;
	int i, ar;
	char c, *p, *ty, tya[IdntSz];

	ar = smem(r->rhs, S);
	p = r->act;
	i = r->actln;
	if (!p)
		return;
	while ((c=*p++))
	switch (c) {
	case '\n':
		i++;
	default:
		fputc(c, fout);
		break;
	case '$':
		c = *p++;
		if (c == '$') {
			fprintf(fout, "yyval");
			if (doty) {
				ty = is[r->lhs].type;
				if (!ty[0]) {
					lineno = i;
					die("$$ has no type");
				}
				fprintf(fout, ".%s", ty);
			}
		}
		else if (c == '<') {
			ty = tya;
			while (istok(*p) && ty-tya<IdntSz-1)
				*ty++ = *p++;
			*ty = 0;
			if (*p++!='>') {
				lineno = i;
				die("unclosed tag field");
			}
			ty = tya;
			c = *p++;
			if (c == '$') {
				fprintf(fout, "yyval.%s", ty);
			} else {
				if (!isdigit(c)) {
					lineno = i;
					die("number or $ expected afer tag field");
				}
				goto readnum;
			}
		}
		else if (isdigit(c)) {
			ty = 0;
		readnum:
			l = strtol(p-1, &p, 10);
			if (l > ar) {
				lineno = i;
				die("invalid $n");
			}
			fprintf(fout, "ps[%d].val", (int)l);
			if (doty) {
				if (!ty && l>0)
					ty = is[r->rhs[l-1]].type;
				if (!ty || !ty[0]) {
					lineno = i;
					die("$n has no type");
				}
				fprintf(fout, ".%s", ty);
			}
		}
	}
	fputs("\n", fout);
}

void
codeout()
{
	extern char *code0[], *code1[];
	char **p;
	Rule *r;
	int n, c;

	for (p=code0; *p; p++)
		fputs(*p, fout);
	for (n=0; n<nrl; n++) {
		fprintf(fout, "\tcase %d:\n", n);
		r = &rs[n];
		fprintf(fout, "#line %d \"%s\"\n", r->actln, fins);
		actout(r);
		fputs("\t\tbreak;\n", fout);
	}
	for (p=code1; *p; p++)
		fputs(*p, fout);
	fprintf(fout, "#line %d \"%s\"\n", lineno, fins);
	while ((c=fgetc(fin))!=EOF)
		fputc(c, fout);
}

void
init(int ac, char *av[])
{
	int vflag;
	char buf[100];
	char *f, *p;

	if (ac<2)
		die("no input file");
	vflag = 0;
	f = av[1];
	if (strcmp(f, "-v")==0) {
		if (ac<3)
			die("no input file");
		f = av[2];
		vflag = 1;
	}
	fins = f;
	fin = fopen(f, "r");
	p = strrchr(f, '.');
	if (p)
		*p = 0;
	snprintf(buf, sizeof buf, "%s.tab.c", f);
	fout = fopen(buf, "w");
	snprintf(buf, sizeof buf, "%s.grm", f);
	if (vflag)
		fgrm = fopen(buf, "w");
	if (!fin || !fout)
		die("cannot open work files");
	if (p)
		*p = '.';
}

int
main(int ac, char *av[])
{

	init(ac, av);
	getdecls();
	getgram();
	ginit();
	stgen();
	stdump();
	tblgen();
	actgen();
	tblout();
	codeout();

	if (srconf)
		fprintf(stderr, "%d shift/reduce conflicts\n", srconf);
	if (rrconf)
		fprintf(stderr, "%d reduce/reduce conflicts\n", rrconf);

	exit(0);
}

/* Glorious macros.
	|sed 's|.*|"&\\n",|'
*/

char *retcode = "\t\tyyval = ps[1].val; return 0;";

char *code0[] = {
"\n",
"YYSTYPE yylval;\n",
"\n",
"int\n",
"yyparse()\n",
"{\n",
"	enum {\n",
"		StackSize = 100,\n",
"		ActSz = sizeof yyact / sizeof yyact[0],\n",
"	};\n",
"	struct {\n",
"		YYSTYPE val;\n",
"		int state;\n",
"	} stk[StackSize], *ps;\n",
"	int r, h, n, s, tk;\n",
"	YYSTYPE yyval;\n",
"\n",
"	ps = stk;\n",
"	ps->state = s = yyini;\n",
"	tk = -1;\n",
"loop:\n",
"	if (tk <= 0)\n",
"		tk = yytrns[yylex()];\n",
"	n = yyadsp[s] + tk;\n",
"	if (n < 0 || n >= ActSz || yychk[n] != tk) {\n",
"		r = yyadef[s];\n",
"		if (r < 0)\n",
"			return -1;\n",
"		goto reduce;\n",
"	}\n",
"	n = yyact[n];\n",
"	if (n == -1)\n",
"		return -1;\n",
"	if (n < 0) {\n",
"		r = - (n+2);\n",
"		goto reduce;\n",
"	}\n",
"	tk = -1;\n",
"	yyval = yylval;\n",
"stack:\n",
"	ps++;\n",
"	if (ps-stk >= StackSize)\n",
"		return -2;\n",
"	s = n;\n",
"	ps->state = s;\n",
"	ps->val = yyval;\n",
"	goto loop;\n",
"reduce:\n",
"	ps -= yyr1[r];\n",
"	h = yyr2[r];\n",
"	s = ps->state;\n",
"	n = yygdsp[h] + s;\n",
"	if (n < 0 || n >= ActSz || yychk[n] != yyntoks+h)\n",
"		n = yygdef[h];\n",
"	else\n",
"		n = yyact[n];\n",
"	switch (r) {\n",
0
};

char *code1[] = {
"	}\n",
"	goto stack;\n",
"}\n",
0
};
