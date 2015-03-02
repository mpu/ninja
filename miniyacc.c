/*% cc -g -std=c99 -Wall -Wextra % -o #
 * miniyacc - port of ninja.ml, LALR(1) grammars.
 */
#include <assert.h>
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

struct Rule {
	Sym lhs;
	Sym *rhs;
	char *action;
};

struct Info {
	char *name;
	int nul;
	Sym *fst;
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
Rule *rs;  /* grammar rules (ordered, rcmp) */
Info *is;  /* symbol information */
Item **st; /* LALR(1) states (ordered, icmp) */
Row *as;   /* action table [state][tok] */
Row *gs;   /* goto table   [sym][state] */

int srconf, rrconf;
int actsz;
int *act;
int *chk;
int *adsp;
int *gdsp;

void
die(char *s)
{
	fprintf(stderr, "%s\n", s);
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

	for (i=&is[ntk]; i-is<nsy; i++)
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
		assert(r);
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

Item *
stgen(Sym sstart)
{
	Sym *eof, s;
	Rule *r;
	Item *start, *i, *i1;
	int n;

	start = yalloc(1, sizeof *start);
	*start = NulItem;
	r = rfind(sstart);
	assert(r);
	eof = salloc(1);
	eof[0] = 0;
	iadd(start, &(Term){ r, 0, eof });
	iclose(start);
	stadd(&start);
	for (;;) {
		for (n=0;; n++) {
			if (n>=nst)
				return start;
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

void
tblset(int *tbl, Item *i, Term *t)
{
	Sym s, *l;

	s = t->rule->rhs[t->dot];
	if (s!=S) {
		/* shift/goto */
		if (s>=ntk)
			return;
		assert(i->gtbl[s]);
		if (tbl[s] && s<ntk && tbl[s] != i->gtbl[s]->id) {
			assert(tbl[s] < 0);
			printf(srs, i->id, is[s].name);
			srconf++;
		}
		tbl[s] = i->gtbl[s]->id;
	} else
		/* reduce */
		for (l=t->look; (s=*l)!=S; l++) {
			/* default to shift if conflict occurs */
			if (tbl[s]<0) {
				printf(rrs, i->id, is[s].name);
				rrconf++;
			} else if (tbl[s]>0) {
				printf(srs, i->id, is[s].name);
				srconf++;
			} else
				tbl[s] = Red(t->rule-rs);
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
	gs = yalloc(nsy-ntk, sizeof gs[0]);
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
	for (n=ntk; n<nsy; n++) {
		r = &gs[n-ntk];
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
	nnt = nsy-ntk;
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
	n = nst*nsy;
	printf("\nOptimizer report\n");
	printf("  Tables size: %d\n", n);
	printf("  Space savings: %.2g\n", (float)(n-actsz)/n);
}

void
aout(char *name, int *t, int n)
{
	int i;

	printf("short %s[] = {", name);
	for (i=0; i<n; i++) {
		if (i % 10 == 0)
			printf("\n");
		printf("%4d", t[i]);
		if (i == n-1)
			printf("\n};\n");
		else
			printf(", ");
	}
}

void
tblout()
{
	int *o, n;

	printf("short yyntoks = %d;\n", ntk);
	o = yalloc(nrl+nst+nsy, sizeof o[0]);
	for (n=0; n<nrl; n++)
		o[n] = smem(rs[n].rhs, S);
	aout("yyr1", o, nrl);
	for (n=0; n<nrl; n++)
		o[n] = rs[n].lhs-ntk;
	aout("yyr2", o, nrl);
	for (n=0; n<nst; n++)
		o[n] = as[n].def;
	aout("yyadef", o, nst);
	for (n=0; n<nsy-ntk; n++) {
		o[n] = gs[n].def;
		assert(o[n]>0 || o[n]==-1);
		if (o[n]>0)
			o[n]--;
	}
	aout("yygdef", o, nsy-ntk);
	aout("yyadsp", adsp, nst);
	aout("yygdsp", gdsp, nsy-ntk);
	for (n=0; n<actsz; n++)
		if (act[n]>=0) {
			assert(act[n]!=0);
			act[n]--;
		}
	aout("yyact", act, actsz);
	aout("yychk", chk, actsz);
	free(o);
}

void
dumpitem(Item *i)
{
	Term *t;
	Sym *s;
	int n, d;
	Rule *r;

	for (t=i->ts; t-i->ts<i->nt; t++) {
		n = 0;
		r = t->rule;
		d = t->dot;
		n += printf("  %s ->", is[r->lhs].name);
		for (s=r->rhs; *s!=S; s++, d--)
			n += printf(" %s%s", d ? "" : ". ", is[*s].name);
		if (!d)
			n += printf(" .");
		while (n++<30)
			putchar(' ');
		printf(" [");
		for (s=t->look; *s!=S; s++)
			printf(" %s", is[*s].name);
		printf(" ]\n");
	}
}

int
main()
{

#define NTOKS 7
#define NT(n) (NTOKS + n)

	Info infos[] = {
	/* Tokens */
	[0]     = { .name = "$" },
	[1]     = { .name = "Num" },
	[2]     = { .name = "+" },
	[3]     = { .name = "-" },
	[4]     = { .name = "*" },
	[5]     = { .name = "(" },
	[6]     = { .name = ")" },
	/* Non-terminals */
	[NT(0)] = { .name = "A" },
	[NT(1)] = { .name = "M" },
	[NT(2)] = { .name = "B" },
	[NT(3)] = { .name = "S" },
	};

	Rule rules[] = {
	{ NT(0), (Sym[]){ NT(1), S },           "A -> M" },
	{ NT(0), (Sym[]){ NT(0), 2, NT(1), S }, "A -> A + M" },
	{ NT(0), (Sym[]){ NT(0), 3, NT(1), S }, "A -> A - M" },
	{ NT(1), (Sym[]){ NT(2), S },           "M -> B" },
	{ NT(1), (Sym[]){ NT(1), 4, NT(2), S }, "M -> M * B" },
	{ NT(2), (Sym[]){ 1, S },               "B -> Num" },
	{ NT(2), (Sym[]){ 5, NT(0), 6, S },     "B -> ( A )" },
	{ NT(3), (Sym[]){ NT(0), 0, S },        "S -> A $" },
	};

	ntk = NTOKS;
	nsy = sizeof infos / sizeof infos[0];
	nrl = sizeof rules / sizeof rules[0];
	is = infos;
	rs = rules;

	ginit();
	for (Info *i=&is[ntk]; i-is<nsy; i++) {
		printf("Symbol %s\n", i->name);
		printf("  Nullable: %s\n", i->nul ? "yes" : "no");
		printf("  First:   ");
		for (Sym *s=i->fst; *s!=S; s++)
			printf(" %s", is[*s].name);
		printf("\n");
	}
	stgen(NT(3));
	for (int n=0; n<nst; n++) {
		printf("\nState %d:\n", n);
		dumpitem(st[n]);
	}
	tblgen();
	actgen();
	tblout();

	exit(0);
}
