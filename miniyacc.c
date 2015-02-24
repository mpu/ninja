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

#define S ((Sym) -1)
#define LastTok 128

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
};

int nrl, nsy, nst;
Rule *rs;
Info *is;
Item **st;

void
die(char *s)
{
	fprintf(stderr, "%s\n", s);
	exit(1);
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

	s = malloc((n+1) * sizeof *s);
	if (!s)
		die("out of memory");
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
		assert(last==S || last<LastTok);
		f = last;
	}
	if (f < LastTok) {
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

	for (i=&is[LastTok]; i-is<nsy; i++)
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
		if (s < LastTok || s == S)
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

	i1 = (Item){ 0, 0, 0 };
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
		st = realloc(st, ++nst * sizeof *st);
		if (!st)
			die("out of memory");
		memmove(&st[hi+1], &st[hi], (nst-1 - hi) * sizeof *st);
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

	start = malloc(sizeof *i);
	if (!start)
		die("out of memory");
	*start = (Item){ 0, 0, 0};
	r = rfind(sstart);
	assert(r);
	eof = salloc(1);
	eof[0] = (LastTok-1);                         /* FIXME */
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
		i->gtbl = malloc(nsy * sizeof i1);
		if (!i->gtbl)
			die("out of memory");
		for (s=0; s<nsy; s++) {
			i1 = malloc(sizeof *i1);
			if (!i1)
				die("out of memory");
			*i1 = igoto(i, s);
			iclose(i1);
			stadd(&i1);
			i->gtbl[s] = i1;
		}
	}
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
		printf("[");
		for (s=t->look; *s!=S; s++)
			printf(" %s", is[*s].name);
		printf(" ]\n");
	}
}

int
main()
{

#define NT(n) (LastTok + n)

	Info infos[] = {
	/* Tokens */
	[0]     = { .name = "Num" },
	[1]     = { .name = "+" },
	[2]     = { .name = "-" },
	[3]     = { .name = "*" },
	[4]     = { .name = "(" },
	[5]     = { .name = ")" },
	[NT(-1)]= { .name = "EOF" },
	/* Non-terminals */
	[NT(0)] = { .name = "A" },
	[NT(1)] = { .name = "M" },
	[NT(2)] = { .name = "B" },
	[NT(3)] = { .name = "S" },
	};

	Rule rules[] = {
	{ NT(0), (Sym[]){ NT(1), S },           "A -> M" },
	{ NT(0), (Sym[]){ NT(0), 1, NT(1), S }, "A -> A + M" },
	{ NT(0), (Sym[]){ NT(0), 2, NT(1), S }, "A -> A - M" },
	{ NT(1), (Sym[]){ NT(2), S },           "M -> B" },
	{ NT(1), (Sym[]){ NT(1), 3, NT(2), S }, "M -> M * B" },
	{ NT(2), (Sym[]){ 0, S },               "B -> Num" },
	{ NT(2), (Sym[]){ 4, NT(0), 5, S },     "B -> ( A )" },
	{ NT(3), (Sym[]){ NT(0), S },           "S -> A" },
	};

	nsy = sizeof infos / sizeof infos[0];
	nrl = sizeof rules / sizeof rules[0];
	is = infos;
	rs = rules;

	ginit();
	for (Info *i=&is[LastTok]; i-is<nsy; i++) {
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

	exit(0);
}
