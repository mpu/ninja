/*% cc -g -std=c99 -Wall -Wextra % -o #
 * miniyacc - port of ninja.ml, LALR(1) grammars.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned Sym;
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
};

int nr, ns;
Rule *rs;
Info *is;

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
	r = bsearch(&k, rs, nr, sizeof *r, rcmp);
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

	for (i=&is[LastTok]; i-is<ns; i++)
		i->fst = salloc(0);
	do {
		chg = 0;
		for (r=rs; r-rs<nr; r++) {
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

#if 0
int
tcmpv(void *a, void *b)
{
	return tcmp(a, b);
}
#endif

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

	i1 = (Item){ 0, 0 };
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

	ns = sizeof infos / sizeof infos[0];
	nr = sizeof rules / sizeof rules[0];
	is = infos;
	rs = rules;

	ginit();
	for (Info *i=&is[LastTok]; i-is<ns; i++) {
		printf("Symbol %s\n", i->name);
		printf("  Nullable: %s\n", i->nul ? "yes" : "no");
		printf("  First:   ");
		for (Sym *s=i->fst; *s!=S; s++)
			printf(" %s", is[*s].name);
		printf("\n");
	}

	Item i0 = {0,0};
	Sym *s = salloc(1);
	s[0] = NT(-1);
	iadd(&i0, &(Term){ .rule = rfind(NT(3)), .dot = 0, .look = s });
	iclose(&i0);
	Item i1 = igoto(&i0, 4);

	Item i = i1;
	printf("\nInitial closure:\n");
	for (Term *t=i.ts; t-i.ts<i.nt; t++) {
		int n = 0;
		Rule *r = t->rule;
		int d = t->dot;
		n += printf("  %s ->", is[r->lhs].name);
		for (Sym *s=r->rhs; *s!=S; s++, d--)
			n += printf(" %s%s", d ? "" : ". ", is[*s].name);
		if (!d)
			n += printf(" .");
		while (n++<30)
			putchar(' ');
		printf("[");
		for (Sym *s=t->look; *s!=S; s++)
			printf(" %s", is[*s].name);
		printf(" ]\n");
	}

	exit(0);
}
