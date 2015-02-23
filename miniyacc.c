/*% cc -g -std=c99 -Wall -Wextra % -o #
 * miniyacc - port of ninja.ml, LALR(1) grammars.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

typedef unsigned Sym;
typedef struct Rule Rule;
typedef struct Info Info;

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
	return ((Rule *)b)->lhs - ((Rule *)a)->lhs;
}

Rule *
rfind(Sym lhs)
{
	Rule *r;
	Rule k;

	k.lhs = lhs;
	r = bsearch(&k, rs, nr, sizeof *r, rcmp);
	if (r != 0) {
		while (r > rs && r->lhs == lhs)
			r--;
	}
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
	free(*pa);
	*pa = l;
	return ch;
}

Sym *
first(Sym *stnc, Sym last)
{
	Sym f, *s;

	f = stnc[0];
	if (f == S) {
		assert(last < LastTok);
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

void
ginit()
{
	int chg;
	Rule *r;
	Info *i;
	Sym *s;

	for (i=&is[LastTok]; i-is<ns; i++) {
		i->nul = 0;
		i->fst = salloc(0);
		i->fst[0] = S;
	}
	do {
		chg = 0;
		for (r=rs; r-rs<nr; r++) {
			i = &is[r->lhs];
			if (r->rhs[0] == S) {
				chg |= i->nul == 0;
				i->nul = 1;
				continue;
			}
			s = first(r->rhs, LastTok);
			chg |= sunion(&i->fst, s);
			free(s);
		}
	} while (chg);
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

	return 0;
}
