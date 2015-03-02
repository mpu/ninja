/*% cc -Wall -g -o # %
 */
#define YYSTYPE int

YYSTYPE yylval, yyval;
int lex(void);

short yyntoks = 7;
short yyr1[] = {
   1,    3,    3,    1,    3,    1,    3,    1
};
short yyr2[] = {
   0,    0,    0,    1,    1,    2,    2,    3
};
short yyadef[] = {
  -1,   -1,   -1,   -1,   -1,    7,   -1,    0,    1,    2,
   3,    4,    5,    6
};
short yygdef[] = {
   4,    7,   10,   -1
};
short yyadsp[] = {
   1,    1,    1,    1,   -2,    5,    1,   -1,   -1,   -1,
  -7,   -7,   -7,   -7
};
short yygdsp[] = {
   4,    7,    5,  -14
};
short yyact[] = {
   2,    3,   12,    6,   13,    5,    0,    2,    3,    8,
   9,   11
};
short yychk[] = {
   2,    3,    1,    4,    6,    7,    5,    2,    3,    8,
   8,    9
};

int
yyparse()
{
	enum {
		StackSize = 100,
		ActSz = sizeof yyact / sizeof yyact[0],
	};
	struct {
		YYSTYPE val;
		int state;
	} stk[StackSize], *ps;
	int r, h, n, s, tk;

	ps = stk;
	ps->state = s = 1; /* to parameterize */
	tk = -1;
loop:
	if (tk <= 0) {
		tk = lex();
		yyval = yylval;
	}
	n = yyadsp[s] + tk;
	if (n < 0 || n >= ActSz || yychk[n] != tk) {
		r = yyadef[s];
		if (r < 0)
			return -1;
		goto reduce;
	}
	n = yyact[n];
	if (n == -1)
		return -1;
	if (n < 0) {
		r = - (n+2);
		goto reduce;
	}
	tk = -1;
stack:
	ps++;
	if (ps-stk >= StackSize)
		return -2;
	s = n;
	ps->state = s;
	ps->val = yyval;
	goto loop;
reduce:
	ps -= yyr1[r];
	h = yyr2[r];
	s = ps->state;
	n = yygdsp[h] + s;
	if (n < 0 || n >= ActSz || yychk[n] != yyntoks+h)
		n = yygdef[h];
	else
		n = yyact[n];
	switch (r) {
	case 0: /* A -> M */
		yyval = ps[1].val;
		break;
	case 1: /* A -> A + M */
		yyval = ps[1].val + ps[3].val;
		break;
	case 2: /* A -> A - M */
		yyval = ps[1].val - ps[3].val;
		break;
	case 3: /* M -> B */
		yyval = ps[1].val;
		break;
	case 4: /* M -> M * B */
		yyval = ps[1].val * ps[3].val;
		break;
	case 5: /* B -> Num */
		yyval = ps[1].val;
		break;
	case 6: /* B -> ( A ) */
		yyval = ps[2].val;
		break;
	case 7: /* S -> A */
		yyval = ps[1].val;
		return 0;
	}
	goto stack;
}

#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum {
	MaxLine = 1000,
};

char line[MaxLine], *p;

int
lex()
{
	char c;

	p += strspn(p, "\t ");
	switch ((c=*p++)) {
	case '+': return 2;
	case '-': return 3;
	case '*': return 4;
	case '(': return 5;
	case ')': return 6;
	case 0:
	case '\n':
		p--;
		return 0;
	}
	if (isdigit(c)) {
		yylval = strtol(p-1, &p, 0);
		return 1;
	}
	puts("lex error!");
	return 0;
}

int
main()
{
	while ((p=fgets(line, MaxLine, stdin))) {
		if (yyparse() < 0)
			puts("parse error!");
		else
			printf("-> %d\n", yyval);
	}
	return 0;
}
