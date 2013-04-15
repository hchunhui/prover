#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "comm.h"

struct qnum
{
	int p;
	int q;
};
typedef struct qnum Q;

static int gcd(int a, int b)
{
	if(a == 0 || b == 0)
		return 1;
	if(a%b == 0) return b;
	return gcd(b, a%b);
}

static void Qreduce(Q *q)
{
	int sgn, x;
	if(q->p == 0)
	{
		q->q = 1;
		return;
	}
	sgn = (q->p<0?-1:1)*(q->q<0?-1:1);
	q->p = abs(q->p);
	q->q = abs(q->q);
	x = gcd(q->p, q->q);
	q->p /= x;
	q->q /= x;
	q->p *= sgn;
}

static Q Qint(int x)
{
	Q q;
	q.p = x;
	q.q = 1;
	return q;
}

static Q Qadd(Q a, Q b)
{
	Q t;
	t.p = b.q*a.p+b.p*a.q;
	t.q = b.q*a.q;
	Qreduce(&t);
	return t;
}

static Q Qmul(Q a, Q b)
{
	Q t;
	t.p = a.p*b.p;
	t.q = a.q*b.q;
	Qreduce(&t);
	return t;
}

static Q Qrev(Q a)
{
	Q t;
	if(a.p == 0)
		exit(-1);
	if(a.p < 0)
	{
		t.p = -a.q;
		t.q = -a.p;
	}
	else
	{
		t.p = a.q;
		t.q = a.p;
	}
	return t;
}

static Q Qsub(Q a, Q b)
{
	Q t;
	t.p = b.q*a.p-b.p*a.q;
	t.q = b.q*a.q;
	Qreduce(&t);
	return t;
}

static Q Qneg(Q a)
{
	a.p = -a.p;
	return a;
}

static int Qsign(Q a)
{
	if(a.p > 0)
		return 1;
	else if(a.p < 0)
		return -1;
	return 0;
}

static void Qprint(Q a)
{
	fprintf(stderr, "%2d/%d ", a.p, a.q);
}

typedef unsigned int xint;
#define XINT_R(x) (!!(x&(1<<31)))
#define XINT_O(x) (!(x&(1<<31)))
#define XINT(x)   (x&(~(1<<31)))
#define XINT_SR(x) (x|(1<<31))
#define XINT_SO(x) (x)

struct simplex_ctx
{
	int n;		/* 原变量数 */
	int m;		/* 松弛变量数 */
	Q   **t;	/* 作业表 m*n */
	xint *nl;	/* 非基变量列表 n */
	xint *bl;	/* 基变量列表 m */
	Q   *av;	/* 非基变量赋值 n */
	Q   *bv;	/* 松弛变量界 m */
};

struct simplex_ctx
*simplex_new_ctx(int n, int m)
{
	int i;
	struct simplex_ctx *ctx;
	ctx = malloc(sizeof(struct simplex_ctx));
	ctx->n = n;
	ctx->m = m;
	ctx->t = malloc(sizeof(Q *)*m);
	ctx->nl = malloc(sizeof(xint)*n);
	ctx->bl = malloc(sizeof(xint)*m);
	ctx->av = malloc(sizeof(Q)*n);
	ctx->bv = malloc(sizeof(Q)*m);
	for(i = 0; i < m; i++)
		ctx->t[i] = malloc(sizeof(Q)*n);
	for(i = 0; i < m; i++)
		ctx->bl[i] = XINT_SR(i);
	for(i = 0; i < n; i++)
		ctx->nl[i] = XINT_SO(i);
	return ctx;
}

void
simplex_del_ctx(struct simplex_ctx *ctx)
{
	int i;
	for(i = 0; i < ctx->m; i++)
		free(ctx->t[i]);
	free(ctx->t);
	free(ctx->nl);
	free(ctx->bl);
	free(ctx->av);
	free(ctx->bv);
	free(ctx);
}

struct simplex_ctx
*simplex_dup_ctx(struct simplex_ctx *ctx)
{
	int i;
	struct simplex_ctx *ctx2;
	ctx2 = simplex_new_ctx(ctx->n, ctx->m);
	for(i = 0; i < ctx->m; i++)
		memcpy(ctx2->t[i], ctx->t[i], sizeof(Q)*ctx->n);
	memcpy(ctx2->nl, ctx->nl, sizeof(xint)*ctx->n);
	memcpy(ctx2->bl, ctx->bl, sizeof(xint)*ctx->m);
	memcpy(ctx2->av, ctx->av, sizeof(Q)*ctx->n);
	memcpy(ctx2->bv, ctx->bv, sizeof(Q)*ctx->m);
	return ctx2;
}

static Q get_basic(struct simplex_ctx *ctx, int i)
{
	Q sum;
	int j;
	sum = Qint(0);
	for(j = 0; j < ctx->n; j++)
		sum = Qadd(sum, Qmul(ctx->t[i][j], ctx->av[j]));
	return sum;
}

static void pretty_print(struct simplex_ctx *ctx)
{
	int i, j;
	fprintf(stderr, "     ");
	for(j = 0; j < ctx->n; j++)
		Qprint(ctx->av[j]);
	fprintf(stderr, "\n     ");
	for(j = 0; j < ctx->n; j++)
		fprintf(stderr, " %s%d  ", XINT_O(ctx->nl[j])?"x":"s", XINT(ctx->nl[j]));
	fprintf(stderr, "\n");
	for(i = 0; i < ctx->m; i++)
	{
		fprintf(stderr, " %s%d  ", XINT_O(ctx->bl[i])?"x":"s", XINT(ctx->bl[i]));
		for(j = 0; j < ctx->n; j++)
			Qprint(ctx->t[i][j]);
		Qprint(get_basic(ctx, i));
		fprintf(stderr, "\n");
	}
	fprintf(stderr, "\nbv: ");
	for(i = 0; i < ctx->m; i++)
	{
		fprintf(stderr, " s%d:  ", i);
		Qprint(ctx->bv[i]);
	}
	fprintf(stderr, "\n");
}

int simplex_solve(struct simplex_ctx *ctx)
{
	int i, j, k, l;
	Q sum, theta, diff, rev;
	xint temp;
	for(i = 0; i < ctx->n; i++)
		ctx->av[i] = Qint(0);
	for(;;)
	{
		pretty_print(ctx);
		/* check relax variable */
		for(i = 0; i < ctx->m; i++)
		{
			if(XINT_O(ctx->bl[i]))
				continue;
			sum = get_basic(ctx, i);
			diff = Qsub(sum, ctx->bv[i]);
			if(Qsign(diff) > 0)
				break;
		}
		if(i == ctx->m)
			return 1; /* sat */
		/* find suitable non-basic variable */
		for(j = 0; j < ctx->n; j++)
		{
			if(Qsign(ctx->t[i][j]) == 0)
			  continue;
			if(XINT_O(ctx->nl[j]))
			{
				ctx->av[j] = Qsub(get_basic(ctx, i), diff);
				break;
			}
			temp = XINT(ctx->nl[j]);
			theta = Qsub(ctx->bv[temp], ctx->av[j]);
			if(Qsign(Qsub(Qmul(ctx->t[i][j], theta), diff)) >= 0)
			{
				ctx->av[j] = Qsub(ctx->av[j], diff);
				break;
			}
		}
		if(j == ctx->n)
			return 0; /* unsat */
		/* pivot */
		temp = ctx->bl[i];
		ctx->bl[i] = ctx->nl[j];
		ctx->nl[j] = temp;
		rev = Qrev(ctx->t[i][j]);
		ctx->t[i][j] = rev;
		for(l = 0; l < ctx->n; l++)
			if(l != j)
				ctx->t[i][l] = Qneg(Qmul(ctx->t[i][l], rev));
		for(k = 0; k < ctx->m; k++)
			if(k != i)
				for(l = 0; l < ctx->n; l++)
					if(l != j)
						ctx->t[k][l] = Qadd(ctx->t[k][l],
								    Qmul(ctx->t[k][j], ctx->t[i][l]));
		for(k = 0; k < ctx->m; k++)
			if(k != i)
				ctx->t[k][j] = Qmul(ctx->t[k][j], rev);
	}
}

static void printh(struct simplex_ctx *ctx)
{
	int i, j;
	for(i = 0; i < ctx->m; i++)
	{
		printf("Hypothesis H%d:", i);
		printf("%s%d=", XINT_O(ctx->bl[i])?"x":"s", XINT(ctx->bl[i]));
		printf("(%d)*%s%d", ctx->t[i][0].p, XINT_O(ctx->nl[0])?"x":"s", XINT(ctx->nl[0]));
		for(j = 1; j < ctx->n; j++)
			printf("+(%d)*%s%d", ctx->t[i][j].p, XINT_O(ctx->nl[j])?"x":"s", XINT(ctx->nl[j]));
		printf(".\n");
	}
}

static void printb(struct simplex_ctx *ctx)
{
	int i;
	for(i = 0; i < ctx->m; i++)
	{
		printf("Hypothesis B%d:", i);
		printf("s%d <= %d.\n", i, ctx->bv[i].p);
	}
}

void simplex_proof(struct simplex_ctx *ctx)
{
	int i;
	printf("Section simplex.\n");
	printf("Variable");
	for(i = 0; i < ctx->n; i++)
		printf(" x%d", i);
	for(i = 0; i < ctx->m; i++)
		printf(" s%d", i);
	printf(":Z.\n");
	printh(ctx);
	printb(ctx);
//	proof(ctx);
	printf("End simplex.\nCheck L.\n");
}

static int count_m(LitSet *ls)
{
	int i;
	int count;
	struct pred p;
	count = 0;
	for(i = 0; i < ls->n; i++)
	{
		pred_get(&p, ls->mem[i].id);
		switch(p.type)
		{
		case P_EQU:
			if(ls->mem[i].neg == 0)
				count += 2;
			else
				count++;
			break;
		case P_LE:
			count++;
			break;
		}
	}
	return count;
}

static void __count_n(int i, int *varmap, int *n)
{
	struct func f;
	struct func_info fi;
	func_get(&f, &fi, i);
	if(strcmp(fi.name,"+") == 0) {
		__count_n(f.arr[0], varmap, n);
		__count_n(f.arr[1], varmap, n);
	} else 	if(strcmp(fi.name, ".") == 0) {
		__count_n(f.arr[1], varmap, n);
	} else if(fi.name[0] != '@') {
		if(varmap[i] == -1) {
			varmap[i] = *n;
			(*n)++;
		}
	}
}

static int count_n(int *varmap, LitSet *ls)
{
	int i, n;
	struct pred p;
	n = 0;
	for(i = 0; i < ls->n; i++)
	{
		pred_get(&p, ls->mem[i].id);
		if(p.type == P_EQU || p.type == P_LE)
		{
			__count_n(p.lv, varmap, &n);
			__count_n(p.rv, varmap, &n);
		}
	}
	return n;
}

static void cons_single(int i, int *varmap, int *c, int add)
{
	struct func f, f1;
	struct func_info fi, fi1;
	int val;
	func_get(&f, &fi, i);
	if(strcmp(fi.name,"+") == 0) {
		cons_single(f.arr[0], varmap, c, add);
		cons_single(f.arr[1], varmap, c, add);
	} else 	if(strcmp(fi.name, ".") == 0) {
		func_get(&f1, &fi1, f.arr[0]);
		val = atoi(fi1.name+1);
		c[varmap[f.arr[1]]] += add*val;
	} else if(fi.name[0] == '@') {
		val = atoi(fi.name+1);
		c[63] += add*val;
	} else {
		val = atoi(fi1.name+1);
		c[varmap[i]] += add;
	}
}

static void cons_ctx(
	struct simplex_ctx *ctx,
	int *varmap,
	int *fix,
	LitSet *ls)
{
	int i, m;
	int j;
	int c[64];
	struct pred p;
	m = 0;
	for(i = 0; i < ls->n; i++)
	{
		pred_get(&p, ls->mem[i].id);
		if(p.type == P_EQU || p.type == P_LE)
		{
			memset(c, 0, sizeof(c));
			cons_single(p.lv, varmap, c, 1);
			cons_single(p.rv, varmap, c, -1);
			if(ls->mem[i].neg == 0)	{
				if(p.type == P_LE) {
					for(j = 0; j < ctx->n; j++)
						ctx->t[m][j] = Qint(c[j]);
					ctx->bv[m] = Qint(-c[63]);
					fix[m] = 0;
					m++;
				}
				if(p.type == P_EQU) {
					for(j = 0; j < ctx->n; j++)
						ctx->t[m][j] = Qint(c[j]);
					ctx->bv[m] = Qint(-c[63]);
					fix[m] = 0;
					m++;
					for(j = 0; j < ctx->n; j++)
						ctx->t[m][j] = Qint(-c[j]);
					ctx->bv[m] = Qint(c[63]);
					fix[m] = 0;
					m++;
				}
			} else {
				if(p.type == P_EQU || p.type == P_LE)
				{
					memset(c, 0, sizeof(c));
					cons_single(p.lv, varmap, c, 1);
					cons_single(p.rv, varmap, c, -1);
					if(p.type == P_LE) {
						for(j = 0; j < ctx->n; j++)
							ctx->t[m][j] = Qint(-c[j]);
						ctx->bv[m] = Qint(c[63]-1);
						fix[m] = 0;
						m++;
					}
					if(p.type == P_EQU) {
						for(j = 0; j < ctx->n; j++)
							ctx->t[m][j] = Qint(c[j]);
						ctx->bv[m] = Qint(-c[63]);
						fix[m] = 1;
						m++;
					}
				}
			}
		}
	}
}

int do_fix_solve(struct simplex_ctx *ctx, int *fix, int i)
{
	int ret;
	int j;
	struct simplex_ctx *ctx2;
	if(i == ctx->m)
		return simplex_solve(ctx);
	if(fix[i])
	{
		fprintf(stderr, "-----branch in %d-----\n", i);
		fprintf(stderr, "-----case1 <= -----\n");
		ctx2 = simplex_dup_ctx(ctx);
		/* case1: a.x != b  ==> a.x <= b-1*/
		ctx->bv[i] = Qsub(ctx->bv[i], Qint(1));
		if(ret = do_fix_solve(ctx, fix, i+1))
			goto clean;
		fprintf(stderr, "-----case1 unsat-----\n");
		fprintf(stderr, "-----case2 >= -----\n");
		/* case2: a.x != b ==> a.x >= b+1 ==> -a.x <= -b-1 */
		for(j = 0; j < ctx->n; j++)
			ctx2->t[i][j] = Qneg(ctx2->t[i][j]);

		ctx2->bv[i] = Qsub(Qneg(ctx2->bv[i]), Qint(1));
		if(ret = do_fix_solve(ctx2, fix, i+1))
			goto clean;
		ret = 0;
		fprintf(stderr, "-----case2 unsat-----\n");
	clean:
		simplex_del_ctx(ctx2);
		return ret;
	}
	return do_fix_solve(ctx, fix, i+1);
}

int arith_test(LitSet *ls)
{
	int i;
	int m, n;
	int id;
	int varmap[64];
	LitSet *ls1;
	struct simplex_ctx *ctx;
	memset(varmap, -1, sizeof(varmap));
	m = count_m(ls);
	n = count_n(varmap, ls);
	ctx = simplex_new_ctx(n, m);
	int fix[m];
	cons_ctx(ctx, varmap, fix, ls);
	if(do_fix_solve(ctx, fix, 0) == 0)
	{
		fprintf(stderr, "unsat\n");
		ls1 = litset_new();
		for(i = 0; i < ls->n; i++)
			litset_add(ls1, lit_make(!ls->mem[i].neg, ls->mem[i].id));
		id = gamma_add(ls1);
		return 1;
	}
	fprintf(stderr, "sat\n");
	return 0;
}

#if 0
int main(int argc, char *argv[])
{
	struct simplex_ctx *ctx;
	ctx = simplex_new_ctx(2, 3);
	ctx->t[0][0] = Qint(-1);
	ctx->t[0][1] = Qint(0);
	ctx->t[1][0] = Qint(0);
	ctx->t[1][1] = Qint(-1);
	ctx->t[2][0] = Qint(1);
	ctx->t[2][1] = Qint(1);
	ctx->bv[0] = Qint(-1);
	ctx->bv[1] = Qint(-1);
	ctx->bv[2] = Qint(1);
	/* ctx = simplex_new_ctx(2, 3); */
	/* ctx->t[0][0] = Qint(-1); */
	/* ctx->t[0][1] = Qint(-1); */
	/* ctx->t[1][0] = Qint(-2); */
	/* ctx->t[1][1] = Qint(1); */
	/* ctx->t[2][0] = Qint(1); */
	/* ctx->t[2][1] = Qint(-2); */
	/* ctx->bv[0] = Qint(-2); */
	/* ctx->bv[1] = Qint(0); */
	/* ctx->bv[2] = Qint(-1); */
	if(simplex_solve(ctx) == 1)
		fprintf(stderr, "sat\n");
	else
	{
		fprintf(stderr, "unsat\n");
		simplex_proof(ctx);
	}
	return 0;
}
#endif
