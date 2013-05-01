#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "comm.h"
#include "arith.h"
#include "equal.h"

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
	int varmap[64];
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
	memset(ctx->varmap, -1, sizeof(int)*64);
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
*simplex_dup_ctx(struct simplex_ctx *ctx, int flag)
{
	int i;
	struct simplex_ctx *ctx2;
	if(flag)
		ctx2 = simplex_new_ctx(ctx->n, ctx->m+1);
	else
		ctx2 = simplex_new_ctx(ctx->n, ctx->m);
	for(i = 0; i < ctx->m; i++)
		memcpy(ctx2->t[i], ctx->t[i], sizeof(Q)*ctx->n);
	memcpy(ctx2->nl, ctx->nl, sizeof(xint)*ctx->n);
	memcpy(ctx2->bl, ctx->bl, sizeof(xint)*ctx->m);
	memcpy(ctx2->av, ctx->av, sizeof(Q)*ctx->n);
	memcpy(ctx2->bv, ctx->bv, sizeof(Q)*ctx->m);
	memcpy(ctx2->varmap, ctx->varmap, sizeof(int)*64);
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
	//return;
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

static void pivot(struct simplex_ctx *ctx, int i, int j)
{
	int k, l;
	xint temp;
	Q rev;
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

int simplex_solve(struct simplex_ctx *ctx)
{
	int i, j;
	Q sum, theta, diff;
	xint temp;
	for(i = 0; i < ctx->n; i++)
		ctx->av[i] = Qint(0);
	for(;;)
	{
		/* check relax variable */
		for(i = 0; i < ctx->m; i++)
		{
			if(XINT_O(ctx->bl[i]))
				continue;
			sum = get_basic(ctx, i);
			diff = Qsub(sum, ctx->bv[XINT(ctx->bl[i])]);
			if(Qsign(diff) > 0)
				break;
		}
		if(i == ctx->m)
		{
			pretty_print(ctx);
			return 1; /* sat */
		}
		/* find suitable non-basic variable */
		for(j = 0; j < ctx->n; j++)
		{
			if(Qsign(ctx->t[i][j]) == 0)
			  continue;
			if(XINT_O(ctx->nl[j]))
			{
				ctx->av[j] = Qsub(sum, diff);
				break;
			}
			temp = XINT(ctx->nl[j]);
			if(Qsign(ctx->t[i][j]) > 0)
			{
				ctx->av[j] = Qsub(sum, diff);
				break;
			}
			theta = Qsub(ctx->bv[temp], ctx->av[j]);
			if(Qsign(Qadd(Qmul(ctx->t[i][j], theta), diff)) <= 0)
			{
				ctx->av[j] = Qsub(sum, diff);
				break;
			}
		}
		if(j == ctx->n)
		{
			pretty_print(ctx);
			return 0; /* unsat */
		}
		/* pivot */
		pivot(ctx, i, j);
	}
}

static void __count_n(int i, int *varmap, int *n, int flag)
{
	int j;
	struct func f;
	struct func_info fi;
	func_get(&f, &fi, i);
	if(strcmp(fi.name,"+") == 0) {
		if(flag && varmap[i] == -1) {
			varmap[i] = *n;
			(*n)++;
		}
		__count_n(f.arr[0], varmap, n, 0);
		__count_n(f.arr[1], varmap, n, 0);
	} else 	if(strcmp(fi.name, ".") == 0) {
		if(flag && varmap[i] == -1) {
			varmap[i] = *n;
			(*n)++;
		}
		__count_n(f.arr[1], varmap, n, 0);
	} else if(fi.name[0] != '@') {
		if(varmap[i] == -1) {
			varmap[i] = *n;
			(*n)++;
		}
		for(j = 0; j < fi.n; j++)
			__count_n(f.arr[j], varmap, n, 1);
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
			__count_n(p.lv, varmap, &n, 0);
			__count_n(p.rv, varmap, &n, 0);
		}
	}
	return n;
}

static int count_m_purify(int fid, int flag)
{
	int i;
	struct func f;
	struct func_info fi;
	int count;
	count = 0;
	func_get(&f, &fi, fid);
	if(strcmp(fi.name,"+") == 0 || strcmp(fi.name, ".") == 0)
	{
		if(flag)
		{
			count += 2;
			flag = 0;
		}
	}
	else
		flag = 1;
	for(i = 0; i < fi.n; i++)
		count += count_m_purify(f.arr[i], flag);
	return count;
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
			break;
		case P_LE:
			count++;
			break;
		}
		if(p.type != P_ATOM)
		{
			count += count_m_purify(p.lv, ls->mem[i].neg);
			count += count_m_purify(p.rv, ls->mem[i].neg);
		}
	}
	return count;
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
		c[64] += add*val;
	} else {
		c[varmap[i]] += add;
	}
}

static void __cons_ctx(struct simplex_ctx *ctx, int c[64+1], int type, int neg, int *m)
{
	int j;
	if(neg == 0)	{
		if(type == P_LE) {
			for(j = 0; j < ctx->n; j++)
			{
				int id = XINT(ctx->nl[j]);
				ctx->t[*m][j] = Qint(c[id]);
			}
			ctx->bv[*m] = Qint(-c[64]);
			(*m)++;
		}
		if(type == P_EQU) {
			for(j = 0; j < ctx->n; j++)
			{
				int id = XINT(ctx->nl[j]);
				ctx->t[*m][j] = Qint(c[id]);
			}
			ctx->bv[*m] = Qint(-c[64]);
			(*m)++;
			for(j = 0; j < ctx->n; j++)
			{
				int id = XINT(ctx->nl[j]);
				ctx->t[*m][j] = Qint(-c[id]);
			}
			ctx->bv[*m] = Qint(c[64]);
			(*m)++;
		}
	} else {
		if(type == P_LE)
		{
			for(j = 0; j < ctx->n; j++)
			{
				int id = XINT(ctx->nl[j]);
				ctx->t[*m][j] = Qint(-c[id]);
			}
			ctx->bv[*m] = Qint(c[64]-1);
			(*m)++;
		}
	}
}

static void cons_ctx_purify(struct simplex_ctx *ctx, int fid, int neg, int *m, int flag)
{
	int i;
	struct func f;
	struct func_info fi;
	int c[64+1];
	func_get(&f, &fi, fid);
	if(strcmp(fi.name,"+") == 0 || strcmp(fi.name, ".") == 0)
	{
		if(flag)
		{
			memset(c, 0, sizeof(c));
			cons_single(fid, ctx->varmap, c, 1);
			c[ctx->varmap[fid]] -= 1;
			__cons_ctx(ctx, c, P_EQU, 0, m);
			flag = 0;
		}
	}
	else 
		flag = 1;
	for(i = 0; i < fi.n; i++)
		cons_ctx_purify(ctx, f.arr[i], neg, m, flag);
}

static void cons_ctx(
	struct simplex_ctx *ctx,
	LitSet *ls)
{

	int i;
	int m;
	int c[64+1];
	struct pred p;
	m = 0;
	for(i = 0; i < ls->n; i++)
	{
		pred_get(&p, ls->mem[i].id);
		if(p.type == P_EQU || p.type == P_LE)
		{
			memset(c, 0, sizeof(c));
			cons_single(p.lv, ctx->varmap, c, 1);
			cons_single(p.rv, ctx->varmap, c, -1);
			__cons_ctx(ctx, c, p.type, ls->mem[i].neg, &m);
			cons_ctx_purify(ctx, p.lv, ls->mem[i].neg, &m, ls->mem[i].neg);
			cons_ctx_purify(ctx, p.rv, ls->mem[i].neg, &m, ls->mem[i].neg);
		}
	}
}

static int push_eqs(struct theory_tree *tt)
{
	int i, j;
	int ub[tt->actx->n], lb[tt->actx->n];
	struct simplex_ctx *ctx = tt->actx;
	struct equal_ctx *ectx = tt->ectx;
	struct equal_ctx *ectx1;
	struct simplex_ctx *ctx1;
	for(j = 0; j < ctx->n; j++)
		ub[j] = 0;
	for(j = 0; j < ctx->n; j++)
		lb[j] = 0;
	for(;;)
	{
		/* check relax variable */
		for(i = 0; i < ctx->m; i++)
		{
			if(XINT_R(ctx->bl[i]))
				continue;
			break;
		}
		if(i == ctx->m)
			break;
		/* find suitable non-basic variable */
		for(j = 0; j < ctx->n; j++)
		{
			if(Qsign(ctx->t[i][j]) == 0)
			  continue;
			if(XINT_O(ctx->nl[j]))
				continue;
			break;
		}
		if(j == ctx->n)
			break;
		/* pivot */
		ctx->av[j] = get_basic(ctx, i);
		pivot(ctx, i, j);
	}
	pretty_print(ctx);
	for(i = 0; i < ctx->m; i++)
	{
		for(j = 0; j < ctx->n; j++)
		{
			int sign = Qsign(ctx->t[i][j]);
			if(sign > 0)
				ub[j] = 1;
			else if(sign < 0)
				lb[j] = 1;
		}
	}
	for(j = 0; j < ctx->n; j++)
	{
		if(ub[j] && lb[j])
		{
			char num[16];
			int idx, idy;
			int k;
			int avj;

			fprintf(stderr, "x%d is bound\n", XINT(ctx->nl[j]));
			avj = ctx->av[j].p;
			if(ctx->av[j].q == 1)
			{
				fprintf(stderr, "I assert x%d=", XINT(ctx->nl[j]));
				Qprint(ctx->av[j]);
				fprintf(stderr, "\n");
			}
			else
			{
				fprintf(stderr, "x%d is not integer:", XINT(ctx->nl[j]));
				Qprint(ctx->av[j]);
				fprintf(stderr, "\n");
				avj /= ctx->av[j].q;
			}

			/* case 1: xi=bi */
			fprintf(stderr, "===xi=bi===\n");
			ctx1 = simplex_dup_ctx(ctx, 0);
			ectx1 = equal_dup_ctx(ectx);
			for(idx = 0; idx < 64; idx++)
				if(ctx->varmap[idx] == XINT(ctx->nl[j]))
					break;
			assert(idx < 64);
			sprintf(num, "@%d", avj);
			idy = func_new(func_info_new(num, 0), -1, -1);
			if(equal_add_eq(ectx1, idx, idy) == 0)
			{
				equal_del_ctx(ectx1);
				fprintf(stderr, "xi=bi sat\n");
				continue;
			}
			tt->eq = theory_tree_new(ctx1, ectx1);
			if(equal_test(tt->eq) == 0)
			{
				fprintf(stderr, "xi=bi sat\n");
				continue;
			}
			/* case2: xi<=bi-1 */
			fprintf(stderr, "===xi<bi===\n");
			ctx1 = simplex_dup_ctx(ctx, 1);
			ectx1 = equal_dup_ctx(ectx);
			tt->lt = theory_tree_new(ctx1, ectx1);
			for(k = 0; k < ctx1->n; k++)
				ctx1->t[ctx->m][k] = Qint(0);
			ctx1->t[ctx->m][j] = Qint(1);
			ctx1->bl[ctx->m] = XINT_SR(ctx->m);
			ctx1->bv[ctx->m] = Qint(avj - 1);
			if(arith_test(tt->lt) == 0)
			{
				fprintf(stderr, "xi<bi sat\n");
				continue;
			}
			/* case3: -xi <= -bi-1 */
			fprintf(stderr, "===xi>bi===\n");
			ctx1 = simplex_dup_ctx(ctx, 1);
			ectx1 = equal_dup_ctx(ectx);
			tt->gt = theory_tree_new(ctx1, ectx1);
			for(k = 0; k < ctx1->n; k++)
				ctx1->t[ctx->m][k] = Qint(0);
			ctx1->t[ctx->m][j] = Qint(-1);
			ctx1->bl[ctx->m] = XINT_SR(ctx->m);
			ctx1->bv[ctx->m] = Qint(-(avj + 1));
			if(arith_test(tt->gt) == 0)
			{
				fprintf(stderr, "xi>bi sat\n");
				continue;
			}
			fprintf(stderr, "bound check ok\n");
			return 1;
		}
	}
	fprintf(stderr, "bound check fail\n");
	return 0;
}

static void pull_eqs(struct theory_tree *tt)
{
	/* eq rewrite */
	int i, k;
	int v;
	struct func f;
	struct func_info fi;
	struct simplex_ctx *ctx = tt->actx;
	struct equal_ctx *ectx = tt->ectx;
	for(k = 0; k < 64; k++)
	{
		if(ctx->varmap[k] != -1)
		{
			v = equal_get_father(ectx, k);
			if(k != v)
			{
				int idk;
				for(idk = 0; idk < 64; idk++)
					if(XINT(ctx->nl[idk]) == ctx->varmap[k])
						break;
				assert(idk < 64);
				if(ctx->varmap[v] != -1)
				{
					int idv;
					for(idv = 0; idv < 64; idv++)
						if(XINT(ctx->nl[idv]) == ctx->varmap[v])
							break;
					assert(idv < 64);
					fprintf(stderr, "rewrite x%d/",ctx->varmap[k]);
					func_print_pure(k, stderr);
					fprintf(stderr, " using x%d/", ctx->varmap[v]);
					func_print_pure(v, stderr);
					fprintf(stderr, "\n");
					for(i = 0; i < ctx->m; i++)
					{
						ctx->t[i][idv] =
							Qadd(ctx->t[i][idv], ctx->t[i][idk]);
						ctx->t[i][idk] = Qint(0);
					}
				}
				else
				{
					fprintf(stderr, "replace x%d/",ctx->varmap[k]);
					func_print_pure(k, stderr);
					fprintf(stderr, " using ");
					func_print_pure(v, stderr);
					fprintf(stderr, "\n");
					func_get(&f, &fi, v);
					if(fi.name[0] != '@')
					{
						ctx->varmap[v] = ctx->varmap[k];
						ctx->varmap[k] = -1;
					}
					else
					{
						int c = atoi(fi.name+1);
						for(i = 0; i < ctx->m; i++)
						{
							int mid = XINT(ctx->bl[i]);
							ctx->bv[mid] = Qsub(ctx->bv[mid],
									    Qmul(ctx->t[i][idk], Qint(c)));
							ctx->t[i][idk] = Qint(0);
						}
					}
				}
			}
		}
	}
}

struct simplex_ctx *arith_build_env(LitSet *env)
{
	int i;
	int m, n;
	struct simplex_ctx *ctx;
	int varmap[64];
	memset(varmap, -1, sizeof(varmap));
	m = count_m(env);
	n = count_n(varmap, env);
	for(i = 0; i < 64; i++)
		if(varmap[i] != -1) {
			fprintf(stderr, "x%d=", varmap[i]);
			func_print_pure(i, stderr);
			fprintf(stderr, "\n");
		}
	ctx = simplex_new_ctx(n, m);
	memcpy(ctx->varmap, varmap, sizeof(varmap));
	cons_ctx(ctx, env);
	return ctx;
}

int arith_test(struct theory_tree *tt)
{
	if(tt->actx->m == 0)
		return 0;
	pull_eqs(tt);
	if(simplex_solve(tt->actx) == 0)
	{
		fprintf(stderr, "unsat\n");
		return 1;
	}
	fprintf(stderr, "sat\ncheck bound\n");
	return push_eqs(tt);
}
