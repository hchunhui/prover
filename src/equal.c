#include "comm.h"
#include "equal.h"
#include <stdlib.h>
#include <string.h>

struct equal_ctx
{
	int dis_n;
	int diseq[64];
	int fa[64];
};

struct equal_ctx
*equal_new_ctx()
{
	int i;
	struct equal_ctx *ctx;
	ctx = malloc(sizeof(struct equal_ctx));
	for(i = 0; i < 64; i++)
		ctx->fa[i] = i;
	ctx->dis_n = 0;
	return ctx;
}

struct equal_ctx
*equal_dup_ctx(struct equal_ctx *ctx0)
{
	struct equal_ctx *ctx;
	ctx = malloc(sizeof(struct equal_ctx));
	memcpy(ctx, ctx0, sizeof(struct equal_ctx));
	return ctx;
}

void 
equal_del_ctx(struct equal_ctx *ctx)
{
	free(ctx);
}

int
equal_get_father(struct equal_ctx *ctx, int v)
{
	if(ctx->fa[v] == v)
		return v;
	else
		return  equal_get_father(ctx, ctx->fa[v]);
}

int
equal_query_eq(struct equal_ctx *ctx, int idx, int idy)
{
	int fx = equal_get_father(ctx, idx);
	int fy = equal_get_father(ctx, idy);
	return fx == fy;
}

int
equal_add_eq(struct equal_ctx *ctx, int idx, int idy)
{
	int fx = equal_get_father(ctx, idx);
	int fy = equal_get_father(ctx, idy);
	if(fy != fx) {
		ctx->fa[fx]=fy;
		return 1;
	}
	return 0;
}

int
equal_closure(struct equal_ctx *ctx)
{
	int i, j, k;
	struct func f1, f2;
	struct func_info fi1, fi2;
	int flag;
	flag = 0;
	for(i = 0; i < 64-1; i++)
	{
		func_get(&f1, &fi1, i);
		if(fi1.n == 0 || f1.type == -1)
			continue;
		for(j = i+1; j < 64; j++)
		{
			func_get(&f2, &fi2, j);
			if(f2.type == -1 || strcmp(fi1.name, fi2.name))
				continue;
			for(k = 0; k < fi1.n; k++)
				if(!equal_query_eq(ctx, f1.arr[k], f2.arr[k]))
					break;
			if(k == fi1.n)
				if(equal_add_eq(ctx, i, j))
					flag = 1;
		}
	}
	return flag;
}

struct equal_ctx
*equal_build_env(LitSet *env)
{
	struct equal_ctx *ctx;
	int i;
	struct pred q;
	ctx = equal_new_ctx();
	for(i = 0; i < env->n; i++)
	{
		pred_get(&q, env->mem[i].id);
		if(q.type != P_EQU)
			continue;
		if(env->mem[i].neg)
			ctx->diseq[ctx->dis_n++] = env->mem[i].id;
		else
			equal_add_eq(ctx, q.lv, q.rv);
	}
	return ctx;
}

int
equal_test(struct equal_ctx *ctx, struct simplex_ctx *sctx)
{
	int i;
	struct pred q;
	for(;equal_closure(ctx);) ;
	for(i = 0; i < ctx->dis_n; i++)
	{
		pred_get(&q, ctx->diseq[i]);
		if(equal_query_eq(ctx, q.lv, q.rv))
			return 1;
	}
	return arith_test(sctx, ctx);
}
