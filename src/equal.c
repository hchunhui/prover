#include "comm.h"
#include "equal.h"
#include <stdlib.h>
#include <string.h>

struct equal_ctx
{
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

int
equal_test(struct equal_ctx *ctx, LitSet *env)
{
	int i, id;
	struct pred q;
	LitSet *ls, *ls1;
	int ret;
	ret = 0;
	ls = litset_new();
	for(i = 0; i < env->n; i++)
	{
		if(env->mem[i].neg)
			continue;
		pred_get(&q, env->mem[i].id);
		if(q.type != P_EQU)
			continue;
		equal_add_eq(ctx, q.lv, q.rv);
		litset_add(ls, lit_make(1, env->mem[i].id));
	}

	for(i = 0; i < env->n; i++)
	{
		if(!env->mem[i].neg)
			continue;
		pred_get(&q, env->mem[i].id);
		if(q.type != P_EQU)
			continue;
		do {
			if(equal_query_eq(ctx, q.lv, q.rv))
			{
				ls1 = litset_dup(ls);
				litset_add(ls1, lit_make(0, env->mem[i].id));
				id = gamma_add(ls1);
//				gamma_add_proof(id, equal_proof, NULL);
				ret = 1;
				return ret;
				break;
			}
		} while(equal_closure(ctx));
	}
	litset_del(ls);
	return ret;
}
