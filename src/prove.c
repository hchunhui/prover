#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <setjmp.h>
#include "comm.h"
#include "dpll.h"
#include "equal.h"
#include "arith.h"

static jmp_buf jmp_env;

static char *pool, *poolp;

static void pool_init()
{
	pool = malloc(1024*1024*1024);
	poolp = pool;
}

static void *pool_get(int size)
{
	void *pp;
	size = (size+sizeof(long)-1)/sizeof(long)*sizeof(long);
	if(poolp + size < pool + 1024*1024*1024)
	{
		pp = poolp;
		poolp += size;
		return pp;
	}
	return NULL;
}

static void pool_free()
{
	free(pool);
	poolp = pool = NULL;
}

void prove_dpll_proof_free(int seq, LitSet *cl, void *extra)
{
	prove_dpll_proof(seq, cl, extra);
	pool_free();
}

static int add_clause(LitSet *env)
{
	int ret;
	struct simplex_ctx *sctx;
	struct equal_ctx *ectx;
	sctx = arith_build_env(env);
	ectx = equal_build_env(env);
	ret = equal_test(ectx, sctx);
	if(ret == 0)
		ret = arith_test(sctx, ectx);
	equal_del_ctx(ectx);
	simplex_del_ctx(sctx);
	return ret;
}

static struct dpll_tree
*__prove_dpll(int i, LitSet *pasgn, LitSet *cls)
{
	LitSet *casgn;
	struct dpll_tree *tr;

	if(i == cls->n) {
		fprintf(stderr, "assign found:");
		litset_print(pasgn, 0, "/\\", stderr);
		fprintf(stderr, "\n");
		longjmp(jmp_env, 1);
	}
	tr = pool_get(sizeof(struct dpll_tree));
	tr->t = NULL;
	tr->f = NULL;
	tr->lit = cls->mem[i];

	casgn = litset_dup(pasgn);
	litset_add(casgn, lit_make(0, cls->mem[i].id));
	if((tr->ti = gamma_match(casgn)) == -1)
	{
		if(!add_clause(casgn) ||
		   (tr->ti = gamma_match(casgn)) == -1)
			tr->t = __prove_dpll(i+1, casgn, cls);
	}
	litset_del(casgn);

	casgn = litset_dup(pasgn);
	litset_add(casgn, lit_make(1, cls->mem[i].id));
	if((tr->fi = gamma_match(casgn)) == -1)
	{
		if(!add_clause(casgn) ||
		   (tr->fi = gamma_match(casgn)) == -1)
			tr->f = __prove_dpll(i+1, casgn, cls);
	}
	litset_del(casgn);
	return tr;
}

int prove_dpll()
{
	LitSet *asgn, *cl, *cls;
	struct dpll_tree *tr;
	int id;
	int i, j, n;

	cls = litset_new();
	/* 消去没有使用的变量, 暂时没有了 */
	n = gamma_get_num();
	for(i = 0; i < n; i++)
	{
		cl = gamma_get(i);
		for(j = 0; j < cl->n; j++)
			litset_add(cls, lit_make(0, cl->mem[j].id));
	}
	fprintf(stderr, "num:%d\n", n);

	/* 搜索并证明 */
	pool_init();
	asgn = litset_new();
	if(!setjmp(jmp_env))
	{
		tr = __prove_dpll(0, asgn, cls);
		id = gamma_add(asgn);
		gamma_add_proof(id, prove_dpll_proof_free, tr);
		gamma_ref(id);
		litset_del(asgn);
		litset_del(cls);
		return id+1;
	}
	else
	{
		pool_free();
		fprintf(stderr, "no!\n");
		litset_del(asgn);
		litset_del(cls);
		return 0;
	}
}
