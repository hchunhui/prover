#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <setjmp.h>
#include "etree.h"
#include "proof.h"
#include "dpll.h"
#include "equal.h"
#include "gamma.h"

void equal_proof(int seq, struct lit_set *lit, void *extra);

static jmp_buf env;

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

void prove_dpll_proof_free(int seq, struct lit_set *cl, void *extra)
{
	prove_dpll_proof(seq, cl, extra);
	pool_free();
}

static int add_clause(unsigned long long penv, unsigned long long nenv)
{
	unsigned long long eq_env, eq_v;
	int i;
	int id;
	eq_v = nenv;
	for(i = 0; i < 64; i++, eq_v >>= 1) {
		if(eq_v & 1) {
			eq_env = penv;
			if(equal_test(&eq_env, i)) {
				id = gamma_add(1ull<<i, eq_env);
				gamma_add_proof(id, equal_proof, NULL);
				gamma_ref(id);
				return id;
			}
		}
	}
	return 0;
}

static struct dpll_tree
*__prove_dpll(int lev, struct lit_set *prev, unsigned long long mask)
{
	unsigned long long vmask, amask;
	struct lit_set cur, *curr;
	struct dpll_tree *tr;
	curr = &cur;
	*curr = *prev;
	if(!mask) {
		fprintf(stderr, "assign %016llx %016llx %016llx\n", curr->cp, curr->cn,
		       curr->cp | curr->cn);
		longjmp(env, 1);
	}
	vmask = 1ull << lev;
	amask = curr->cp | curr->cn;
	if((mask & 1) && !(amask & vmask)) {
		tr = pool_get(sizeof(struct dpll_tree));
		tr->t = NULL;
		tr->f = NULL;
		tr->lev = lev;

		curr->cp |= vmask;
		if((tr->ti = gamma_match(~curr->cn, ~curr->cp)) != -1)
			gamma_ref(tr->ti);
	        else if(!(tr->ti = add_clause(curr->cp, curr->cn)))
			tr->t = __prove_dpll(lev+1, curr, mask>>1);

		*curr = *prev;
		curr->cn |= vmask;
		if((tr->fi = gamma_match(~curr->cn, ~curr->cp)) != -1)
			gamma_ref(tr->fi);
		else if(!(tr->fi = add_clause(curr->cp, curr->cn)))
			tr->f = __prove_dpll(lev+1, curr, mask>>1);
	} else {
		return __prove_dpll(lev+1, curr, mask>>1);
	}
	return tr;
}

int prove_dpll()
{
	struct lit_set assign;
	struct lit_set lit;
	struct dpll_tree *tr;
	unsigned long long cp, cn, mask;
	int i;
	int id;
	int n;

	/* 消去没有使用的变量 */
	cp = 0;
	cn = 0;
	n = gamma_get_num();
	for(i = 0; i < n; i++)
	{
		gamma_get(i, &lit);
		cp |= lit.cp;
		cn |= lit.cn;
	}
	mask = cp | cn;
	assign.cp = cp & (cp ^ cn);
	assign.cn = cn & (cp ^ cn);
	for(i = 0; i < n; i++)
	{
		cp &= ~assign.cp;
		cn &= ~assign.cn;
	}
	assign.cp = 0;
	assign.cn = 0;

	fprintf(stderr, "num:%d\n", n);
	fprintf(stderr, "initial assign %016llx %016llx mask %016llx\n", assign.cp, assign.cn, mask);

	/* 搜索并证明 */
	pool_init();
	if(!setjmp(env))
	{
		tr = __prove_dpll(0, &assign, mask);
		id = gamma_add(0ull, 0ull);
		gamma_add_proof(id, prove_dpll_proof_free, tr);
		gamma_ref(id);
		return id+1;
	}
	else
	{
		pool_free();
		fprintf(stderr, "no!\n");
		return 0;
	}
}
