#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <setjmp.h>
#include "etree.h"
#include "proof.h"
#include "dpll.h"
#include "equal.h"
#include "gamma.h"
#include "pred.h"
#include "func.h"

void cnf_proof(int seq, struct lit_set *lit);
void equal_proof(int seq, struct lit_set *lit);
void equal_uif_proof(int seq, struct lit_set *lit);
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

static struct etree *simp_dist1(struct etree *t1, struct etree *t2)
{
	struct etree *t;
	if(t1->type == T_AND)
	{
		t = etree_mknode(T_AND,
				 0,
				 simp_dist1(t1->l, t2),
				 simp_dist1(t1->r, t2));
	}
	else if(t2->type == T_AND)
	{
		t = etree_mknode(T_AND,
				 0,
				 simp_dist1(t1, t2->l),
				 simp_dist1(t1, t2->r));
	}
	else
	{
		t = etree_mknode(T_OR,
				 0,
				 t1,
				 t2);
	}
	return t;
}

static struct etree *simp_dist(struct etree *p)
{
	struct etree *t1, *t2, *t;
	switch(p->type)
	{
	case T_AND:
		return etree_mknode(T_AND, 0, simp_dist(p->l), simp_dist(p->r));
	case T_OR:
		t1 = simp_dist(p->l);
		t2 = simp_dist(p->r);
		t = simp_dist1(t1, t2);
		return t;
	case T_PROP:
		return etree_mknode(T_PROP, p->val, NULL, NULL);
	}
	return NULL;
}

static void __cons_clause(struct etree *p,
			  unsigned long long *pcp,
			  unsigned long long *pcn)
{
	switch(p->type)
	{
	case T_PROP:
		if(p->val > 0)
			*pcp |= 1ull << (p->val-1);
		else
			*pcn |= 1ull << (-p->val-1);
		break;
	case T_OR:
		__cons_clause(p->l, pcp, pcn);
		__cons_clause(p->r, pcp, pcn);
		break;
	}
}

static void cons_clause(struct etree *et, struct etree *p)
{
	unsigned long long cp, cn;
	int id;
	switch(p->type)
	{
	case T_AND:
		cons_clause(et, p->l);
		cons_clause(et, p->r);
		break;
	default:
		cp = 0ull;
		cn = 0ull;
		__cons_clause(p, &cp, &cn);
		id = gamma_add(cp, cn);
		gamma_add_proof(id, cnf_proof, et);
		break;
	}
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

void proof_dpll_proof(struct dpll_tree *tr);

int prove_dpll(struct etree *et)
{
	struct lit_set assign;
	struct lit_set lit;
	struct dpll_tree *tr;
	unsigned long long cp, cn, mask;
	int i;
	struct etree *t;
	struct func f1, f2;
	struct func_info fi1, fi2;
	int j, k;
	int id;
	int n;

	t = simp_dist(et);
	etree_dump_prefix(t, stderr);
	fprintf(stderr, "\n");

	gamma_init();
	cons_clause(et, t);

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
			cp = 0;
			cn = 0;
			for(k = 0; k < fi1.n; k++)
			{
				if(f1.arr[k] != f2.arr[k])
					cn |= 1ull << pred_new(P_EQU, f1.arr[k], f2.arr[k]);
			}
			cp = 1ull << pred_new(P_EQU, i, j);
			id = gamma_add(cp, cn);
			gamma_add_proof(id, equal_uif_proof, NULL);
		}
	}
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
	/*assign.cp = cp & (cp ^ cn);
	assign.cn = cn & (cp ^ cn);
	for(i = 0; i < num_clauses; i++)
	{
		cp &= ~assign.cp;
		cn &= ~assign.cn;
		}*/
	assign.cp = 0;
	assign.cn = 0;

	fprintf(stderr, "num:%d\n", n);
	fprintf(stderr, "initial assign %016llx %016llx mask %016llx\n", assign.cp, assign.cn, mask);

	/* 搜索并证明 */
	pool_init();
	if(!setjmp(env))
	{
		tr = __prove_dpll(0, &assign, mask);
		proof_dpll_proof(tr);
	}
	else
	{
		pool_free();
		fprintf(stderr, "no!\n");
		return 0;
	}
	pool_free();
	return gamma_get_num()+1;
}
