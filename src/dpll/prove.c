#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <setjmp.h>
#include "etree.h"
#include "proof.h"
#include "dpll.h"
#include "equal.h"

#define MAX 256
static struct lit_set clauses[MAX];
static int cl_ref[MAX];
static int num_clauses;
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

static void __cons_clause(struct etree *p)
{
	switch(p->type)
	{
	case T_PROP:
		if(p->val > 0)
			clauses[num_clauses].cp |= 1ull << (p->val-1);
		else
			clauses[num_clauses].cn |= 1ull << (-p->val-1);
		break;
	case T_OR:
		__cons_clause(p->l);
		__cons_clause(p->r);
		break;
	}
}

static void cons_clause(struct etree *p)
{
	switch(p->type)
	{
	case T_AND:
		cons_clause(p->l);
		cons_clause(p->r);
		break;
	default:
		clauses[num_clauses].cp = 0;
		clauses[num_clauses].cn = 0;
		__cons_clause(p);
		num_clauses++;
		break;
	}
}

static int add_clause(unsigned long long penv, unsigned long long nenv)
{
	unsigned long long eq_env, eq_v;
	int i;
	eq_v = nenv;
	for(i = 0; i < 64; i++, eq_v >>= 1) {
		if(eq_v & 1) {
			eq_env = penv;
			if(equal_test(&eq_env, i)) {
				clauses[num_clauses].cp = 1ull << i;
				clauses[num_clauses].cn = eq_env;
				cl_ref[num_clauses] = 2;/*FIXME: hard wire*/
				return num_clauses++;
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
	int i;
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
		for(i = 0; i < num_clauses; i++)
		{
			if((clauses[i].cp & curr->cp) ||
			   (clauses[i].cn & curr->cn))
				continue;
			if((clauses[i].cp & (~curr->cn)) == 0ull &&
			   (clauses[i].cn & (~curr->cp)) == 0ull) {
				tr->ti = i;
				cl_ref[i] = 1;
				goto choose_next1;
			}
		}
		if(tr->ti = add_clause(curr->cp, curr->cn))
			goto choose_next1;
		tr->t = __prove_dpll(lev+1, curr, mask>>1);
	choose_next1:
		*curr = *prev;
		curr->cn |= vmask;
		for(i = 0; i < num_clauses; i++)
		{
			if((clauses[i].cp & curr->cp) ||
			   (clauses[i].cn & curr->cn))
				continue;
			if((clauses[i].cp & (~curr->cn)) == 0ull &&
			   (clauses[i].cn & (~curr->cp)) == 0ull) {
				tr->fi = i;
				cl_ref[i] = 1;
				goto choose_next2;
			}
		}
		if(tr->fi = add_clause(curr->cp, curr->cn))
			goto choose_next2;
		tr->f = __prove_dpll(lev+1, curr, mask>>1);
	choose_next2:;
	} else {
		return __prove_dpll(lev+1, curr, mask>>1);
	}
	return tr;
}

void proof_dpll_proof(
	struct etree *et,
	struct dpll_tree *tr,
	struct lit_set *cl,
	int *cl_ref,
	int n);
int prove_dpll(struct etree *et)
{
	struct lit_set assign;
	struct dpll_tree *tr;
	unsigned long long cp, cn, mask;
	int i;
	struct etree *t;

	t = simp_dist(et);
	etree_dump_prefix(t, stderr);
	fprintf(stderr, "\n");

	num_clauses = 0;
	cons_clause(t);

	/* 消去没有使用的变量 */
	cp = 0;
	cn = 0;
	for(i = 0; i < num_clauses; i++)
	{
		cp |= clauses[i].cp;
		cn |= clauses[i].cn;
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

	fprintf(stderr, "num:%d\n", num_clauses);
	fprintf(stderr, "initial assign %016llx %016llx mask %016llx\n", assign.cp, assign.cn, mask);

	/* 搜索并证明 */
	memset(cl_ref, 0, sizeof(cl_ref));
	pool_init();
	if(!setjmp(env))
	{
		tr = __prove_dpll(0, &assign, mask);
		proof_dpll_proof(et, tr, clauses, cl_ref, num_clauses);
	}
	else
	{
		pool_free();
		fprintf(stderr, "no!\n");
		return 0;
	}
	pool_free();
	return num_clauses+1;
}
