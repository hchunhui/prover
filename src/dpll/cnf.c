#include "etree.h"
#include "gamma.h"
#include "cnf.h"

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

void cnf_gen_gamma(struct etree *et)
{
	/* FIXME: memory leak */
	struct etree *t;
	t = simp_dist(et);
	etree_dump_prefix(t, stderr);
	fprintf(stderr, "\n");
	cons_clause(et, t);
}
