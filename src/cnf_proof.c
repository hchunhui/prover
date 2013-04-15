#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include "comm.h"
#include "proof.h"
#include "cnf.h"

static int __goal_include(struct etree *p, LitSet *goal)
{
	int i;
	switch(p->type)
	{
	case T_OR:
		return __goal_include(p->l, goal) && __goal_include(p->r, goal);
	case T_AND:
		return __goal_include(p->l, goal) || __goal_include(p->r, goal);
	case T_PROP:
		for(i = 0; i < goal->n; i++)
			if(goal->mem[i].neg == p->val.neg &&
			   goal->mem[i].id  == p->val.id)
				return 1;
		return 0;
	}
	return 0;
}

static void or_intro(int rank, LitSet *ls, int hi)
{
	int i;
//	fprintf(pout, "(* %d *)", rank);
	for(i = 0; i < rank; i++)
	{
		fprintf(pout, "(or_intror (");
		lit_print(ls->mem[i], pout);
		fprintf(pout, ") ");
	}
	if(rank < ls->n-1)
	{
		fprintf(pout, "(or_introl (");
		litset_print(ls, rank+1, "\\/", pout);
		fprintf(pout, ") H%d)", hi);
	}
	else
		fprintf(pout, "H%d", hi);
	for(i = 0; i < rank; i++)
		fprintf(pout, ")");
}

static int __proof_dist(struct etree *p, int from, int hc, LitSet *goal)
{
	int thc;
	int i;
	switch(p->type)
	{
	case T_AND:
		thc = hc;
		fprintf(pout, "(and_ind (fun (H%d:", hc++);
		etree_dump_infix(p->l, pout);
		fprintf(pout, ") (H%d:", hc++);
		etree_dump_infix(p->r, pout);
		fprintf(pout, ") => (");
		if(__goal_include(p->l, goal))
			hc = __proof_dist(p->l, thc, hc, goal);
		else if(__goal_include(p->r, goal))
			hc = __proof_dist(p->r, thc+1, hc, goal);
		fprintf(pout, "))H%d)\n", from);
		break;
	case T_OR:
		thc = hc;
		fprintf(pout, "(or_ind\n");
		fprintf(pout, "(fun (H%d:", hc++);
		etree_dump_infix(p->l, pout);
		fprintf(pout, ") => (");
		hc = __proof_dist(p->l, thc, hc, goal);
		fprintf(pout, "))\n");
		thc = hc;
		fprintf(pout, "(fun (H%d:", hc++);
		etree_dump_infix(p->r, pout);
		fprintf(pout, ") => (");
		hc = __proof_dist(p->r, thc, hc, goal);
		fprintf(pout, "))\n");
		fprintf(pout, "H%d)\n", from);
		break;
	case T_PROP:
		for(i = 0; i < goal->n; i++)
			if(goal->mem[i].neg == p->val.neg &&
			   goal->mem[i].id  == p->val.id)
				break;
		assert(i < goal->n);
		or_intro(i, goal, from);
		break;
	}
	return hc;
}

void cnf_proof(int seq, LitSet *cl, void *extra)
{
	struct etree *et = extra;
	fprintf(pout, "Definition L%d:=((fun (H0:", seq);
	etree_dump_infix(et, pout);
	fprintf(pout, ") =>\n");
	__proof_dist(et, 0, 1, cl);
	fprintf(pout, ") L0').\nCheck (L%d).\n", seq);
}
