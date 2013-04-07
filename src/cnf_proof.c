#include <stdio.h>
#include <stdlib.h>
#include "etree.h"
#include "proof.h"
#include "proof_utils.h"
#include "gamma.h"
#include "cnf.h"

static int or_merge(int *vec1, int n1, int *vec2, int n2, int *rank, int *vec)
{
	int i;
	int n;
	unsigned long long cp, cn;
	cp = 0;	cn = 0;
	for(i = 0; i < n1; i++)
		if(vec1[i] > 0)
			cp |= 1ull << (vec1[i]-1);
		else
			cn |= 1ull << (-vec1[i]-1);
	for(i = 0; i < n2; i++)
		if(vec2[i] > 0)
			cp |= 1ull << (vec2[i]-1);
		else
			cn |= 1ull << (-vec2[i]-1);
	for(i = 0; i < 128; i++)
		rank[i] = -1;
	n = bit2vec(cp, cn, vec);
	for(i = 0; i < n; i++)
		if(vec[i] < 0)
			rank[64-vec[i]-1] = i;
		else
			rank[vec[i]-1] = i;
	return n;
}

static void or_intro(int rank, int *vec, int n, int hi)
{
	int i;
//	fprintf(pout, "(* %d *)", rank);
	for(i = 0; i < rank; i++)
	{
		fprintf(pout, "(or_intror (");
		print_lit(vec[i]);
		fprintf(pout, ") ");
	}
	if(rank < n-1)
	{
		fprintf(pout, "(or_introl (");
		print_vec(vec+rank+1, n - rank - 1);
		fprintf(pout, ") H%d)", hi);
	}
	else
		fprintf(pout, "H%d", hi);
	for(i = 0; i < rank; i++)
		fprintf(pout, ")");
}

static void or_make(int *vec1, int n1, int *rank, int *vec, int n)
{
	int i, j;
	for(i = 0; i < n1; i++)
	{
		if(i != n1 - 1)
			fprintf(pout, "(or_ind (fun (H1:");
		else
			fprintf(pout, "(fun (H1:");
		print_lit(vec1[i]);
		fprintf(pout, ") => ");
		/*FIXME: -1 or not*/
		or_intro(rank[vec1[i]>0?vec1[i]-1:(63-vec1[i])], vec, n, 1);
		fprintf(pout, ")\n");
		if(i == n1 - 1)
		{
			for(j = 0; j < n1 - 1; j++)
				fprintf(pout, ")");
		}
	}
}

static void or_trans(int *vec1, int n1, int *vec2, int n2)
{
	int rank[128];
	int vec[128];
	int n;
	n = or_merge(vec1, n1, vec2, n2, rank, vec);
	fprintf(pout, "(*");
	print_vec(vec, n);
	fprintf(pout, "*)\n");
	fprintf(pout, "(fun (H:(");
	print_vec(vec1, n1);
	fprintf(pout, ")\\/(");
	print_vec(vec2, n2);
	fprintf(pout, ")) =>\n\t");
	fprintf(pout, "(or_ind\n\t(");
	or_make(vec1, n1, rank, vec, n);
	fprintf(pout, ")\n\t (");
	or_make(vec2, n2, rank, vec, n);
	fprintf(pout, ") H))\n");
}

static int __goal_include(struct etree *p, struct lit_set *goal)
{
	switch(p->type)
	{
	case T_OR:
		return __goal_include(p->l, goal) && __goal_include(p->r, goal);
	case T_AND:
		return __goal_include(p->l, goal) || __goal_include(p->r, goal);
	case T_PROP:
		if(p->val < 0 && (goal->cn & (1ull<<(-p->val-1))) ||
		   (p->val > 0 && (goal->cp & (1ull<<(p->val-1)))))
			return 1;
		return 0;
	}
	return 0;
}

static int __proof_dist(struct etree *p, int from, int hc, struct lit_set *goal)
{
	int thc;
	int vec1[128], vec2[1], vec[128];
	int n1, n2, n;
	int rank[128];
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
		n1 = bit2vec(goal->cp, goal->cn, vec1);
		vec2[0] = p->val;
		n2 = 1;
		n = or_merge(vec1, n1, vec2, n2, rank, vec);
		or_intro(rank[p->val>0?p->val-1:(63-p->val)], vec, n, from);
		break;
	}
	return hc;
}

void cnf_proof(int seq, struct lit_set *cl, void *extra)
{
	struct lit_set goal;
	struct etree *et = extra;
	goal.cp = cl->cp;
	goal.cn = cl->cn;
	fprintf(pout, "Definition L%d:=((fun (H0:", seq);
	etree_dump_infix(et, pout);
	fprintf(pout, ") =>\n");
	__proof_dist(et, 0, 1, &goal);
	fprintf(pout, ") L0').\nCheck (L%d).\n", seq);
}