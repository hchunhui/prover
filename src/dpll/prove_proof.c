#include <stdio.h>
#include <stdlib.h>
#include "etree.h"
#include "proof.h"
#include "dpll.h"

struct __internal
{
	unsigned long long cp;
	unsigned long long cn;
};

static void print_lit(int v)
{
        if(v > 0)
        {
                prop_print(v-1, pout);
        }
        else
        {
                fprintf(pout, "~");
                prop_print(-v-1, pout);
        }
}

static void print_vec(int *vec, int n)
{
	int i;
	if(n == 0)
		fprintf(pout, "False");
	else
	{
		print_lit(vec[0]);
		for(i = 1; i < n; i++)
		{
			fprintf(pout, "\\/");
			print_lit(vec[i]);
		}
	}
}

static void rep_print(char *p, int count)
{
	int i;
	for(i = 0; i < count; i++)
		fprintf(pout, "%s", p);
}

static int bit2vec(unsigned long long cp, unsigned long long cn, int *vec)
{
	int i, r;
	r = 0;
	for(i = 0; i < 64; cp >>=1, i++)
		if(cp & 1)
		{
			vec[r] = i+1;
			r++;
		}
	for(i = 0; i < 64; cn >>=1, i++)
		if(cn & 1)
		{
			vec[r] = -(i+1);
			r++;
		}
	return r;
}

static int or_merge(int *vec1, int n1, int *vec2, int n2, int *rank, int *vec)
{
	int i;
	int r;
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
	r = 0;
	for(i = 0; i < 128; i++)
		rank[i] = -1;
	for(i = 0; i < 64; cp >>=1, i++)
		if(cp & 1)
		{
			rank[i] = r;
			vec[r] = i+1;
			r++;
		}
	for(i = 0; i < 64; cn >>=1, i++)
		if(cn & 1)
		{
			rank[64+i] = r;
			vec[r] = -(i+1);
			r++;
		}
	return r;
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

static int __goal_include(struct etree *p, struct __internal *goal)
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

static int __proof_dist(struct etree *p, int from, int hc, struct __internal *goal)
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

static void resolve(int *vec, int n)
{
	int i;
	int hcount = 1;
	for(i = 0; i < n; i++)
	{
		if(i != n - 1)
			fprintf(pout, "(or_ind ");
		fprintf(pout, "(fun (H%d:", hcount++);
		print_lit(vec[i]);
		fprintf(pout, ") => ");
		if(vec[i] > 0)
			fprintf(pout, "F%d H%d", vec[i]-1, hcount-1);
		else
			fprintf(pout, "H%d T%d", hcount-1, -vec[i]-1);
		fprintf(pout, ")");
		if(i == n - 1)
			rep_print(")", n-1);
	}
}


static void define_hypothesis(int seq,
			      unsigned long long cp,
			      unsigned long long cn,
			      struct etree *et)
{
	struct __internal goal;
	goal.cp = cp;
	goal.cn = cn;
	fprintf(pout, "Definition L%d:=((fun (H0:", seq);
	etree_dump_infix(et, pout);
	fprintf(pout, ") =>\n");
	__proof_dist(et, 0, 1, &goal);
	fprintf(pout, ") L0').\nCheck (L%d).\n", seq);
}

static void define_theorem(
	unsigned long long cp,
	unsigned long long cn,
	int hseq)
{
	int vec[128];
	int n;
	n = bit2vec(cp, cn, vec);
	fprintf(pout, "(");
	resolve(vec, n);
	fprintf(pout, "L%d)", hseq);
}

static void __prove_dpll_proof(struct dpll_tree *tr, struct lit_set *cl)
{
	int lev = tr->lev;
	fprintf(pout, "(fun (F%d:~", lev);print_lit(lev+1);
	fprintf(pout, ") => (");
	if(!tr->f)
		define_theorem(cl[tr->fi].cp, cl[tr->fi].cn, tr->fi+1);
	else
		__prove_dpll_proof(tr->f, cl);
	fprintf(pout, ")) (fun (T%d:", lev);print_lit(lev+1);
	fprintf(pout, ") => (");
	if(!tr->t)
		define_theorem(cl[tr->ti].cp, cl[tr->ti].cn, tr->ti+1);
	else
		__prove_dpll_proof(tr->t, cl);
	fprintf(pout, "))");
}

void proof_dpll_proof(
	struct etree *et,
	struct dpll_tree *tr,
	struct lit_set *cl,
	int *cl_ref,
	int n)
{
	int i;
	for(i = 0; i < n; i++) {
		if(cl_ref[i] == 0)
			continue;
		define_hypothesis(i+1, cl[i].cp, cl[i].cn, et);
	}
	fprintf(pout, "Lemma L%d:False.\nProof (", n+1);
	__prove_dpll_proof(tr, cl);
	fprintf(pout, ").\n");
}
