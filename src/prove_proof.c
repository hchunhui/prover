#include <stdio.h>
#include <stdlib.h>
#include "etree.h"
#include "list.h"

extern char prop_name[][16];
static void print_lit(int v)
{
	if(v > 0)
		printf("%s", prop_name[v-1]);
	else
		printf("~%s", prop_name[-v-1]);
}

static void print_vec(int *vec, int n)
{
	int i;
	if(n == 0)
		printf("False");
	else
	{
		print_lit(vec[0]);
		for(i = 1; i < n; i++)
		{
			printf("\\/");
			print_lit(vec[i]);
		}
	}
}

static void rep_print(char *p, int count)
{
	int i;
	for(i = 0; i < count; i++)
		printf("%s", p);
}

static int first_bit(unsigned long long x)
{
	unsigned long long mask = 0xffffffffull;
	int shift = 32;
	int i = 0;
	for(;shift;shift >>= 1, mask >>= shift)
		if((x&mask) == 0) {
			i += shift;
			x >>= shift;
		}
	return i;
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
//	printf("(* %d *)", rank);
	for(i = 0; i < rank; i++)
	{
		printf("(or_intror (");
		print_lit(vec[i]);
		printf(") ");
	}
	if(rank < n-1)
	{
		printf("(or_introl (");
		print_vec(vec+rank+1, n - rank - 1);
		printf(") H%d)", hi);
	}
	else
		printf("H%d", hi);
	for(i = 0; i < rank; i++)
		printf(")");
}

static void or_make(int *vec1, int n1, int *rank, int *vec, int n)
{
	int i, j;
	for(i = 0; i < n1; i++)
	{
		if(i != n1 - 1)
			printf("(or_ind (fun (H1:");
		else
			printf("(fun (H1:");
		print_lit(vec1[i]);
		printf(") => ");
		/*FIXME: -1 or not*/
		or_intro(rank[vec1[i]>0?vec1[i]-1:(63-vec1[i])], vec, n, 1);
		printf(")\n");
		if(i == n1 - 1)
		{
			for(j = 0; j < n1 - 1; j++)
				printf(")");
		}
	}
}

static void or_trans(int *vec1, int n1, int *vec2, int n2)
{
	int rank[128];
	int vec[128];
	int n;
	n = or_merge(vec1, n1, vec2, n2, rank, vec);
	printf("(*");
	print_vec(vec, n);
	printf("*)\n");
	printf("(fun (H:(");
	print_vec(vec1, n1);
	printf(")\\/(");
	print_vec(vec2, n2);
	printf(")) =>\n\t");
	printf("(or_ind\n\t(");
	or_make(vec1, n1, rank, vec, n);
	printf(")\n\t (");
	or_make(vec2, n2, rank, vec, n);
	printf(") H))\n");
}

static void resolve(
	int *vec1, int n1,
	int *vec2, int n2,
	int *vec1p, int n1p,
	int *vec2p, int n2p,
	int var)
{
	int rank[128];
	int vec[128];
	int n;
	int i, j;
	int hcount = 1;
	int pl_count;
	n = or_merge(vec1p, n1p, vec2p, n2p, rank, vec);
	printf("(fun (H%d:(", hcount++);
	print_vec(vec1, n1);
	printf(")) (H%d:(", hcount++);
	print_vec(vec2, n2);
	printf(")) =>\n\t");

	for(i = 0; i < n1; i++)
	{
		if(i != n1 - 1)
			printf("(or_ind ");
		printf("(fun (H%d:", hcount++);
		print_lit(vec1[i]);
		printf(") => ");
		if(vec1[i] != var)
			or_intro(rank[vec1[i]>0?vec1[i]-1:(63-vec1[i])],
				 vec, n, hcount-1);
		else {
			pl_count = hcount-1;
			for(j = 0; j < n2; j++)
			{
				if(j != n2 - 1)
					printf("(or_ind ");
				printf("(fun (H%d:", hcount++);
				print_lit(vec2[j]);
				printf(") => ");
				if(vec2[j] != -var)
					or_intro(rank[vec2[j]>0?vec2[j]-1:(63-vec2[j])],
						 vec, n, hcount-1);
				else {
					printf("False_ind (");
					print_vec(vec, n);
					printf(") (H%d H%d)", hcount-1, pl_count);
				}
				printf(")\n");
				if(j == n2 - 1)
					rep_print(")", n2-1);
			}
			printf("H2");
		}
		printf(")\n");
		if(i == n1 - 1)
			rep_print(")", n1-1);
	}
	printf("H1");
	printf(")\n");
}


static int __goal_include(struct etree *p, struct list *goal)
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

static int __proof_dist(struct etree *p, int from, int hc, struct list *goal)
{
	int thc;
	int vec1[128], vec2[1], vec[128];
	int n1, n2, n;
	int rank[128];
	switch(p->type)
	{
	case T_AND:
		thc = hc;
		printf("(and_ind (fun (H%d:", hc++);
		etree_dump_infix(p->l, stdout);
		printf(") (H%d:", hc++);
		etree_dump_infix(p->r, stdout);
		printf(") => (");
		if(__goal_include(p->l, goal))
			hc = __proof_dist(p->l, thc, hc, goal);
		else if(__goal_include(p->r, goal))
			hc = __proof_dist(p->r, thc+1, hc, goal);
		printf("))H%d)\n", from);
		break;
	case T_OR:
		thc = hc;
		printf("(or_ind\n");
		printf("(fun (H%d:", hc++);
		etree_dump_infix(p->l, stdout);
		printf(") => (");
		hc = __proof_dist(p->l, thc, hc, goal);
		printf("))\n");
		thc = hc;
		printf("(fun (H%d:", hc++);
		etree_dump_infix(p->r, stdout);
		printf(") => (");
		hc = __proof_dist(p->r, thc, hc, goal);
		printf("))\n");
		printf("H%d)\n", from);
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

static void define_hypothesis(struct list *p, struct etree *et)
{
	printf("Definition L%d:=((fun (H0:", p->seq);
	etree_dump_infix(et, stdout);
	printf(") =>\n");
	__proof_dist(et, 0, 1, p);
	printf(") L0').\nCheck (L%d).\n", p->seq);
}

static void define_theorem(struct list *p)
{
	int vec[128];
	int vec1[128], vec2[128];
	int vec1p[128], vec2p[128];
	int n, n1, n2, n1p, n2p;
	unsigned long long x1, x2, x;
	int rvar;
	x1 = p->f1->cp & p->f2->cn;
	x2 = p->f1->cn & p->f2->cp;
	x = x1 | x2;
	rvar = first_bit(x) + 1;
	n = bit2vec(p->cp, p->cn, vec);
	n1 = bit2vec(p->f1->cp, p->f1->cn, vec1);
	n2 = bit2vec(p->f2->cp, p->f2->cn, vec2);
	n1p = bit2vec(p->f1->cp & (~x1), p->f1->cn & (~x2), vec1p);
	n2p = bit2vec(p->f2->cp & (~x2), p->f2->cn & (~x1), vec2p);

	printf("Lemma L%d:", p->seq);
	print_vec(vec, n);
	printf(".\nProof (\n");
	if(p->f1->cp & x)
	{
		resolve(vec1, n1, vec2, n2, vec1p, n1p, vec2p, n2p, rvar);
		printf("L%d L%d).\n", p->f1->seq, p->f2->seq);
	}
	else
	{
		resolve(vec2, n2, vec1, n1, vec2p, n2p, vec1p, n1p, rvar);
		printf("L%d L%d).\n", p->f2->seq, p->f1->seq);
	}
}

static void clause_show(struct list *p, struct etree *et)
{
	int is_hypothesis = !(p->f1);
	printf("(* [%3d] ", p->seq);
	if(is_hypothesis)
	{
		printf("   hypothesis *)\n");
		define_hypothesis(p, et);
	}
	else
	{
		printf("   resolve [%d] [%d] *)\n", p->f1->seq, p->f2->seq);
		define_theorem(p);
	}
	printf("\n");
}

int proof_prove(struct list *g, struct etree *et, int seq)
{
	if(g->f1)
	{
		if(g->f1->seq == 0)
			seq = proof_prove(g->f1, et, seq);
		if(g->f2->seq == 0)
			seq = proof_prove(g->f2, et, seq);
	}
	g->seq = seq;
	clause_show(g, et);
	return seq+1;
}
