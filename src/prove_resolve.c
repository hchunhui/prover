#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "etree.h"
#include "list.h"

void resolve(
	int *vec1, int n1,
	int *vec2, int n2,
	int *vec1p, int n1p,
	int *vec2p, int n2p,
	int var);
int bit2vec(unsigned long long cp, unsigned long long cn, int *vec);

char prop_name[64][16];

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
}

static void __cons_clause(struct etree *p, struct list *list)
{
	switch(p->type)
	{
	case T_PROP:
		if(p->val > 0)
			list->cp |= 1ull << (p->val-1);
		else
			list->cn |= 1ull << (-p->val-1);
		break;
	case T_OR:
		__cons_clause(p->l, list);
		__cons_clause(p->r, list);
		break;
	}
}

static struct list *cons_clause(struct etree *p)
{
	struct list *cl1, *cl2, *cl;
	switch(p->type)
	{
	case T_AND:
		cl1 = cons_clause(p->l);
		cl2 = cons_clause(p->r);
		for(cl = cl1; cl->next; cl = cl->next);
		cl->next = cl2;
		return cl1;
	default:
		cl = list_new();
		cl->cp = 0;
		cl->cn = 0;
		__cons_clause(p, cl);
		return cl;
	}
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

struct list *proof_dist(struct etree *p)
{
	struct etree *t;
	struct list *list, *pl;
	int i;
	t = simp_dist(p);
	etree_dump_prefix(t, stderr);
	fprintf(stderr, "\n");
	list = cons_clause(t);
	return list;
}


int max(int a, int b)
{
	return a>b?a:b;
}

static int bit_count4(unsigned int n) 
{ 
    n = (n & 0x55555555) + ((n >> 1) & 0x55555555) ; 
    n = (n & 0x33333333) + ((n >> 2) & 0x33333333) ; 
    n = (n & 0x0f0f0f0f) + ((n >> 4) & 0x0f0f0f0f) ; 
    n = (n & 0x00ff00ff) + ((n >> 8) & 0x00ff00ff) ; 
    n = (n & 0x0000ffff) + ((n >> 16) & 0x0000ffff) ; 

    return n ; 
}

static int bit_count(unsigned long long x)
{
	return bit_count4(x&0xffffffff)+bit_count4(x>>32);
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

void define_hypothesis(struct list *p, struct etree *et)
{
	printf("Definition L%d:=((fun (H0:", p->seq);
	etree_dump_infix(et, stdout);
	printf(") =>\n");
	__proof_dist(et, 0, 1, p);
	printf(") L0').\nCheck (L%d).\n", p->seq);
}

void define_theorem(struct list *p)
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

void clause_show(struct list *p, struct etree *et)
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
	int orig_seq;
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

int prove(struct etree *et)
{
	struct list *base, *pend;
	struct list *is, *ir, *it;
	struct list *p;
	unsigned long long x, x1, x2;
	int seq = 1;
	int orig_seq;
	struct list *clauses;
	clauses = proof_dist(et);
	base = NULL;
	pend = clauses;
	for(;;)
	{
		if(pend == NULL)
		{
			printf("(* no *)\n");
			return 0;
		}
		is = pend;
		pend = NULL;
		for(; is;)
		{
			ir = is;
			is = is->next;
			if(ir->cp & ir->cn)
			{
				list_free(ir);
				continue;
			}
			if(!list_insert(&base, ir))
			{
				list_free(ir);
				continue;
			}
			fprintf(stderr, "search [%d]\r", seq++);
			fflush(stderr);
			for(it = base->next; it; it = it->next)
			{
				x1 = (it->cp & ir->cn);
				x2 = (it->cn & ir->cp);
				x = x1 | x2;
				if(x == 0 || x&(x-1))
					continue;
				p = list_new();
				p->cp = (it->cp & (~x1)) | (ir->cp & (~x2));
				p->cn = (it->cn & (~x2)) | (ir->cn & (~x1));
				if(p->cp & p->cn)
				{
					list_free(p);
					continue;
				}
				if(bit_count(p->cp)+bit_count(p->cn) >
				   max(bit_count(it->cp)+bit_count(it->cn),
				       bit_count(ir->cp)+bit_count(ir->cn)))
				{
					list_free(p);
					continue;
				}
				p->f1 = it;
				p->f2 = ir;
				if(p->cp == 0 && p->cn == 0)
				{
					printf("(* yes *)\n");
					return proof_prove(p, et, 1)-1;
				}
				p->next = pend;
				pend = p;
	       		}
		}
	}
}

