#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "etree.h"
#include "list.h"
#include "proof.h"

int proof_prove_naive(struct list *g, struct etree *et, int seq);

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

static int max(int a, int b)
{
	return a>b?a:b;
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

int prove_naive(struct etree *et)
{
	struct list *base, *pend;
	struct list *is, *ir, *it;
	struct list *p;
	unsigned long long x, x1, x2;
	int seq = 1;
	struct list *clauses;
	struct etree *t;

	t = simp_dist(et);
	etree_dump_prefix(t, stderr);
	fprintf(stderr, "\n");
	clauses = cons_clause(t);

	base = NULL;
	pend = clauses;
	for(;;)
	{
		if(pend == NULL)
			return 0;
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
					return proof_prove_naive(p, et, 1)-1;
				p->next = pend;
				pend = p;
	       		}
		}
	}
}
