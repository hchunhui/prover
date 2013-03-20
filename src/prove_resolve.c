#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "list.h"

void resolve(
	int *vec1, int n1,
	int *vec2, int n2,
	int *vec1p, int n1p,
	int *vec2p, int n2p,
	int var);
int bit2vec(unsigned long long cp, unsigned long long cn, int *vec);

char prop_name[64][16];

int max(int a, int b)
{
	return a>b?a:b;
}

void define_clause(struct list *p)
{
	int i;
	unsigned long long x;
	int flag = 0;
	if((p->cp | p->cn) == 0)
	{
		printf("False");
		return;
	}
	x = p->cp;
	for(i = 0; i < 64; i++)
	{
		if(x & 1)
		{
			printf(" %s %s", flag?"\\/":"", prop_name[i]);
			flag = 1;
		}
		x = x >> 1;
	}
	x = p->cn;
	for(i = 0; i < 64; i++)
	{
		if(x & 1)
		{
			printf(" %s ~%s", flag?"\\/":"", prop_name[i]);
			flag = 1;
		}
		x = x >> 1;
	}
}

void define_hypothesis(struct list *p, int orig_seq)
{
#if 0
	printf("Hypothesis L%d:", p->seq);
	define_clause(p);
	printf(".\n");
#else
	printf("Definition L%d := (_L%d L0').\n", p->seq, orig_seq);
#endif
}

int calc_resolve_var(struct list *f1, struct list *f2)
{
	unsigned long long x;
	int i;
	x = (f1->cp & f2->cn) | (f1->cn & f2->cp);
	for(i = 0; i < 64; i++)
	{
		if (x & 1)
			return i;
		x>>=1;
	}
}

void define_theorem(struct list *p)
{
	int rvar;
	int vec1[128];
	int vec2[128];
	int vec1p[128];
	int vec2p[128];
	int n1, n2, n1p, n2p;
	rvar = calc_resolve_var(p->f1, p->f2);
	printf("Lemma L%d:", p->seq);
	define_clause(p);
	printf(".\nProof (\n");
	n1 = bit2vec(p->f1->cp, p->f1->cn, vec1);
	n2 = bit2vec(p->f2->cp, p->f2->cn, vec2);
	n1p = bit2vec(p->f1->cp & (~(1<<rvar)), p->f1->cn & (~(1<<rvar)), vec1p);
	n2p = bit2vec(p->f2->cp & (~(1<<rvar)), p->f2->cn & (~(1<<rvar)), vec2p);
	if(p->f1->cp & (1<<rvar))
	{
		resolve(vec1, n1, vec2, n2, vec1p, n1p, vec2p, n2p, rvar+1);
		printf("L%d L%d).\n", p->f1->seq, p->f2->seq);
	}
	else
	{
		resolve(vec2, n2, vec1, n1, vec2p, n2p, vec1p, n1p, rvar+1);
		printf("L%d L%d).\n", p->f2->seq, p->f1->seq);
	}
}

void clause_show(struct list *p, int orig_seq)
{
	int is_hypothesis = !(p->f1 && p->f2);
	printf("(* [%3d] ", p->seq);
//	define_clause(p);
	if(is_hypothesis)
	{
		printf("   hypothesis *)\n");
		define_hypothesis(p, orig_seq);
	}
	else
	{
		printf("   resolve [%d] [%d] *)\n", p->f1->seq, p->f2->seq);
		define_theorem(p);
	}
	printf("\n");
}

int bit_count4(unsigned int n) 
{ 
    n = (n & 0x55555555) + ((n >> 1) & 0x55555555) ; 
    n = (n & 0x33333333) + ((n >> 2) & 0x33333333) ; 
    n = (n & 0x0f0f0f0f) + ((n >> 4) & 0x0f0f0f0f) ; 
    n = (n & 0x00ff00ff) + ((n >> 8) & 0x00ff00ff) ; 
    n = (n & 0x0000ffff) + ((n >> 16) & 0x0000ffff) ; 

    return n ; 
}

int bit_count(unsigned long long x)
{
	return bit_count4(x&0xffffffff)+bit_count4(x>>32);
}

int prove(struct list *clauses)
{
	struct list *base, *pend;
	struct list *is, *ir, *it;
	struct list *p;
	unsigned long long x, x1, x2;
	int seq = 1;
	int orig_seq;
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
			orig_seq = ir->seq;
			ir->seq = seq++;
			clause_show(ir, orig_seq);
			for(it = base->next; it; it = it->next)
			{
				x1 = (it->cp & ir->cn);
				x2 = (it->cn & ir->cp);
				x = x1 | x2;
/*				x = (it->cp & ir->cn) | (it->cn & ir->cp);*/
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
					orig_seq = p->seq;
					p->seq = seq++;
					clause_show(p, orig_seq);
					printf("(* yes *)\n");
					return p->seq;
				}
				p->next = pend;
				pend = p;
	       		}
		}
	}
}

