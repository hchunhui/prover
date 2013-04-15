#include <stdio.h>
#include <stdlib.h>
#include "comm.h"
#include "gamma.h"
#include "proof.h"

#define MAX 1024

struct gamma_list
{
	LitSet *lit;
	int ref;
	void (*proof)(int seq, LitSet *lit, void *extra);
	void *extra;
};

static struct gamma_list gamma[MAX];
static int num_gamma;

int gamma_search(LitSet *ls)
{
	int i;
	int j;
	for(i = 0; i < num_gamma; i++)
	{
		if(ls->n != gamma[i].lit->n)
			continue;
		for(j = 0; j < ls->n ; j++)
			if(gamma[i].lit->mem[j].neg != ls->mem[j].neg ||
			   gamma[i].lit->mem[j].id  != ls->mem[j].id)
				break;
		if(j == ls->n)
			return i;
	}
	return -1;
}

int gamma_add(LitSet *ls)
{
	int id;
	id = gamma_search(ls);
	if(id != -1)
	{
		litset_del(ls);
		return id;
	}
	if(num_gamma == MAX)
	{
		fprintf(stderr, "gamma full\n");
		exit(1);
	}
	id = num_gamma;
	gamma[id].lit = ls;
	gamma[id].proof = NULL;
	gamma[id].extra = NULL;
	gamma[id].ref = 0;
	num_gamma++;
	return id;
}

void gamma_add_proof(int id,
		     void (*proof)(int seq, LitSet *lit, void *extra),
		     void *extra)
{
	gamma[id].proof = proof;
	gamma[id].extra = extra;
}

void gamma_ref(int id)
{
	gamma[id].ref = 1;
}

int gamma_match(LitSet *ls)
{
	int i;
	int k, j1, k1;
	LitSet *ls1;
	int flag;
	for(i = 0; i < num_gamma; i++)
	{
		ls1 = gamma[i].lit;
		//fprintf(stderr, "gamma_match %d: ", i);
		//litset_print(ls1, 0, "\\/", stderr);
		//fprintf(stderr, " ");
		//litset_print(ls, 0, "/\\", stderr);
		//fprintf(stderr, "\n");

		for(k = 0; k < ls1->n; k++)
			if(ls1->mem[k].neg == 0)
				break;
		if(k == ls1->n)
			k = 0;
		flag = 0;
		for(j1 = k1 = 0; j1 < ls->n && k1 < ls1->n;)
		{
			int nl, il;
			if(ls->mem[j1].neg && ls1->mem[k+k1].neg)
				nl = -1;
			else if((!ls->mem[j1].neg) == ls1->mem[k+k1].neg)
				nl = 0;
			else
				nl = 1;
			il = ls->mem[j1].id - ls1->mem[k+k1].id;
			//fprintf(stderr, "j%d k%d, %d %d nl=%d il=%d\n",j1, k+k1, ls->mem[j1].neg, ls1->mem[k+k1].neg, nl, il);
			if(nl < 0 || (nl == 0 && il < 0))
				j1++;
			else if (nl == 0 && il == 0)
			{
				j1++;
				k1++;
				if(k+k1 >= ls1->n) k -= ls1->n;
			}
			else
			{
				flag = 1;
				break;
			}
		}
		if(j1 == ls->n && k1 < ls1->n)
			continue;
		if(flag)
			continue;
		//fprintf(stderr, "ok\n");
		gamma_ref(i);
		return i;
	}
	//fprintf(stderr, "fail\n");
	return -1;
}

LitSet *gamma_get(int id)
{
	return gamma[id].lit;
}

int gamma_get_num()
{
	return num_gamma;
}

void gamma_proof()
{
	int i;
	for(i = 0; i < num_gamma; i++)
	{
		if(!gamma[i].ref)
			continue;
		if(gamma[i].proof)
			gamma[i].proof(i+1, gamma[i].lit, gamma[i].extra);
		else
		{
			fprintf(pout, "Lemma L%d:(", i+1);
			litset_print(gamma[i].lit, 0, "\\/", pout);
			fprintf(pout, ").\nAdmitted.\nCheck L%d.\n", i+1);
		}
	}
}

void gamma_init()
{
	num_gamma = 0;
}
