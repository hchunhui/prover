#include "gamma.h"
#include <stdio.h>
#include <stdlib.h>
#define MAX 1024
static struct lit_set gamma[MAX];
static int num_gamma;

int gamma_search(unsigned long long cp,
		 unsigned long long cn)
{
	int i;
	for(i = 0; i < num_gamma; i++)
		if(gamma[i].cp == cp &&
		   gamma[i].cn == cn)
			return i;
	return -1;
}

int gamma_add(unsigned long long cp,
	      unsigned long long cn)
{
	int id;
	id = gamma_search(cp, cn);
	if(id != -1)
		return id;
	if(num_gamma == MAX)
	{
		fprintf(stderr, "gamma full\n");
		exit(1);
	}
	id = num_gamma;
	gamma[id].cp = cp;
	gamma[id].cn = cn;
	gamma[id].proof = NULL;
	gamma[id].extra = NULL;
	gamma[id].ref = 0;
	num_gamma++;
	return id;
}

void gamma_add_proof(int id,
		     void (*proof)(int seq, struct lit_set *lit),
		     void *extra)
{
	gamma[id].proof = proof;
	gamma[id].extra = extra;
}

void gamma_ref(int id)
{
	gamma[id].ref = 1;
}

int gamma_match(unsigned long long cpmask,
		unsigned long long cnmask)
{
	int i;
	for(i = 0; i < num_gamma; i++)
	{
		if((gamma[i].cp & cpmask) == 0ull &&
		   (gamma[i].cn & cnmask) == 0ull)
			return i;
	}
	return -1;
}

void gamma_get(int id, struct lit_set *lit)
{
	*lit = gamma[id];
}

int gamma_get_num()
{
	return num_gamma;
}

void gamma_proof()
{
	int i;
	for(i = 0; i < num_gamma; i++)
		if(gamma[i].proof)
			gamma[i].proof(i+1, gamma + i);
}

void gamma_init()
{
	num_gamma = 0;
}
