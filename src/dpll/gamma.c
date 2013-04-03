#include <stdio.h>
#include <stdlib.h>
#include "gamma.h"
#include "proof.h"
#include "proof_utils.h"

#define MAX 1024

struct gamma_list
{
	struct lit_set lit;
	int ref;
	void (*proof)(int seq, struct lit_set *lit, void *extra);
	void *extra;
};

static struct gamma_list gamma[MAX];
static int num_gamma;

int gamma_search(unsigned long long cp,
		 unsigned long long cn)
{
	int i;
	for(i = 0; i < num_gamma; i++)
		if(gamma[i].lit.cp == cp &&
		   gamma[i].lit.cn == cn)
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
	gamma[id].lit.cp = cp;
	gamma[id].lit.cn = cn;
	gamma[id].proof = NULL;
	gamma[id].extra = NULL;
	gamma[id].ref = 0;
	num_gamma++;
	return id;
}

void gamma_add_proof(int id,
		     void (*proof)(int seq, struct lit_set *lit, void *extra),
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
		if((gamma[i].lit.cp & cpmask) == 0ull &&
		   (gamma[i].lit.cn & cnmask) == 0ull)
			return i;
	}
	return -1;
}

void gamma_get(int id, struct lit_set *lit)
{
	*lit = gamma[id].lit;
}

int gamma_get_num()
{
	return num_gamma;
}

void gamma_proof()
{
	int i, n;
	int vec[128];
	for(i = 0; i < num_gamma; i++)
	{
		if(!gamma[i].ref)
			continue;
		if(gamma[i].proof)
			gamma[i].proof(i+1, &gamma[i].lit, gamma[i].extra);
		else
		{
			fprintf(pout, "Lemma L%d:(", i+1);
			n = bit2vec(gamma[i].lit.cp, gamma[i].lit.cn, vec);
			print_vec(vec, n);
			fprintf(pout, ").\nAdmitted.\nCheck L%d.\n", i+1);
		}
	}
}

void gamma_init()
{
	num_gamma = 0;
}
