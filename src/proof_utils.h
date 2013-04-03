#ifndef _PROOF_UTILS_H_
#define _PROOF_UTILS_H_
#include "proof.h"
#include "pred.h"

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
	for(i = 0; i < 64; cn >>=1, i++)
		if(cn & 1)
		{
			vec[r] = -(i+1);
			r++;
		}
	for(i = 0; i < 64; cp >>=1, i++)
		if(cp & 1)
		{
			vec[r] = (i+1);
			r++;
		}
	return r;
}

#endif /* _PROOF_UTILS_H_ */
