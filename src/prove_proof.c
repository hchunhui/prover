#include <stdio.h>
#include <stdlib.h>
#include "comm.h"
#include "proof.h"
#include "dpll.h"

static void proof(LitSet *ls, int hseq)
{
	int i, j;
	int hcount;
	hcount = 1;
	fprintf(pout, "(");
	for(i = 0; i < ls->n; i++)
	{
		if(i != ls->n-1)
			fprintf(pout, "(or_ind ");
		fprintf(pout, "(fun (H%d:", hcount++);
		lit_print(ls->mem[i], pout);
		fprintf(pout, ") => ");
		if(ls->mem[i].neg == 0)
			fprintf(pout, "F%d H%d", ls->mem[i].id, hcount-1);
		else
			fprintf(pout, "H%d T%d", hcount-1, ls->mem[i].id);
		fprintf(pout, ")");
		if(i == ls->n-1) {
			for(j = 0; j < ls->n-1;j++)
				fprintf(pout, ")");
		}
	}
	fprintf(pout, "L%d)", hseq);
}

static void __prove_dpll_proof(struct dpll_tree *tr, int i)
{
	LitSet *ls;
	fprintf(pout, "(fun (F%d:~", i);
	lit_print(tr->lit, pout);
	fprintf(pout, ") => (");
	if(!tr->f) {
		ls = gamma_get(tr->fi);
		proof(ls, tr->fi+1);
	} else {
		__prove_dpll_proof(tr->f, i+1);
	}
	fprintf(pout, ")) (fun (T%d:", i);
	lit_print(tr->lit, pout);
	fprintf(pout, ") => (");
	if(!tr->t) {
		ls = gamma_get(tr->ti);
		proof(ls, tr->ti+1);
	} else {
		__prove_dpll_proof(tr->t, i+1);
	}
	fprintf(pout, "))");
}

void prove_dpll_proof(int seq, LitSet *cl, void *extra)
{
	struct dpll_tree *tr = extra;
	fprintf(pout, "Lemma L%d:False.\nProof (", seq);
	__prove_dpll_proof(tr, 0);
	fprintf(pout, ").\n");
}
