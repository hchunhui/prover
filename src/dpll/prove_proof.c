#include <stdio.h>
#include <stdlib.h>
#include "proof.h"
#include "dpll.h"
#include "proof_utils.h"
#include "gamma.h"

static void proof(
	unsigned long long cp,
	unsigned long long cn,
	int hseq)
{
	int i, n;
	int vec[128];
	int hcount;
	n = bit2vec(cp, cn, vec);
	hcount = 1;
	fprintf(pout, "(");
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
	fprintf(pout, "L%d)", hseq);
}

static void __prove_dpll_proof(struct dpll_tree *tr)
{
	struct lit_set lit;
	int lev = tr->lev;
	fprintf(pout, "(fun (F%d:~", lev);print_lit(lev+1);
	fprintf(pout, ") => (");
	if(!tr->f) {
		gamma_get(tr->fi, &lit);
		proof(lit.cp, lit.cn, tr->fi+1);
	} else {
		__prove_dpll_proof(tr->f);
	}
	fprintf(pout, ")) (fun (T%d:", lev);print_lit(lev+1);
	fprintf(pout, ") => (");
	if(!tr->t) {
		gamma_get(tr->ti, &lit);
		proof(lit.cp, lit.cn, tr->ti+1);
	} else {
		__prove_dpll_proof(tr->t);
	}
	fprintf(pout, "))");
}

void prove_dpll_proof(int seq, struct lit_set *cl, void *extra)
{
	struct dpll_tree *tr = extra;
	fprintf(pout, "Lemma L%d:False.\nProof (", seq);
	__prove_dpll_proof(tr);
	fprintf(pout, ").\n");
}
