#ifndef _DPLL_H_
#define _DPLL_H_

struct dpll_tree
{
	struct dpll_tree *t, *f;
	Lit lit;
	int ti, fi;
};

int prove_dpll();
void prove_dpll_proof(int seq, LitSet *lit, void *extra);
#endif /* _DPLL_H_ */
