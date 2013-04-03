#ifndef _DPLL_H_
#define _DPLL_H_

struct dpll_tree
{
	struct dpll_tree *t, *f;
	int lev;
	int ti, fi;
};

struct lit_set
{
	unsigned long long cp;
	unsigned long long cn;
};

int prove_dpll();
void prove_dpll_proof(int seq, struct lit_set *lit, void *extra);
#endif /* _DPLL_H_ */
