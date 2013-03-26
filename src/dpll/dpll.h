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

#endif /* _DPLL_H_ */
