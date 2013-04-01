#include <stdio.h>
#include "dpll.h"
#include "proof.h"
#include "pred.h"
#include "proof_utils.h"
static int fa[64];
static int id[64];
static int vec[128];

static int get_fa(int v)
{
	while(fa[v] != v)
		v = fa[v];
	return v;
}

static int get_fa_proof(int v)
{
	int n;
	n = 0;
	if(fa[v] == v)
	{
		fprintf(pout, "(refl_equal x%d)", v);
		return v;
	}
	while(fa[v] != v)
	{
		if(fa[fa[v]] != fa[v])
			fprintf(pout, "(trans_eq ");
		fprintf(pout, "H%d ", id[v]);
		if(fa[fa[v]] == fa[v])
			rep_print(")", n);
		v = fa[v];
		n++;
	}
	return v;
}

static void set_init()
{
	int i;
	for(i = 0; i < 64; i++) {
		fa[i] = i;
		id[i] = 0;
	}
}

static int set_find(int idx, int idy)
{
	int fx, fy;
	fprintf(pout, "(trans_eq ");
	fx = get_fa_proof(idx);
	fprintf(pout, "(sym_eq ");
	fy = get_fa_proof(idy);
	fprintf(pout, "))");
	return fx == fy;
}

static void set_union(int idx, int idy, int hseq)
{
	int fx, fy;
	fx = get_fa(idx);
	fy = get_fa(idy);
	if(fy != fx) {
		fa[fx]=fy;
		id[fx] = hseq;
	}
}

void equal_proof(int seq, struct lit_set *lit)
{
	int i, n;
	struct pred p;
	fprintf(pout, "Definition L%d := ", seq);
	n = bit2vec(lit->cp, lit->cn, vec);
	set_init();
	for(i = 0; i < n; i++)
	{
		if(vec[i] < 0)
		{
			pred_get(&p, -vec[i]-1);
			set_union(p.lv, p.rv, i);
			fprintf(pout, "horn _ _ (fun H%d:(", i);
			print_lit(-vec[i]);
			fprintf(pout, ") => ");
		}
	}

	for(i = 0; i < n; i++)
	{
		if(vec[i] > 0)
		{
			pred_get(&p, vec[i]-1);
			set_find(p.lv, p.rv);
			break;
		}
	}

	rep_print(")", n-1);
	fprintf(pout, ".\nCheck (L%d).\n", seq);
}
