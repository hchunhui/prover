#include <stdio.h>
#include "dpll.h"
#include "proof.h"
#include "pred.h"
#include "func.h"
#include "proof_utils.h"
static int fa[64];
static int id[64];
static int count;

static int get_fa_proof(int v)
{
	int n;
	n = 0;
	if(fa[v] == v)
	{
		fprintf(pout, "(refl_equal ");
		func_print(v, pout);
		fprintf(pout, ")");
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
	count = 0;
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
	fprintf(pout, "let H%d := ", count++);
	fprintf(pout, "(trans_eq (trans_eq (sym_eq (");
	fx = get_fa_proof(idx);
	fprintf(pout, ")) H%d) ", hseq);
	fy = get_fa_proof(idy);
	fprintf(pout, ")");
	fa[fx]= fy;
	id[fx] = count-1;
	fprintf(pout, " in ");
}

void equal_proof(int seq, struct lit_set *lit)
{
	int i, n;
	struct pred p;
	int vec[128];

	fprintf(pout, "Definition L%d := ", seq);
	n = bit2vec(lit->cp, lit->cn, vec);
	set_init();
	for(i = 0; i < n; i++)
	{
		if(vec[i] < 0)
		{
			pred_get(&p, -vec[i]-1);
			fprintf(pout, "horn _ _ (fun H%d:(", count++);
			print_lit(-vec[i]);
			fprintf(pout, ") => ");
			set_union(p.lv, p.rv, count-1);
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

void equal_uif_proof(int seq, struct lit_set *lit)
{
	int i, j, n;
	struct pred p;
	struct func f1, f2;
	struct func_info fi;
	int vec[128];
	int h[64];

	fprintf(pout, "(*uif*)\nDefinition L%d := ", seq);
	n = bit2vec(lit->cp, lit->cn, vec);
	for(i = 0; i < n; i++)
	{
		if(vec[i] < 0)
		{
			pred_get(&p, -vec[i]-1);
			fprintf(pout, "horn _ _ (fun H%d:(", i);
			print_lit(-vec[i]);
			fprintf(pout, ") => ");
			h[p.lv] = i;
		}
	}

	for(i = 0; i < n; i++)
	{
		if(vec[i] > 0)
		{
			pred_get(&p, vec[i]-1);
			func_get(&f1, &fi, p.lv);
			func_get(&f2, &fi, p.rv);
			break;
		}
	}

	for(i = 0; i < fi.n; i++)
	{
		if(f1.arr[i] == f2.arr[i])
			continue;
		fprintf(pout, "(eq_ind _ (fun _x => %s", fi.name);
		for(j = 0; j < fi.n; j++)
		{
			fprintf(pout, " ");
			func_print(f1.arr[j], pout);
		}
		fprintf(pout, " = %s", fi.name);
		for(j = 0; j < fi.n; j++)
		{
			fprintf(pout, " ");
			if(j < i)
				func_print(f1.arr[j], pout);
			else if(j > i)
				func_print(f2.arr[j], pout);
			else
				fprintf(pout, "_x");
		}
		fprintf(pout, ")");
	}
	fprintf(pout, "(refl_equal _)");
	for(i = fi.n - 1; i >= 0; i--)
	{
		if(f1.arr[i] == f2.arr[i])
			continue;
		fprintf(pout, " _ H%d)", h[f1.arr[i]]);
	}
	rep_print(")", n-1);
	fprintf(pout, ".\nCheck (L%d).\n", seq);
}
