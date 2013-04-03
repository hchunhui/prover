#include <stdio.h>
#include <string.h>
#include "dpll.h"
#include "proof.h"
#include "pred.h"
#include "func.h"
#include "proof_utils.h"
static int fa[64];
static int id[64];
static int count;

static void set_init()
{
	int i;
	for(i = 0; i < 64; i++) {
		fa[i] = i;
		id[i] = 0;
	}
	count = 0;
}

/* silent version */
static int get_fa(int v)
{
	if(fa[v] == v)
		return v;
	while(fa[v] != v)
		v = fa[v];
	return v;
}

static int set_find(int idx, int idy)
{
	int fx, fy;
	fx = get_fa(idx);
	fy = get_fa(idy);
	return fx == fy;
}

/* proof version */
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

static int set_find_proof(int idx, int idy)
{
	int fx, fy;
	fprintf(pout, "(trans_eq ");
	fx = get_fa_proof(idx);
	fprintf(pout, "(sym_eq ");
	fy = get_fa_proof(idy);
	fprintf(pout, "))");
	return fx == fy;
}

static void set_union_proof(int idx, int idy, int hseq)
{
	int fx, fy;
	fprintf(pout, "let H%d := ", count++);
	fprintf(pout, "(trans_eq (trans_eq (sym_eq (");
	fx = get_fa_proof(idx);
	fprintf(pout, ")) H%d) ", hseq);
	fy = get_fa_proof(idy);
	fprintf(pout, ")");
	fa[fx] = fy;
	id[fx] = count-1;
	fprintf(pout, " in ");
}

static void set_uif_proof(int hseq,
				int idx, int idy,
				struct func *f1, struct func *f2,
				struct func_info *fi)
{
	int i, j;
	for(i = 0; i < fi->n; i++)
	{
		fprintf(pout, "(eq_ind _ (fun _x => %s", fi->name);
		for(j = 0; j < fi->n; j++)
		{
			fprintf(pout, " ");
			func_print(f1->arr[j], pout);
		}
		fprintf(pout, " = %s", fi->name);
		for(j = 0; j < fi->n; j++)
		{
			fprintf(pout, " ");
			if(j < i)
				func_print(f1->arr[j], pout);
			else if(j > i)
				func_print(f2->arr[j], pout);
			else
				fprintf(pout, "_x");
		}
		fprintf(pout, ")");
	}
	fprintf(pout, "(refl_equal _)");
	for(i = fi->n - 1; i >= 0; i--)
		fprintf(pout, " _ H%d)", hseq+i);
}

static int equal_closure()
{
	int i, j, k;
	struct func f1, f2;
	struct func_info fi1, fi2;
	int flag;
	flag = 0;
	for(i = 0; i < 64-1; i++)
	{
		func_get(&f1, &fi1, i);
		if(fi1.n == 0 || f1.type == -1)
			continue;
		for(j = i+1; j < 64; j++)
		{
			func_get(&f2, &fi2, j);
			if(f2.type == -1 || strcmp(fi1.name, fi2.name))
				continue;
			for(k = 0; k < fi1.n; k++)
				if(!set_find(f1.arr[k], f2.arr[k]))
					break;
			if(k == fi1.n && !set_find(i, j))
			{
				int lab = count;
				flag = 1;
				for(k = 0; k < fi1.n; k++)
				{
					fprintf(pout, "let H%d := ", count++);
					set_find_proof(f1.arr[k], f2.arr[k]);
					fprintf(pout, " in ");
				}
				fprintf(pout, "let H%d := ", count++);
				set_uif_proof(lab, i, j, &f1, &f2, &fi1);
				fprintf(pout, " in ");
				set_union_proof(i, j, count-1);
			}
		}
	}
	return flag;
}

void equal_proof(int seq, struct lit_set *lit, void *extra)
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
			set_union_proof(p.lv, p.rv, count-1);
		}
	}

	for(i = 0; i < n; i++)
	{
		if(vec[i] > 0)
		{
			pred_get(&p, vec[i]-1);
			do {
				if(set_find(p.lv, p.rv))
					break;
			} while(equal_closure());
			break;
		}
	}

	set_find_proof(p.lv, p.rv);
	rep_print(")", n-1);
	fprintf(pout, ".\nCheck (L%d).\n", seq);
}
