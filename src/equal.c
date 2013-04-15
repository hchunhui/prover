#include "comm.h"
#include "equal.h"
#include <string.h>

static int get_fa(int *fa, int v)
{
	if(fa[v] == v)
		return v;
	else
		return  get_fa(fa, fa[v]);
}

static void set_init(int *fa)
{
	int i;
	for(i = 0; i < 64; i++) {
		fa[i] = i;
	}
}

static int set_find(int *fa, int idx, int idy)
{
	int fx = get_fa(fa, idx);
	int fy = get_fa(fa, idy);
	return fx == fy;
}

static int set_union(int *fa, int idx, int idy)
{
	int fx, fy;
	fx = get_fa(fa, idx);
	fy = get_fa(fa, idy);
	if(fy != fx) {
		fa[fx]=fy;
		return 1;
	}
	return 0;
}

static int equal_closure(int *fa)
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
				if(!set_find(fa, f1.arr[k], f2.arr[k]))
					break;
			if(k == fi1.n)
				if(set_union(fa, i, j))
					flag = 1;
		}
	}
	return flag;
}

int equal_test(LitSet *env)
{
	int i, id;
	struct pred q;
	LitSet *ls, *ls1;
	int fa[64];
	int ret;
	ret = 0;
	set_init(fa);
	ls = litset_new();
	for(i = 0; i < env->n; i++)
	{
		if(env->mem[i].neg)
			continue;
		pred_get(&q, env->mem[i].id);
		if(q.type != P_EQU)
			continue;
		set_union(fa, q.lv, q.rv);
		litset_add(ls, lit_make(1, env->mem[i].id));
	}

	for(i = 0; i < env->n; i++)
	{
		if(!env->mem[i].neg)
			continue;
		pred_get(&q, env->mem[i].id);
		if(q.type != P_EQU)
			continue;
		do {
			if(set_find(fa, q.lv, q.rv))
			{
				ls1 = litset_dup(ls);
				litset_add(ls1, lit_make(0, env->mem[i].id));
				id = gamma_add(ls1);
				gamma_add_proof(id, equal_proof, NULL);
				ret = 1;
				return ret;
				break;
			}
		} while(equal_closure(fa));
	}
	litset_del(ls);
	return ret;
}
