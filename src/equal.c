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

int equal_test(unsigned long long *penv, int v)
{
	int i;
	struct pred p, q;
	unsigned long long env;
	int fa[64];
	env = *penv;
	pred_get(&p, v);
	if(p.type != P_EQU)
		return 0;
	set_init(fa);
	for(i = 0; i < 64; i++, env >>= 1)
	{
		if(env & 1)
		{
			pred_get(&q, i);
			if(q.type != P_EQU) {
				*penv &= ~(1ull << i);
				continue;
			}
			set_union(fa, q.lv, q.rv);
		}
	}

	do {
		if(set_find(fa, p.lv, p.rv))
			return 1;
	} while(equal_closure(fa));
	return 0;
}
