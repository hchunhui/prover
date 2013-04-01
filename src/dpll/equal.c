#include "equal.h"
#include "pred.h"

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

static void set_union(int *fa, int idx, int idy)
{
	int fx, fy;
	fx = get_fa(fa, idx);
	fy = get_fa(fa, idy);
	if(fy != fx) {
		fa[fx]=fy;
	}
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
				*penv &= ~(1 << i);
				continue;
			}
			set_union(fa, q.lv, q.rv);
		}
	}
	if(set_find(fa, p.lv, p.rv))
	{
		return 1;
	}
	return 0;
}
