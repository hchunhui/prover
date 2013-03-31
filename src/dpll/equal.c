#include <stdio.h>
static int fa[64+1];
static int id[64+1][64+1];
static int seq;

void new_eq(int x, int y)
{
	if(x == y)
		return;
	printf("(%d)new_eq \tx%d = x%d\n", seq++, x, y);
	id[x][y] = seq-1;
}

void refl_eq(int i)
{
	printf("(x)refl_eq \tx%d = x%d\n", i, i);
}

void sym_eq(int x, int y)
{
	if(x == y)
		return;
	printf("(%d)sym_eq  \tfrom [%d] => x%d = x%d\n",
	       seq++,
	       id[x][y], y, x);
	id[y][x] = seq-1;
}

void trans_eq(int x, int y, int z)
{
	if(x == y) {
		if(y != z)
			printf("(x)exact    \t[%d]\n", id[y][z]);
		else
			refl_eq(y);
		return;
	} else if(y == z) {
			printf("(x)exact    \t[%d]\n", id[x][y]);
			return;
	}
	printf("(%d)trans_eq\tfrom [%d][%d] => x%d, x%d\n",
	       seq++, id[x][y], id[y][z], x, z);
	id[x][z] = seq-1;
}

int get_fa(int v)
{
	if(fa[v] == v)
		return v;
	else
	{
		int t = get_fa(fa[v]);
		if(fa[v] != t)
			trans_eq(v, fa[v], t);
		return fa[v] = t;
	}
}

void set_init()
{
	int i;
	for(i = 0; i < 64+1; i++) {
		fa[i] = i;
	}
	seq = 1;
}

int set_find(int idx, int idy)
{
	if(idx == idy) {
		refl_eq(idx);
		return 1;
	}
	int fx = get_fa(idx);
	int fy = get_fa(idy);
	if(fx != idy)
		sym_eq(idy, idx);
	return fx == fy;
}

void set_union(int idx, int idy)
{
	int fx, fy;
	fx = get_fa(idx);
	fy = get_fa(idy);
	if(fy != fx) {
		if(fa[fx] != fy) {
			new_eq(idx, idy);
			sym_eq(idx, fx);
			trans_eq(fx, idx, idy);
			trans_eq(fx, idy, fy);
		}
		fa[fx]=fy;
	}
}
/*
int main(int argc, char *argv[])
{
	set_init();
	set_find(1, 1);
	set_union(1, 2);
	set_union(2, 3);
	set_find(3, 1);
	set_find(1, 3);
	set_find(1, 1);
	set_find(1, 1);
	set_union(2, 4);
	set_find(1, 4);
	return 0;
}
*/
