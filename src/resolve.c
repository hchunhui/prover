#include <stdio.h>
#include <stdlib.h>

int or_merge(int *vec1, int n1, int *vec2, int n2, int *rank, int *vec)
{
	int i;
	int r;
	unsigned long long cp, cn;
	cp = 0;	cn = 0;
	for(i = 0; i < n1; i++)
		if(vec1[i] > 0)
			cp |= 1ull << (vec1[i]-1);
		else
			cn |= 1ull << (-vec1[i]-1);
	for(i = 0; i < n2; i++)
		if(vec2[i] > 0)
			cp |= 1ull << (vec2[i]-1);
		else
			cn |= 1ull << (-vec2[i]-1);
	r = 0;
	for(i = 0; i < 128; i++)
		rank[i] = -1;
	for(i = 0; i < 64; cp >>=1, i++)
		if(cp & 1)
		{
			rank[i] = r;
			vec[r] = i+1;
			r++;
		}
	for(i = 0; i < 64; cn >>=1, i++)
		if(cn & 1)
		{
			rank[64+i] = r;
			vec[r] = -(i+1);
			r++;
		}
	return r;
}

void print_lit(int v)
{
	if(v > 0)
		printf("A%d", v);
	else
		printf("~A%d", -v);
}

void print_vec(int *vec, int n)
{
	int i;
	if(n == 0)
		printf("False");
	else
	{
		print_lit(vec[0]);
		for(i = 1; i < n; i++)
		{
			printf("\\/");
			print_lit(vec[i]);
		}
	}
}

void or_intro(int rank, int *vec, int n, int hi)
{
	int i;
//	printf("(* %d *)", rank);
	for(i = 0; i < rank; i++)
	{
		printf("(or_intror (");
		print_lit(vec[i]);
		printf(") ");
	}
	if(rank < n-1)
	{
		printf("(or_introl (");
		print_vec(vec+rank+1, n - rank - 1);
		printf(") H%d)", hi);
	}
	else
		printf("H%d", hi);
	for(i = 0; i < rank; i++)
		printf(")");
}

void or_make(int *vec1, int n1, int *rank, int *vec, int n)
{
	int i, j;
	for(i = 0; i < n1; i++)
	{
		if(i != n1 - 1)
			printf("(or_ind (fun (H1:");
		else
			printf("(fun (H1:");
		print_lit(vec1[i]);
		printf(") => ");
/*FIXME: -1 or not*/
		or_intro(rank[vec1[i]>0?vec1[i]-1:(63-vec1[i])], vec, n, 1);
		printf(")\n");
		if(i == n1 - 1)
		{
			for(j = 0; j < n1 - 1; j++)
				printf(")");
		}
	}
}

void or_trans(int *vec1, int n1, int *vec2, int n2)
{
	int rank[128];
	int vec[128];
	int n;
	n = or_merge(vec1, n1, vec2, n2, rank, vec);
	printf("(*");
	print_vec(vec, n);
	printf("*)\n");
	printf("(fun (H:(");
	print_vec(vec1, n1);
	printf(")\\/(");
	print_vec(vec2, n2);
	printf(")) =>\n\t");
	printf("(or_ind\n\t(");
	or_make(vec1, n1, rank, vec, n);
	printf(")\n\t (");
	or_make(vec2, n2, rank, vec, n);
	printf(") H))\n");
}

void rep_print(char *p, int count)
{
	int i;
	for(i = 0; i < count; i++)
		printf("%s", p);
}

void resolve(
	int *vec1, int n1,
	int *vec2, int n2,
	int *vec1p, int n1p,
	int *vec2p, int n2p,
	int var)
{
	int rank[128];
	int vec[128];
	int n;
	int i, j;
	int hcount = 1;
	int pl_count;
	n = or_merge(vec1p, n1p, vec2p, n2p, rank, vec);
	printf("(fun (H%d:(", hcount++);
	print_vec(vec1, n1);
	printf(")) (H%d:(", hcount++);
	print_vec(vec2, n2);
	printf(")) =>\n\t");

	for(i = 0; i < n1; i++)
	{
		if(i != n1 - 1)
			printf("(or_ind ");
		printf("(fun (H%d:", hcount++);
		print_lit(vec1[i]);
		printf(") => ");
		if(vec1[i] != var)
			or_intro(rank[vec1[i]>0?vec1[i]-1:(63-vec1[i])],
				 vec, n, hcount-1);
		else {
			pl_count = hcount-1;
			for(j = 0; j < n2; j++)
			{
				if(j != n2 - 1)
					printf("(or_ind ");
				printf("(fun (H%d:", hcount++);
				print_lit(vec2[j]);
				printf(") => ");
				if(vec2[j] != -var)
					or_intro(rank[vec2[j]>0?vec2[j]-1:(63-vec2[j])],
						 vec, n, hcount-1);
				else {
					printf("False_ind (");
					print_vec(vec, n);
					printf(") (H%d H%d)", hcount-1, pl_count);
				}
				printf(")\n");
				if(j == n2 - 1)
					rep_print(")", n2-1);
			}
			printf("H2");
		}
		printf(")\n");
		if(i == n1 - 1)
			rep_print(")", n1-1);
	}
	printf("H1");
	printf(")\n");
}
/*
int main(int argc, char *argv[])
{
	int vec1[] = {2, 8, -7};
	int vec2[] = {2, -8, -5};
	int vec1p[] = {2, -7};
	int vec2p[] = {2, -5};
	int n1, n2, n1p, n2p;
	n1 = 3;
	n2 = 3;
	n1p = 2;
	n2p = 2;
	resolve(vec1, n1,
		vec2, n2,
		vec1p, n1p,
		vec2p, n2p,
		8);
	return 0;
}
*/
int bit2vec(unsigned long long cp, unsigned long long cn, int *vec)
{
	int i, r;
	r = 0;
	for(i = 0; i < 64; cp >>=1, i++)
		if(cp & 1)
		{
			vec[r] = i+1;
			r++;
		}
	for(i = 0; i < 64; cn >>=1, i++)
		if(cn & 1)
		{
			vec[r] = -(i+1);
			r++;
		}
	return r;	
}
