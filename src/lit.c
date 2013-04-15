#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "comm.h"
#include "lit.h"

LitSet *litset_new()
{
	LitSet *ls;
	ls = malloc(sizeof(LitSet));
	assert(ls);
	ls->mem = malloc(sizeof(Lit));
	assert(ls->mem);
	ls->alloc_n = 1;
	ls->n = 0;
	return ls;
}

void litset_add(LitSet *ls, Lit l)
{
	int i, j;
	for(i = 0; i < ls->n; i++)
		if(l.neg > ls->mem[i].neg ||
		   (l.neg == ls->mem[i].neg && ls->mem[i].id >= l.id))
			break;
	if(i < ls->n && l.neg == ls->mem[i].neg && l.id == ls->mem[i].id)
		return;
	if(ls->n == ls->alloc_n)
	{
		ls->alloc_n *= 2;
		ls->mem = realloc(ls->mem, sizeof(Lit)*ls->alloc_n);
		assert(ls->mem);
	}
	for(j = ls->n-1; j >= i; j--)
		ls->mem[j+1] = ls->mem[j];
	ls->mem[i] = l;
	ls->n++;
}

LitSet *litset_dup(LitSet *ls)
{
	LitSet *ls1;
	ls1 = malloc(sizeof(LitSet));
	assert(ls1);
	ls1->n = ls->n;
	ls1->alloc_n = ls->alloc_n;
	ls1->mem = malloc(sizeof(Lit)*ls1->alloc_n);
	assert(ls1->mem);
	memcpy(ls1->mem, ls->mem, sizeof(Lit)*ls1->alloc_n);
	return ls1;
}

void litset_del(LitSet *ls)
{
	free(ls->mem);
	free(ls);
}

Lit lit_make(int neg, int id)
{
	Lit l;
	l.neg = neg;
	l.id = id;
	return l;
}


void lit_print(Lit l, FILE *fp)
{
	fprintf(fp, "%s", l.neg?"~":"");
	prop_print(l.id, fp);
}

void litset_print(LitSet *ls, int start, char *sep, FILE *fp)
{
	int i;
	if(ls->n == start)
		fprintf(fp, "False");
	else
	{
		lit_print(ls->mem[start], fp);
		for(i = start+1; i < ls->n; i++)
		{
			fprintf(fp, sep);
			lit_print(ls->mem[i], fp);
		}
	}
}
