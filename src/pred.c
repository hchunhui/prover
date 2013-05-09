#include <stdio.h>
#include "pred.h"
#include "func.h"

static struct pred pred_tab[64];
static char atom_name[64][16];

void pred_init()
{
	int i;
	for(i = 0; i < 64; i++)
		pred_tab[i].type = P_NULL;
}

int pred_search(int type, int lv, int rv)
{
	int i;
	for(i = 0; i < 64; i++)
		if(pred_tab[i].type == type &&
		   pred_tab[i].lv == lv &&
		   pred_tab[i].rv == rv)
			break;
	if(i < 64)
		return i;
	return -1;
}

int pred_new(int type, int lv, int rv)
{
	int id;
	if((id = pred_search(type, lv, rv)) != -1)
		return id;
	for(id = 0; id < 64; id++)
		if(pred_tab[id].type == P_NULL)
			break;
	if(id < 64)
	{
		pred_tab[id].type = type;
		pred_tab[id].lv = lv;
		pred_tab[id].rv = rv;
		return id;
	}
	return -1;
}

void pred_get(struct pred *p, int v)
{
	*p = pred_tab[v];
}

int prop_new(int i)
{
	int id;
	id = pred_new(P_ATOM, 64, i);
	if(id != -1)
		sprintf(atom_name[id], "A%d", i);
	return id;
}

void prop_print(int id, FILE *fp)
{
	char *pred;
	switch(pred_tab[id].type)
	{
	case P_ATOM:
		fprintf(fp, "%s", atom_name[id]);
		break;
	case P_EQU:
		pred = "=";
		goto comm;
	case P_LE:
		pred = "<=";
		goto comm;
	case P_LT:
		pred = "<";
		goto comm;
	case P_GT:
		pred = ">";
		goto comm;
	comm:
		fprintf(fp, "(");
		func_print(pred_tab[id].lv, fp);
		fprintf(fp, pred);
		func_print(pred_tab[id].rv, fp);
		fprintf(fp, ")");
		break;
	}
}

void prop_decl(FILE *fp)
{
	int i;
	for(i = 0; i < 64; i++)
		if(pred_tab[i].type == P_ATOM)
			break;
	if(i < 64) {
		fprintf(fp, "Variable");
		for(i = 0; i < 64; i++)
			if(pred_tab[i].type == P_ATOM)
			{
				fprintf(fp, " ");
				prop_print(i, fp);
			}
		fprintf(fp, ":Prop.\n");
	}
}
