#include <stdio.h>
#include <string.h>
#include "func.h"

static struct func func_tab[64];
static struct func_info func_info_tab[64];

void func_init()
{
	int i;
	for(i = 0; i < 64; i++)
		func_tab[i].type = -1;
	for(i = 0; i < 64; i++)
	{
		func_info_tab[i].name[0] = 0;
		func_info_tab[i].n = 0;
	}
	strcpy(func_info_tab[0].name, "c0");
	func_info_tab[0].n = 0;
	strcpy(func_info_tab[1].name, "c1");
	func_info_tab[1].n = 0;
	strcpy(func_info_tab[2].name, "c2");
	func_info_tab[2].n = 0;
	strcpy(func_info_tab[3].name, "c3");
	func_info_tab[3].n = 0;

	strcpy(func_info_tab[4].name, "f0");
	func_info_tab[4].n = 1;
	strcpy(func_info_tab[5].name, "f1");
	func_info_tab[5].n = 1;
	strcpy(func_info_tab[6].name, "f2");
	func_info_tab[6].n = 1;
	strcpy(func_info_tab[7].name, "f3");
	func_info_tab[7].n = 1;

	strcpy(func_info_tab[8].name, "g0");
	func_info_tab[8].n = 2;
	strcpy(func_info_tab[9].name, "g1");
	func_info_tab[9].n = 2;
	strcpy(func_info_tab[10].name, "g2");
	func_info_tab[10].n = 2;
	strcpy(func_info_tab[11].name, "g3");
	func_info_tab[11].n = 2;
}

void func_print(int id, FILE *fp)
{
	int fid;
	fid = func_tab[id].type;
	fprintf(fp,"(");
	fprintf(fp, "%s", func_info_tab[fid].name);
	switch(func_info_tab[fid].n)
	{
	case 0:
		break;
	case 1:
		fprintf(fp, " ");
		func_print(func_tab[id].arr[0], fp);
		break;
	case 2:
		fprintf(fp," ");
		func_print(func_tab[id].arr[0], fp);
		fprintf(fp, " ");
		func_print(func_tab[id].arr[1], fp);
		break;
	}
	fprintf(fp, ")");
}

int func_search(int type, int arg1, int arg2)
{
	int i;
	for(i = 0; i < 64; i++)
		if(func_tab[i].type == type &&
		   func_tab[i].arr[0] == arg1 &&
		   func_tab[i].arr[1] == arg2)
			break;
	if(i < 64)
		return i;
	return -1;
}

int func_new(int type, int arg1, int arg2)
{
	int id;
	if((id = func_search(type, arg1, arg2)) != -1)
		return id;
	for(id = 0; id < 64; id++)
		if(func_tab[id].type == -1)
			break;
	if(id < 64)
	{
		func_tab[id].type = type;
		func_tab[id].arr[0] = arg1;
		func_tab[id].arr[1] = arg2;
		return id;
	}
	return -1;
}


void func_decl(FILE *fp)
{
	int i, j;
	for(i = 0; i < 64; i++)
	{
		if(func_info_tab[i].name[0])
		{
			fprintf(fp, "Variable %s:Set", func_info_tab[i].name);
			for(j = 0; j < func_info_tab[i].n;j++)
				fprintf(fp, "->Set");
			fprintf(fp, ".\n");
		}
	}
}
