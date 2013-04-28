#include <stdio.h>
#include <stdlib.h>
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
}

void func_print(int id, FILE *fp)
{
	int fid;
	fid = func_tab[id].type;
	fprintf(fp,"(");
	if(func_info_tab[fid].name[0] == '+')
		fprintf(fp, "Zplus");
	else if(func_info_tab[fid].name[0] == '.')
		fprintf(fp, "Zmult");
	else if(func_info_tab[fid].name[0] != '@')
		fprintf(fp, "%s", func_info_tab[fid].name);
	else
		fprintf(fp, "%s", func_info_tab[fid].name+1);
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

void func_print_pure(int id, FILE *fp)
{
	int fid;
	fid = func_tab[id].type;
	if(func_info_tab[fid].name[0] == '+')
		fprintf(fp, "p");
	else if(func_info_tab[fid].name[0] == '.')
		fprintf(fp, "m");
	else if(func_info_tab[fid].name[0] != '@')
		fprintf(fp, "_%s", func_info_tab[fid].name);
	else
		fprintf(fp, "_%s", func_info_tab[fid].name+1);
	switch(func_info_tab[fid].n)
	{
	case 0:
		break;
	case 1:
		func_print_pure(func_tab[id].arr[0], fp);
		break;
	case 2:
		func_print_pure(func_tab[id].arr[0], fp);
		func_print_pure(func_tab[id].arr[1], fp);
		break;
	}
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

int func_info_search(char *name, int n)
{
	int i;
	for(i = 0; i < 64; i++)
		if(strcmp(func_info_tab[i].name, name) == 0)
		{
			if(n != func_info_tab[i].n)
				exit(1);
			break;
		}
	if(i < 64)
		return i;
	return -1;

}

int func_info_new(char *name, int n)
{
	int id;
	if((id = func_info_search(name, n)) != -1)
		return id;
	for(id = 0; id < 64; id++)
		if(func_info_tab[id].name[0] == 0)
			break;
	if(id < 64)
	{
		strcpy(func_info_tab[id].name, name);
		func_info_tab[id].n = n;
		return id;
	}
	return -1;
}


void func_decl(FILE *fp)
{
	int i, j;
	for(i = 0; i < 64; i++)
	{
		if(func_info_tab[i].name[0] &&
		   func_info_tab[i].name[0] != '@' &&
		   func_info_tab[i].name[0] != '+' &&
		   func_info_tab[i].name[0] != '.')
		{
			fprintf(fp, "Variable %s:Z", func_info_tab[i].name);
			for(j = 0; j < func_info_tab[i].n;j++)
				fprintf(fp, "->Z");
			fprintf(fp, ".\n");
		}
	}
}

void func_get(struct func *f, struct func_info *fi, int v)
{
	*f = func_tab[v];
	if(func_tab[v].type != -1)
		*fi = func_info_tab[func_tab[v].type];
}
