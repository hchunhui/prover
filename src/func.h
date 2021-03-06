#ifndef _FUNC_H_
#define _FUNC_H_
#include <stdio.h>

struct func
{
	int type;
	int arr[4];
};

struct func_info
{
	char name[16];
	int n;
};

void func_print(int id, FILE *fp);
void func_print_pure(int id, FILE *fp);
int func_search(int type, int arg1, int arg2);
int func_new(int type, int arg1, int arg2);
void func_decl(FILE *fp);
void func_get(struct func *f, struct func_info *fi, int v);
void func_init();
int func_info_new(char *name, int n);
int func_info_search(char *name, int n);
#endif /* _FUNC_H_ */
