#ifndef _PRED_H_
#define _PRED_H_
#include <stdio.h>

struct pred
{
	int type;
	int lv, rv;
};

enum {
	P_NULL,
	P_ATOM,
	P_EQU,
	P_LE,
	P_LT,
	P_GT,
};

int prop_new(int i);
int pred_new(int type, int lv, int rv);
void prop_print(int id, FILE *fp);
void prop_decl(FILE *fp);
void pred_get(struct pred *p, int v);
void pred_init();
#endif /* _PRED_H_ */
