#ifndef _PRED_H_
#define _PRED_H_

struct pred;
enum {
	P_NULL,
	P_ATOM,
	P_EQU,
};

int prop_new(int i);
int pred_new(int type, int lv, int rv);
void prop_print(int id, FILE *fp);
void prop_decl(FILE *fp);
#endif /* _PRED_H_ */
