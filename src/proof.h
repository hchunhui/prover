#ifndef _PROOF_H_
#define _PROOF_H_
#include <stdio.h>
struct etree;
struct list;

void proof_impl(struct etree *p, char *name);
void proof_not1(struct etree *p, char *name);
void proof_not2(struct etree *p, char *name);

extern FILE *pout;
#endif /* _PROOF_H_ */
