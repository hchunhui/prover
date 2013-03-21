#ifndef _PROOF_H_
#define _PROOF_H_

struct etree;
struct list;

void proof_impl(struct etree *p, char *name);
void proof_not1(struct etree *p, char *name);
void proof_not2(struct etree *p, char *name);
int proof_prove(struct list *g, struct etree *et, int seq);

#endif /* _PROOF_H_ */
