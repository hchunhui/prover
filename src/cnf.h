#ifndef _CNF_H_
#define _CNF_H_

struct etree;
struct list;

void proof_impl(struct etree *p);
void proof_not(struct etree *p);
struct list *proof_dist(struct etree *p);

#endif /* _CNF_H_ */
