#ifndef _NNF_H_
#define _NNF_H_

struct etree;
struct list;

void simp_impl(struct etree *p);
void simp_not1(struct etree *p, int not);
void simp_not2(struct etree *p, int not);

#endif /* _NNF_H_ */
