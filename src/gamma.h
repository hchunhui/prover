#ifndef _GAMMA_H_
#define _GAMMA_H_

int gamma_search(LitSet *ls);
int gamma_add(LitSet *ls);
void gamma_add_proof(int id,
		     void (*proof)(int seq, LitSet *lit, void *extra),
		     void *extra);
void gamma_ref(int id);
int gamma_match(LitSet *ls);
LitSet *gamma_get(int id);
int gamma_get_num();
void gamma_proof();
void gamma_init();

#endif /* _GAMMA_H_ */
