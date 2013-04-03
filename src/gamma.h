#ifndef _GAMMA_H_
#define _GAMMA_H_

#include "dpll.h"
int gamma_search(unsigned long long cp,
		 unsigned long long cn);
int gamma_add(unsigned long long cp,
	      unsigned long long cn);
void gamma_add_proof(int id,
		     void (*proof)(int seq, struct lit_set *lit, void *extra),
		     void *extra);
void gamma_ref(int id);
int gamma_match(unsigned long long cpmask,
		unsigned long long cnmask);
void gamma_get(int id, struct lit_set *lit);
int gamma_get_num();
void gamma_proof();
void gamma_init();

#endif /* _GAMMA_H_ */
