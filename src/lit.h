#ifndef _LIT_H_
#define _LIT_H_
#include <stdio.h>

typedef struct {unsigned int id:31; unsigned int neg:1;} Lit;
typedef struct {Lit *mem; short alloc_n; short n;} LitSet;
typedef struct {Lit *mem; short alloc_n; short n;} LitList;

LitSet *litset_new();
LitSet *litset_dup(LitSet *ls);
void litset_del(LitSet *ls);
void litset_add(LitSet *ls, Lit l);
Lit lit_make(int neg, int id);
void lit_print(Lit l, FILE *fp);
void litset_print(LitSet *ls, int start, char *sep, FILE *fp);

LitList *litlist_new();
void litlist_add(LitList *ls, Lit l);
LitList *litlist_dup(LitList *ls);
LitList *litlist_dupset(LitSet *ls);
void litlist_del(LitList *ls);
void litlist_print(LitList *ls, int start, char *sep, FILE *fp);
#endif /* _LIT_H_ */
