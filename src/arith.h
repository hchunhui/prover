#ifndef _ARITH_H_
#define _ARITH_H_
#include "comm.h"
#include "theory.h"
#include "equal.h"

struct simplex_ctx *simplex_new_ctx(int n, int m);
void simplex_del_ctx(struct simplex_ctx *ctx);
struct simplex_ctx *simplex_dup_ctx(struct simplex_ctx *ctx, int flag);
int simplex_solve(struct simplex_ctx *ctx);
struct simplex_ctx *arith_build_env(LitSet *env);
int arith_test(struct theory_tree *tt);

#endif /* _ARITH_H_ */
