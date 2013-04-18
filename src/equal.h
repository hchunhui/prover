#ifndef _EQUAL_H_
#define _EQUAL_H_
#include "comm.h"
#include "arith.h"
struct equal_ctx;
struct simplex_ctx;

struct equal_ctx *equal_new_ctx();
struct equal_ctx *equal_dup_ctx(struct equal_ctx *ctx);
void equal_del_ctx(struct equal_ctx *ctx);
int equal_get_father(struct equal_ctx *ctx, int v);
int equal_query_eq(struct equal_ctx *ctx, int idx, int idy);
int equal_add_eq(struct equal_ctx *ctx, int idx, int idy);
int equal_closure(struct equal_ctx *ctx);
int equal_test(struct equal_ctx *ctx, struct simplex_ctx *sctx);
struct equal_ctx *equal_build_env(LitSet *env);

void equal_proof(int seq, LitSet *ls, void *extra);

#endif /* _EQUAL_H_ */
