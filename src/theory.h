#ifndef _THEORY_H_
#define _THEORY_H_
#include <stdlib.h>
struct simplex_ctx;
struct equal_ctx;

struct theory_tree
{
	struct simplex_ctx *actx;
	struct equal_ctx *ectx;
	struct theory_tree *lt, *eq, *gt;
};

static inline struct theory_tree
*theory_tree_new(struct simplex_ctx *actx, struct equal_ctx *ectx)
{
	struct theory_tree *tt;
	tt = malloc(sizeof(struct theory_tree));
	tt->actx = actx;
	tt->ectx = ectx;
	tt->lt = tt->eq = tt->gt = NULL;
	return tt;
}

#endif /* _THEORY_H_ */
