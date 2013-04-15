#ifndef _ETREE_H_
#define _ETREE_H_
#include <stdio.h>
#include <stdlib.h>
#include "lit.h"

struct etree
{
	int type;
	Lit val;
	struct etree *l, *r;
};

enum {
	T_NOT,
	T_AND,
	T_OR,
	T_IMPL,
	T_PROP,
};

static struct etree *etree_mknode
(int type,
 Lit val,
 struct etree *l,
 struct etree *r)
{
	struct etree *p;
	p = malloc(sizeof(struct etree));
	p->type = type;
	p->val = val;
	p->l = l;
	p->r = r;
	return p;
}

static void etree_destroy(struct etree *p)
{
	if(p->l)
		etree_destroy(p->l);
	if(p->r)
		etree_destroy(p->r);
	free(p);
}

void etree_dump_infix(struct etree *p, FILE *fp);
void etree_dump_prefix(struct etree *p, FILE *fp);
#endif /* _ETREE_H_ */
