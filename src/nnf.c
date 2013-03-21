#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "list.h"
#include "etree.h"
#include "nnf.h"

/*
 * 第一步：消除蕴含词
 */
void simp_impl(struct etree *p)
{
	struct etree *t;
	switch(p->type)
	{
	case T_IMPL:
		t = etree_mknode(T_NOT, 0, p->l, NULL);
		p->l = t;
		p->type = T_OR;
		simp_impl(p->l);
		simp_impl(p->r);
		break;
	case T_OR:
	case T_AND:
		simp_impl(p->l);
		simp_impl(p->r);
		break;
	case T_NOT:
		simp_impl(p->l);
		break;
	}
}

/*
 * 第二步：否定词深入
 */
static void __simp_not1(struct etree *p, int not)
{
	struct etree *t;
	switch(p->type)
	{
	case T_NOT:
		__simp_not1(p->l, !not);
		break;
	case T_OR:
		if(not)
			p->type = T_AND;
		goto comm_case;
	case T_AND:
		if(not)
			p->type = T_OR;
	comm_case:
		if(not) {
			t = etree_mknode(0, 0, NULL, NULL);
			memcpy(t, p, sizeof(struct etree));
			p->type = T_NOT;
			p->l = t;
			p->r = NULL;
			p = p->l;
			t = etree_mknode(T_NOT, 0, p->l, NULL);
			p->l = t;
			t = etree_mknode(T_NOT, 0, p->r, NULL);
			p->r = t;
		}
		__simp_not1(p->l, 0);
		__simp_not1(p->r, 0);
		break;
	}
}

void simp_not1(struct etree *p)
{
	__simp_not1(p, 0);
}

static void __simp_not2(struct etree *p, int not)
{
	struct etree *t;
	switch(p->type)
	{
	case T_NOT:
		t = p->l;
		memcpy(p, t, sizeof(struct etree));
		free(t);
		__simp_not2(p, !not);
		break;
	case T_OR:
	case T_AND:
		__simp_not2(p->l, not);
		__simp_not2(p->r, not);
		break;
	case T_PROP:
		if(not)
			p->val = -p->val;
		break;
	}
}

void simp_not2(struct etree *p)
{
	__simp_not2(p, 0);
}
