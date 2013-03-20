#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "list.h"
#include "etree.h"
#include "nnf.h"

/*
 * 第一步：消除蕴含词
 */
static void simp_impl(struct etree *p)
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

static void __proof_imp(struct etree *p)
{

	struct etree *t;
	switch(p->type)
	{
	case T_IMPL:
		printf("(iff_trans _ _ _ (L_imp _ _ _ _ (");
		__proof_imp(p->l);
		printf(") (");
		__proof_imp(p->r);
		printf(")) (imp_or _ _))");
		break;
	case T_AND:
		printf("(L_and _ _ _ _ (");
		__proof_imp(p->l);
		printf(") (");
		__proof_imp(p->r);
		printf("))");
		break;
	case T_OR:
		printf("(L_or _ _ _ _ (");
		__proof_imp(p->l);
		printf(") (");
		__proof_imp(p->r);
		printf("))");
		break;
	case T_NOT:
		printf("(L_not _ _ (");
		__proof_imp(p->l);
		printf("))");
		break;
	case T_PROP:
		printf("(iff_p A%d)", p->val);
		break;
	}
}

void proof_impl(struct etree *p)
{
	printf("Definition elim_impl:=(");
	__proof_imp(p);
	printf(").\nCheck (elim_impl).\n");
	simp_impl(p);
}

/*
 * 第二步：否定词深入
 */
static void simp_not1(struct etree *p, int not)
{
	struct etree *t;
	switch(p->type)
	{
	case T_NOT:
		simp_not1(p->l, !not);
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
		simp_not1(p->l, 0);
		simp_not1(p->r, 0);
		break;
	}
}

static void simp_not2(struct etree *p, int not)
{
	struct etree *t;
	switch(p->type)
	{
	case T_NOT:
		t = p->l;
		memcpy(p, t, sizeof(struct etree));
		free(t);
		simp_not2(p, !not);
		break;
	case T_OR:
	case T_AND:
		simp_not2(p->l, not);
		simp_not2(p->r, not);
		break;
	case T_PROP:
		if(not)
			p->val = -p->val;
		break;
	}
}

static void __proof_not1(struct etree *p, int not)
{
	const char *pc1;
	switch(p->type)
	{
	case T_NOT:
		printf("(L_not _ _ (");
		__proof_not1(p->l, !not);
		printf("))");
		break;
	case T_OR:
		pc1 = "or";
		goto comm_case;
	case T_AND:
		pc1 = "and";
	comm_case:
		if(not) {
			printf("(iff_trans _ _ _ (L_%s _ _ _ _ (", pc1);
			__proof_not1(p->l, not);
			printf(") (");
			__proof_not1(p->r, not);
			printf(")) (n%s _ _))", pc1);
		} else {
			printf("(L_%s _ _ _ _ (", pc1);
			__proof_not1(p->l, not);
			printf(") (");
			__proof_not1(p->r, not);
			printf("))");
		}
		break;
	case T_PROP:
		printf("(iff_p A%d)", p->val);
		break;
	}
}

static void __proof_not2(struct etree *p, int not)
{
	const char *pc1;
	switch(p->type)
	{
	case T_NOT:
		if(not) {
			printf("(iff_trans _ _ _ (L_not _ _ (L_not _ _ (");
			__proof_not2(p->l, 0);
			printf("))) (np _))");
		} else {
			__proof_not2(p->l, 1);
		}
		break;
	case T_OR:
		pc1 = "or";
		goto comm_case;
	case T_AND:
		pc1 = "and";
	comm_case:
		if(not) {
			printf("(L_not _ _ (");
		}
		printf("(L_%s _ _ _ _ (", pc1);
		__proof_not2(p->l, 0);
		printf(") (");
		__proof_not2(p->r, 0);
		printf("))");
		if(not) {
			printf("))");
		}
		break;
	case T_PROP:
		if(not) {
			printf("(L_not _ _ (");
		}
		printf("(iff_p A%d)", p->val);
		if(not) {
			printf("))");
		}
		break;
	}
}

void proof_not(struct etree *p)
{
	printf("Definition insert_not1:=(");
	__proof_not1(p, 0);
	printf(").\nCheck (insert_not1).\n");
	simp_not1(p, 0);
	printf("Definition insert_not2:=(");
	__proof_not2(p, 0);
	printf(").\nCheck (insert_not2).\n");
	printf("Definition L0':= "
	       "(iff_imp _ _ "
	       "(iff_trans _ _ _ elim_impl (iff_trans _ _ _ insert_not1 insert_not2)) "
	       "L0).\n");
	simp_not2(p, 0);
}
