#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "list.h"
#include "etree.h"
#include "proof.h"

/*
 * 第一步：消除蕴含词
 */
static void __proof_imp(struct etree *p)
{
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
}

/*
 * 第二步：否定词深入
 */
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

void proof_not1(struct etree *p)
{
	printf("Definition insert_not1:=(");
	__proof_not1(p, 0);
	printf(").\nCheck (insert_not1).\n");
}

void proof_not2(struct etree *p)
{
	printf("Definition insert_not2:=(");
	__proof_not2(p, 0);
	printf(").\nCheck (insert_not2).\n");
}
