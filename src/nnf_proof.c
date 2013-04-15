#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "etree.h"
#include "proof.h"
#include "pred.h"

static void print_iffp(Lit val)
{
	fprintf(pout, "(iff_p ");
	prop_print(val.id, pout);
	fprintf(pout, ")");
}

/*
 * 第一步：消除蕴含词
 */
static void __proof_imp(struct etree *p)
{
	switch(p->type)
	{
	case T_IMPL:
		fprintf(pout, "(iff_trans _ _ _ (L_imp _ _ _ _ (");
		__proof_imp(p->l);
		fprintf(pout, ") (");
		__proof_imp(p->r);
		fprintf(pout, ")) (imp_or _ _))");
		break;
	case T_AND:
		fprintf(pout, "(L_and _ _ _ _ (");
		__proof_imp(p->l);
		fprintf(pout, ") (");
		__proof_imp(p->r);
		fprintf(pout, "))");
		break;
	case T_OR:
		fprintf(pout, "(L_or _ _ _ _ (");
		__proof_imp(p->l);
		fprintf(pout, ") (");
		__proof_imp(p->r);
		fprintf(pout, "))");
		break;
	case T_NOT:
		fprintf(pout, "(L_not _ _ (");
		__proof_imp(p->l);
		fprintf(pout, "))");
		break;
	case T_PROP:
		print_iffp(p->val);
		break;
	}
}

void proof_impl(struct etree *p, char *name)
{
	fprintf(pout, "Definition %s:=(", name);
	__proof_imp(p);
	fprintf(pout, ").\nCheck (%s).\n", name);
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
		fprintf(pout, "(L_not _ _ (");
		__proof_not1(p->l, !not);
		fprintf(pout, "))");
		break;
	case T_OR:
		pc1 = "or";
		goto comm_case;
	case T_AND:
		pc1 = "and";
	comm_case:
		if(not) {
			fprintf(pout, "(iff_trans _ _ _ (L_%s _ _ _ _ (", pc1);
			__proof_not1(p->l, not);
			fprintf(pout, ") (");
			__proof_not1(p->r, not);
			fprintf(pout, ")) (n%s _ _))", pc1);
		} else {
			fprintf(pout, "(L_%s _ _ _ _ (", pc1);
			__proof_not1(p->l, not);
			fprintf(pout, ") (");
			__proof_not1(p->r, not);
			fprintf(pout, "))");
		}
		break;
	case T_PROP:
		print_iffp(p->val);
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
			fprintf(pout, "(iff_trans _ _ _ (L_not _ _ (L_not _ _ (");
			__proof_not2(p->l, 0);
			fprintf(pout, "))) (np _))");
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
			fprintf(pout, "(L_not _ _ (");
		}
		fprintf(pout, "(L_%s _ _ _ _ (", pc1);
		__proof_not2(p->l, 0);
		fprintf(pout, ") (");
		__proof_not2(p->r, 0);
		fprintf(pout, "))");
		if(not) {
			fprintf(pout, "))");
		}
		break;
	case T_PROP:
		if(not) {
			fprintf(pout, "(L_not _ _ (");
		}
		print_iffp(p->val);
		if(not) {
			fprintf(pout, "))");
		}
		break;
	}
}

void proof_not1(struct etree *p, char *name)
{
	fprintf(pout, "Definition %s:=(", name);
	__proof_not1(p, 0);
	fprintf(pout, ").\nCheck (%s).\n", name);
}

void proof_not2(struct etree *p, char *name)
{
	fprintf(pout, "Definition %s:=(", name);
	__proof_not2(p, 0);
	fprintf(pout, ").\nCheck (%s).\n", name);
}
