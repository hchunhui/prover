#include <stdio.h>
#include <string.h>
#include "etree.h"
#include "proof.h"

static void print_lit(int val, FILE *fp)
{
	if(val < 0)
		fprintf(fp, "~%s", prop_name[-val-1]);
	else
		fprintf(fp, "%s", prop_name[val-1]);
}

void etree_dump_infix(struct etree *p, FILE *fp)
{
	const char *pc1, *pc2;
	switch(p->type)
	{
	case T_OR:
		pc1 = "";
		pc2 = "\\/";
		goto comm_case;
	case T_AND:
		pc1 = "";
		pc2 = "/\\";
		goto comm_case;
	case T_IMPL:
		pc1 = "";
		pc2 = "->";
	comm_case:
		fprintf(fp, "%s(", pc1);
		etree_dump_infix(p->l, fp);
		fprintf(fp, ")%s(", pc2);
		etree_dump_infix(p->r, fp);
		fprintf(fp, ")");
		break;
	case T_PROP:
		print_lit(p->val, fp);
		break;
	case T_NOT:
		fprintf(fp, "~(");
		etree_dump_infix(p->l, fp);
		fprintf(fp, ")");
		break;
	}
}

void etree_dump_prefix(struct etree *p, FILE *fp)
{
	const char *pc;
	switch(p->type)
	{
	case T_OR:
		pc = "or";
		goto comm_case;
	case T_AND:
		pc = "and";
		goto comm_case;
	case T_IMPL:
		pc = "impl";
	comm_case:
		fprintf(fp,"(%s ", pc);
		etree_dump_prefix(p->l, fp);
		fprintf(fp," ");
		etree_dump_prefix(p->r, fp);
		fprintf(fp,")");
		break;
	case T_PROP:
		print_lit(p->val, fp);
		break;
	case T_NOT:
		fprintf(fp,"(not ");
		etree_dump_prefix(p->l, fp);
		fprintf(fp,")");
		break;
	}
}
