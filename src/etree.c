#include <stdio.h>
#include <string.h>
#include "etree.h"

void dump_prop(struct etree *p)
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
		printf("%s(", pc1);
		dump_prop(p->l);
		printf(")%s(", pc2);
		dump_prop(p->r);
		printf(")");
		break;
	case T_PROP:
		if(p->val < 0)
			printf("~A%d", -p->val);
		else
			printf("A%d", p->val);
		break;
	case T_NOT:
		printf("~(");
		dump_prop(p->l);
		printf(")");
		break;
	}
}

void dump(struct etree *p)
{
	switch(p->type)
	{
	case T_OR:
		fprintf(stderr,"(or ");
		dump(p->l);
		fprintf(stderr," ");
		dump(p->r);
		fprintf(stderr,")");
		break;
	case T_AND:
		fprintf(stderr,"(and ");
		dump(p->l);
		fprintf(stderr," ");
		dump(p->r);
		fprintf(stderr,")");
		break;
	case T_IMPL:
		fprintf(stderr,"(impl ");
		dump(p->l);
		fprintf(stderr," ");
		dump(p->r);
		fprintf(stderr,")");
		break;
	case T_PROP:
		if(p->val < 0)
			fprintf(stderr, "~A%d", -p->val);
		else
			fprintf(stderr, "A%d", p->val);
		break;
	case T_NOT:
		fprintf(stderr,"(not ");
		dump(p->l);
		fprintf(stderr,")");
		break;
	}
}
