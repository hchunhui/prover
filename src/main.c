#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "list.h"
#include "etree.h"
#include "cnf.h"

struct etree *parse();
extern char prop_name[][16];

int main(int argc, char *argv[])
{
	int i;
	int seq;
	struct etree *et;
	struct list *clauses = NULL;

	for(i = 0; i < 64; i++)
	{
		sprintf(prop_name[i], "A%d", i+1);
	}

	printf("Section prove.\n");
	for(i = 0; i < 64; i++)
	{
		printf("Variable %s:Prop.\n", prop_name[i]);
	}
	printf("Section prove0.\n");

	et = parse();
	if(et == NULL)
		exit(1);
	et = etree_mknode(T_NOT, 0, et, NULL);
	etree_dump_prefix(et, stderr);
	fprintf(stderr, "\n");
	printf("Hypothesis L0: ");
	etree_dump_infix(et, stdout);
	printf(".\n");
	proof_impl(et);
	etree_dump_prefix(et, stderr);
	fprintf(stderr, "\n");
	proof_not(et);
	etree_dump_prefix(et, stderr);
	fprintf(stderr, "\n");
	clauses = proof_dist(et);
	seq = prove(clauses);
	printf("End prove0.\n");
	if(seq)
		printf("Definition Lem:=(NNPP _ L%d).\n", seq);
	printf("End prove.\n");
	if(seq)
		printf("Check Lem.\n");
	return 0;
}
