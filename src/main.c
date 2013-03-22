#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "etree.h"
#include "nnf.h"
#include "proof.h"

struct etree *parse();
int prove_naive(struct etree *et);

/* global variable */
char prop_name[64][16];
FILE *pout;

int main(int argc, char *argv[])
{
	int i;
	int seq;
	struct etree *et;
	for(i = 0; i < 64; i++)
		sprintf(prop_name[i], "A%d", i+1);
	pout = stdout;

	fprintf(pout, "Section prove.\n");
	for(i = 0; i < 64; i++)
		fprintf(pout, "Variable %s:Prop.\n", prop_name[i]);
	fprintf(pout, "Section prove0.\n");

	/* 输入a */
	et = parse();
	if(et == NULL)
		exit(1);

	/* ~a */
	et = etree_mknode(T_NOT, 0, et, NULL);
	etree_dump_prefix(et, stderr);
	fprintf(stderr, "\n");

	fprintf(pout, "Hypothesis L0: ");
	etree_dump_infix(et, pout);
	fprintf(pout, ".\n");

	/* 消蕴含 */
	proof_impl(et, "simp_impl");
	simp_impl(et);
	etree_dump_prefix(et, stderr);
	fprintf(stderr, "\n");

	/* 否定范式 */
	proof_not1(et, "simp_not1");
	simp_not1(et);
	proof_not2(et, "simp_not2");
	simp_not2(et);
	fprintf(pout, "Definition L0':= "
		"(iff_imp _ _ "
		"(iff_trans _ _ _ simp_impl (iff_trans _ _ _ simp_not1 simp_not2)) "
		"L0).\n");

	etree_dump_prefix(et, stderr);
	fprintf(stderr, "\n");

	/* 归结 */
	seq = prove_naive(et);
	fprintf(pout, "End prove0.\n");

	if(seq)
		fprintf(pout, "Definition Lem:=(NNPP _ L%d).\n", seq);
	fprintf(pout, "End prove.\n");
	if(seq)
		fprintf(pout, "Check Lem.\n");
	return 0;
}
