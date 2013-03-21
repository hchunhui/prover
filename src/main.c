#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "etree.h"
#include "nnf.h"
#include "proof.h"

struct etree *parse();
char prop_name[64][16];

int main(int argc, char *argv[])
{
	int i;
	int seq;
	struct etree *et;
	for(i = 0; i < 64; i++)
		sprintf(prop_name[i], "A%d", i+1);

	printf("Section prove.\n");
	for(i = 0; i < 64; i++)
		printf("Variable %s:Prop.\n", prop_name[i]);
	printf("Section prove0.\n");

	/* 输入a */
	et = parse();
	if(et == NULL)
		exit(1);

	/* ~a */
	et = etree_mknode(T_NOT, 0, et, NULL);
	etree_dump_prefix(et, stderr);
	fprintf(stderr, "\n");

	printf("Hypothesis L0: ");
	etree_dump_infix(et, stdout);
	printf(".\n");

	/* 消蕴含 */
	proof_impl(et);
	simp_impl(et);
	etree_dump_prefix(et, stderr);
	fprintf(stderr, "\n");

	/* 否定范式 */
	proof_not1(et);
	simp_not1(et, 0);
	proof_not2(et);
	printf("Definition L0':= "
	       "(iff_imp _ _ "
	       "(iff_trans _ _ _ elim_impl (iff_trans _ _ _ insert_not1 insert_not2)) "
	       "L0).\n");
	simp_not2(et, 0);

	etree_dump_prefix(et, stderr);
	fprintf(stderr, "\n");

	/* 归结 */
	seq = prove(et);
	printf("End prove0.\n");

	if(seq)
		printf("Definition Lem:=(NNPP _ L%d).\n", seq);
	printf("End prove.\n");
	if(seq)
		printf("Check Lem.\n");
	return 0;
}
