#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "etree.h"
#include "nnf.h"
#include "proof.h"
#include "pred.h"
#include "func.h"
#include "dpll/gamma.h"

void pred_init();
void func_init();
struct etree *parse();
int prove_naive(struct etree *et);
int prove_dpll(struct etree *et);

/* global variable */
FILE *pout;

int main(int argc, char *argv[])
{
	int seq;
	struct etree *et;
	pout = stdout;
	func_init();
	pred_init();
	gamma_init();

	/* 输入a */
	et = parse();
	if(et == NULL)
		exit(1);

	fprintf(pout, "Section prove.\n");
	func_decl(pout);
	prop_decl(pout);
	fprintf(pout, "Section prove0.\n");

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
	if(seq = prove_dpll(et))
		gamma_proof();
	fprintf(pout, "End prove0.\n");

	if(seq)
		fprintf(pout, "Definition Lem:=(NNPP _ L%d).\n", seq);
	fprintf(pout, "End prove.\n");
	if(seq)
		fprintf(pout, "Check Lem.\n");
	return 0;
}
