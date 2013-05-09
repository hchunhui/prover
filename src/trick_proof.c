#include <stdio.h>
#include <stdlib.h>
#include "comm.h"
#include "proof.h"
#include "dpll.h"
#include "theory.h"

static int tid;

static void emit_tactic()
{
	fprintf(pout,
		"clear L0.\n"
		"congruence || omega ||"
		"(intros;subst;simpl in *;omega).\nQed.\n");
}

static void emit_tri(int seq, int ids[], int hlen, int tf)
{
	int i, j;
	fprintf(pout, "clear L0.\n");
	if(tf)
		fprintf(pout, "intros.\napply NNPP;intro.\n");
	else
		fprintf(pout, "unfold not.\nintros.\n");
	fprintf(pout, "exact (ar_tri _ _");
	for(i = 0; i < 3; i++)
	{
		fprintf(pout, " (trick_%d_%d", seq, ids[i]);
		for(j = 0; j < hlen; j++)
		{
			if(j == 0)
				fprintf(pout, " H");
			else
				fprintf(pout, " H%d", j-1);
		}
		fprintf(pout, ")");
	}
	fprintf(pout, ").\nQed.\n");
}

static int emit_tt(int seq, struct theory_tree *tt)
{
	int myid = tid++;
	int ids[3];
	if(tt->lt && tt->eq && tt->gt)
	{
		ids[0] = emit_tt(seq, tt->lt);
		ids[1] = emit_tt(seq, tt->eq);
		ids[2] = emit_tt(seq, tt->gt);
	}
	tt->env->mem[tt->env->n-1].neg = !tt->env->mem[tt->env->n-1].neg;
	fprintf(pout, "Lemma trick_%d_%d:", seq, myid);
	litlist_print(tt->env, 0, "->", pout);
	fprintf(pout, ".\n");
	if(tt->lt && tt->eq && tt->gt)
		emit_tri(seq, ids, tt->env->n, !tt->env->mem[tt->env->n-1].neg);
	else
		emit_tactic();
	return myid;
}

static void trick_emit(int seq, struct theory_tree *tt)
{
	int ids[3];
	fprintf(pout, "\n(* tricks for L%d *)\n", seq);
	if(tt->lt && tt->eq && tt->gt)
	{
		ids[0] = emit_tt(seq, tt->lt);
		ids[1] = emit_tt(seq, tt->eq);
		ids[2] = emit_tt(seq, tt->gt);
	}
	tt->env->mem[tt->env->n-1].neg = !tt->env->mem[tt->env->n-1].neg;
	fprintf(pout, "Lemma trick_%d:", seq);
	litlist_print(tt->env, 0, "->", pout);
	fprintf(pout, ".\n");
	if(tt->lt && tt->eq && tt->gt)
		emit_tri(seq, ids, tt->env->n, !tt->env->mem[tt->env->n-1].neg);
	else
		emit_tactic();
}

void trick_proof(int seq, LitSet *lit, void *extra)
{
	struct theory_tree *tt;
	tt = extra;
	tid = 0;

	trick_emit(seq, tt);

	fprintf(pout, "Lemma trick_%d_tr:(", seq);
	litlist_print(tt->env, 0, "->", pout);
	fprintf(pout, ")->");
	litset_print(lit, 0, "\\/", pout);
	fprintf(pout,".\nclear L0.\n(apply NNPP;tauto) || tauto.\nQed.\n");

	fprintf(pout, "Definition L%d:=trick_%d_tr trick_%d.\n", seq, seq, seq);
}
