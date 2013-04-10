bin_PROGRAMS = prover.x
prover_front = expr.tab.y expr.lex.l
prover_base = main.c etree.c nnf.c cnf.c gamma.c prove.c pred.c func.c equal.c arith.c
prover_proof = nnf_proof.c cnf_proof.c prove_proof.c equal_proof.c
prover_x_SOURCES = $(prover_front) $(prover_base) $(prover_proof)
AM_YFLAGS=-d
#AM_CPPFLAGS=-I$(top_srcdir)/include
CLEANFILES=expr.tab.h expr.tab.c expr.lex.c
