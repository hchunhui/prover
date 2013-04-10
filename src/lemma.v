Require Import Classical.
Require Import ZArith.
Open Scope Z_scope.

Lemma imp_or: forall P Q:Prop, (P->Q)<->(~P\/Q).
unfold iff.
split.
apply NNPP.
tauto.
tauto.
Qed.

Lemma nor: forall P Q:Prop, P\/Q <-> ~(~P/\~Q).
unfold iff.
split.
tauto.
apply NNPP.
tauto.
Qed.

Lemma nand: forall P Q:Prop, P/\Q <-> ~(~P\/~Q).
unfold iff.
split.
tauto.
apply NNPP.
tauto.
Qed.

Lemma np: forall P:Prop, ~~P<->P.
split.
exact (NNPP P).
tauto.
Qed.

Lemma iff_p: forall P:Prop, P<->P.
tauto.
Qed.

Lemma iff_trans: forall P Q R:Prop, (P<->Q)->(Q<->R)->(P<->R).
tauto.
Qed.

Lemma iff_imp: forall P Q:Prop, (P<->Q)->(P->Q).
tauto.
Qed.

Lemma L_imp: forall A B C D:Prop, (A<->B)->(C<->D)->((A->C)<->(B->D)).
intros A B C D.
unfold iff.
tauto.
Qed.

Lemma L_and: forall A B C D:Prop, (A<->B)->(C<->D)->((A/\C)<->(B/\D)).
intros A B C D.
tauto.
Qed.

Lemma L_or: forall A B C D:Prop, (A<->B)->(C<->D)->((A\/C)<->(B\/D)).
intros A B C D.
tauto.
Qed.

Lemma L_not: forall A B:Prop, (A<->B)->((~A)<->(~B)).
intros A B.
tauto.
Qed.

Lemma horn: forall P Q:Prop, (P->Q)->(~P\/Q).
intros.
apply NNPP.
tauto.
Qed.
