Require Import CAS.basic. 
Require Import CAS.properties. 
Require Import CAS.structures.


Lemma brel_reduce_reflexive (S :Type) (eq : brel S) (r : unary_op S) : brel_reflexive S eq -> brel_reflexive S (brel_reduce r eq).
Proof. intros H s. compute. apply (H (r s)). Qed.

Lemma brel_reduce_symmetric (S :Type) (eq : brel S) (r : unary_op S) : brel_symmetric S eq -> brel_symmetric S (brel_reduce r eq).
Proof. intros H1 s1 s2. compute. intro H2. apply (H1 (r s1) (r s2)); auto. Qed.

Lemma brel_reduce_transitive (S :Type) (eq : brel S) (r : unary_op S) : brel_transitive S eq -> brel_transitive S (brel_reduce r eq).
Proof. intros H1 s1 s2 s3. compute. intros H2 H3. apply (H1 (r s1) (r s2) (r s3)); auto. Qed.

Definition red_eqv_proofs (S : Type) (eq : brel S) (r : unary_op S) : eqv_proofs S eq -> eqv_proofs S (brel_reduce r eq)
:= λ eqv,
{|
  eqv_reflexive      := brel_reduce_reflexive S eq r (eqv_reflexive S eq eqv) 
; eqv_transitive     := brel_reduce_transitive S eq r (eqv_transitive S eq eqv) 
; eqv_symmetric      := brel_reduce_symmetric S eq r (eqv_symmetric S eq eqv) 
; eqv_witness        := r (eqv_witness S eq eqv) 
|}.

