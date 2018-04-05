Require Export Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.   
Require Import CAS.basic. 
Require Import CAS.properties. 


Lemma bop_full_reduce_congruence (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
  uop_congruence S eqS r ->
  bop_congruence S eqS bS -> bop_congruence S eqS (bop_full_reduce r bS). 
Proof.  intros H C a b c d. compute. intros E1 E2. apply H. apply C. apply H in E1. exact E1. apply H in E2. exact E2. Qed. 

Lemma bop_full_reduce_congruence_v2 (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
  uop_congruence S eqS r ->
  bop_congruence S eqS bS -> bop_congruence S (brel_reduce r eqS) (bop_full_reduce r bS). 
Proof.  intros H C a b c d. compute.
        intros E1 E2. apply H. apply H. 
        apply C.
        exact E1.
        exact E2.
Qed.

Lemma bop_full_reduce_pseudo_associative_implies_associative (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
  brel_reflexive S eqS ->
  brel_symmetric S eqS ->  
  brel_transitive S eqS ->   
  uop_idempotent S eqS r ->
  uop_congruence S eqS r ->
  bop_congruence S eqS bS ->
  bop_pseudo_associative S eqS r bS -> 
         bop_associative S (brel_reduce r eqS) (bop_full_reduce r bS). 
Proof. intros refS symS tranS r_idem r_cong bS_cong p_assoc s1 s2 s3. compute.
       apply r_cong.
       assert (J1 := r_idem (bS (r s1) (r s2))).
       assert (J2 := bS_cong _ _ _ _ J1 (refS (r s3))). 
       assert (J3 := r_idem (bS (r s2) (r s3))).
       assert (J4 := bS_cong _ _ _ _ (refS (r s1)) J3). 
       apply r_cong in J2. apply r_cong in J4.
       assert (K : eqS (r (bS (r (bS (r s1) (r s2))) (r s3))) (r (bS (r s1) (r (bS (r s2) (r s3))))) = true). apply p_assoc. 
       assert (J5 := tranS _ _ _ J2 K).
       apply symS in J4.
       assert (J6 := tranS _ _ _ J5 J4).
       exact J6.
Qed.


Lemma bop_full_reduce_associative_implies_pseudo_associative (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
  brel_reflexive S eqS ->
  brel_symmetric S eqS ->  
  brel_transitive S eqS ->   
  uop_idempotent S eqS r ->
  uop_congruence S eqS r ->
  bop_congruence S eqS bS ->
  bop_associative S (brel_reduce r eqS) (bop_full_reduce r bS) ->
      bop_pseudo_associative S eqS r bS. 
Proof. intros refS symS tranS r_idem r_cong bS_cong assoc s1 s2 s3. compute.
       assert (K := assoc s1 s2 s3). compute in K.
       assert (J1 := r_idem ((bS (r (r (bS (r s1) (r s2)))) (r s3)))). 
       assert (J2 := r_idem ((bS (r s1) (r (r (bS (r s2) (r s3))))))).
       assert (J3 := tranS _ _ _ K J2).
       apply symS in J1.
       assert (J4 := tranS _ _ _ J1 J3).       
       assert (J5 := r_idem (bS (r s1) (r s2))).
       assert (J6 := r_idem (bS (r s2) (r s3))).
       assert (J7 := bS_cong _ _ _ _ J5 (refS (r s3))). apply r_cong in J7.
       assert (J8 := bS_cong _ _ _ _ (refS (r s1)) J6). apply r_cong in J8.
       assert (J9 := tranS _ _ _ J4 J8).              
       apply symS in J7.
       assert (J10 := tranS _ _ _ J7 J9).               
       exact J10.
Qed.



Lemma bop_full_reduce_commutative (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
      uop_congruence S eqS r -> 
      bop_commutative S eqS bS -> bop_commutative S eqS (bop_full_reduce r bS). 
Proof.  intros H C a b. compute. apply H. apply C. Qed. 


Lemma bop_full_reduce_commutative_v2 (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
      uop_congruence S eqS r -> 
      bop_commutative S eqS bS ->
           bop_commutative S (brel_reduce r eqS) (bop_full_reduce r bS). 
Proof.  intros H C a b. compute. apply H. apply H. apply C. Qed. 

(*
Lemma bop_full_reduce_not_commutative (S : Type) (x y : S) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
  uop_congruence S eqS r -> 
         bop_not_commutative S (brel_reduce r eqS) (bop_full_reduce r bS). 
Proof. intro r_cong. exists (x, y). compute.

Qed.
*) 
