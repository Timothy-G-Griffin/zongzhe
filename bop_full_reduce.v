
Require Export Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.   
Require Import CAS.basic. 
Require Import CAS.properties. 



Lemma bop_full_reduce_commutative (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
      uop_congruence S eqS r -> 
      bop_commutative S eqS bS -> bop_commutative S eqS (bop_full_reduce r bS). 
Proof.  intros H C a b. compute. apply H. apply C. Qed. 


Lemma bop_full_reduce_commutative_v2 (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
      uop_congruence S eqS r -> 
      bop_commutative S eqS bS ->
           bop_commutative S (brel_reduce r eqS) (bop_full_reduce r bS). 
Proof.  intros H C a b. compute. apply H. apply H. apply C. Qed. 


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

