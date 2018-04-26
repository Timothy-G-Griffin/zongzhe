Require Export Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.   
Require Import CAS.basic. 
Require Import CAS.properties. 
Require Import CAS.structures.
Require Import CAS.product.
Require Import CAS.facts.
Require Import CAS.brel_reduce.
Require Import CAS.bop_full_reduce.
Require Import CAS.predicate_reduce.
Require Import CAS.reduce_annihilators.
Require Coq.Arith.EqNat.         (* beq_nat *) 
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Min.   
Require Export Coq.Unicode.Utf8.
(* Require Import Coq.Bool.Bool.    *)

Open Scope nat.


Section MinPlusCeiling.

Definition brel_eq_nat  : brel nat  := Arith.EqNat.beq_nat.

Definition P (ceiling : nat): nat -> bool := λ n, n <=? ceiling.

Definition uop_nat (ceiling : nat) : unary_op nat := uop_predicate_reduce ceiling (P ceiling).

Definition min := Nat.min.
Definition plus := Nat.add.

Lemma brel_nat_eq_S : ∀ s t : nat, brel_eq_nat (S s) (S t) = brel_eq_nat s t. 
Proof. unfold brel_eq_nat. induction s; induction t; compute; reflexivity. Qed. 

Lemma brel_nat_neq_S : ∀ s : nat, brel_eq_nat s (S s) = false. 
Proof. unfold brel_eq_nat. induction s. 
          compute; reflexivity. 
          rewrite brel_nat_eq_S. assumption. 
Qed.   

Lemma brel_eq_nat_reflexive : brel_reflexive nat brel_eq_nat. 
Proof. unfold brel_reflexive, brel_eq_nat. induction s; auto. Qed. 

Lemma brel_eq_nat_symmetric : brel_symmetric nat brel_eq_nat. 
Proof. unfold brel_symmetric, brel_eq_nat. 
       induction s; induction t; simpl; intros; auto. Qed. 

Lemma brel_eq_nat_transitive : brel_transitive nat brel_eq_nat. 
Proof. unfold brel_transitive, brel_eq_nat. 
       induction s; induction t; induction u; simpl; intros; auto.        
          discriminate. apply (IHs t u H H0).
Qed. 

Lemma brel_eq_nat_congruence : brel_congruence nat brel_eq_nat brel_eq_nat. 
Proof. unfold brel_congruence, brel_eq_nat. 
       induction s; induction t; induction u; induction v; simpl; intros; auto; try discriminate.         
Qed. 

Lemma brel_reduce_nat_reflexive (ceiling :nat) : brel_reflexive nat (brel_reduce (uop_nat ceiling) brel_eq_nat).
Proof. apply brel_reduce_reflexive.
       apply brel_eq_nat_reflexive.
Qed.

Lemma brel_reduce_nat_symmetric (ceiling :nat) : brel_symmetric nat (brel_reduce (uop_nat ceiling) brel_eq_nat).
Proof. apply brel_reduce_symmetric.
       apply brel_eq_nat_symmetric.
Qed.

Lemma brel_reduce_nat_transitive (ceiling :nat) : brel_transitive nat (brel_reduce (uop_nat ceiling) brel_eq_nat).
  Proof. apply brel_reduce_transitive.
         apply brel_eq_nat_transitive; auto.
  Qed.

Lemma brel_reduce_nat_congruence (ceiling :nat) : brel_congruence nat (brel_reduce (uop_nat ceiling) brel_eq_nat) (brel_reduce (uop_nat ceiling) brel_eq_nat).
  Proof. apply brel_reduce_congruence; auto. 
         apply brel_eq_nat_congruence; auto. 
  Qed.
  
Lemma P_congruence (ceiling : nat): pred_congruence nat brel_eq_nat (P ceiling).
Proof. intros n1 n2; intro H. compute.
       assert (H' : true = brel_eq_nat n1 n2). auto.
       assert (A := beq_nat_eq n1 n2 H').
       rewrite A. auto.
Qed.

Lemma uop_nat_idempontent (ceiling : nat): uop_idempotent nat brel_eq_nat (uop_predicate_reduce ceiling (P ceiling)).
Proof. Admitted.

Lemma uop_nat_congruence (ceiling : nat) : 
  uop_congruence nat brel_eq_nat (uop_predicate_reduce ceiling (P ceiling)).
Proof. apply uop_predicate_reduce_congruence; auto.
      apply brel_eq_nat_reflexive; auto.
      unfold pred_congruence. apply P_congruence.
Qed.

Lemma P_true (ceiling : nat): pred_true nat (P ceiling) ceiling.
Proof. compute. induction ceiling. auto. auto.
Qed.

Lemma P_min_decompose (ceiling : nat): pred_bop_decompose nat (P ceiling) min.
Proof. intros n1 n2. 
     Admitted.       


Lemma P_plus_compose (ceiling : nat): pred_bop_compose nat (P ceiling) plus.
Proof. intros n1 n2 H. destruct H as [H | H].
     Admitted.

Lemma P_min_preserve_order (ceiling : nat): pred_preserve_order nat (P ceiling) brel_eq_nat min.
Proof. intros n1 n2 H1 H2.
     Admitted.

Lemma beq_nat_to_prop  : ∀ s t: nat, beq_nat s t = true -> s = t. 
Proof.  induction s;  induction t; simpl; intro H; auto; discriminate. Defined. 

Lemma beq_nat_min_congruence : 
   ∀ s1 s2 t1 t2 : nat,
   beq_nat s1 t1 = true
   → beq_nat s2 t2 = true → beq_nat (min s1 s2) (min t1 t2) = true.
Proof. 
   intros s1 s2 t1 t2 H1 H2. 
   assert (C1 := beq_nat_to_prop s1 t1 H1). 
   assert (C2 := beq_nat_to_prop s2 t2 H2). 
   rewrite C1. rewrite C2.  apply brel_eq_nat_reflexive. 
  Qed. 

Lemma bop_min_congruence : bop_congruence nat brel_eq_nat min.
Proof. unfold bop_congruence. unfold brel_eq_nat, min.
       exact beq_nat_min_congruence. 
      Qed. 


Lemma bop_min_associative : bop_associative nat brel_eq_nat min.
Proof. unfold bop_associative. intros. unfold brel_eq_nat, min. 
       rewrite (Min.min_assoc s t u). apply brel_eq_nat_reflexive.        
      Qed. 

Lemma bop_min_commutative : bop_commutative nat brel_eq_nat min.
Proof. unfold bop_commutative, min. intros s t. 
       rewrite Min.min_comm at 1. apply brel_eq_nat_reflexive. 
      Qed.

Lemma bop_min_selective : bop_selective nat brel_eq_nat min.
Proof. unfold bop_selective, min. intros s t. 
Admitted.


Lemma beq_nat_plus_congruence : 
∀ s1 s2 t1 t2 : nat,
beq_nat s1 t1 = true
→ beq_nat s2 t2 = true → beq_nat (plus s1 s2) (plus t1 t2) = true.
Proof.
  intros s1 s2 t1 t2 H1 H2.
  assert (C1 := beq_nat_to_prop s1 t1 H1). 
  assert (C2 := beq_nat_to_prop s2 t2 H2).
  rewrite C1. rewrite C2.  apply brel_eq_nat_reflexive. 
Qed.

Lemma bop_plus_congruence : bop_congruence nat brel_eq_nat plus.
Proof. unfold bop_congruence. unfold brel_eq_nat, plus.
       exact beq_nat_plus_congruence. 
      Qed.   

Lemma bop_plus_associative : bop_associative nat brel_eq_nat plus.
Proof. unfold bop_associative. intros. unfold brel_eq_nat, plus. 
       rewrite (Nat.add_assoc s t u). apply brel_eq_nat_reflexive.        
      Qed. 

Lemma bop_plus_commutative : bop_commutative nat brel_eq_nat plus.
Proof. unfold bop_commutative, plus. intros s t. 
       rewrite Nat.add_comm at 1. apply brel_eq_nat_reflexive. 
      Qed.


Lemma bop_left_distributive_min_plus : bop_left_distributive nat brel_eq_nat min plus.
Proof. intros n1 n2 n3. compute.
   Admitted.

Lemma bop_right_distributive_min_plus : bop_right_distributive nat brel_eq_nat min plus.
Proof. intros n1 n2 n3. compute.
   Admitted.  

Lemma bop_is_ann_min_zero : bop_is_ann nat brel_eq_nat min 0.
Proof. compute. intro s. split. auto.
       induction s; auto.
Qed.

Lemma bop_is_id_plus_zero : bop_is_id nat brel_eq_nat plus 0.
Proof. compute. intro s. induction s; auto. 
Qed.

Lemma uop_ceiling_min_preserves_ann (ceiling : nat) :
 uop_preserves_ann nat brel_eq_nat min (uop_nat ceiling).
Proof. intros n H.
Admitted.

Lemma uop_ceiling_plus_preserves_id (ceiling : nat) :
uop_preserves_id nat brel_eq_nat plus (uop_nat ceiling).
Proof. intros n H. compute. induction n.
Admitted.

Definition bop_nat_min (ceiling : nat) : binary_op nat := bop_fpr ceiling (P ceiling) min.
Definition bop_nat_plus (ceiling : nat) : binary_op nat := bop_fpr ceiling (P ceiling) plus.

Lemma bop_nat_min_congruence (ceiling : nat) : bop_congruence nat (brel_reduce (uop_nat ceiling) brel_eq_nat) (bop_nat_min ceiling).
Proof. apply bop_full_reduce_congruence; auto.
  apply uop_predicate_reduce_congruence; auto.
  apply brel_eq_nat_reflexive; auto.
  unfold pred_congruence. apply P_congruence. 
  apply bop_min_congruence; auto. 
Qed.

Lemma bop_nat_plus_congruence (ceiling : nat) : bop_congruence nat (brel_reduce (uop_nat ceiling) brel_eq_nat) (bop_nat_plus ceiling).
Proof. apply bop_full_reduce_congruence; auto.
  apply uop_predicate_reduce_congruence; auto.
  apply brel_eq_nat_reflexive; auto.
  unfold pred_congruence. apply P_congruence. 
  apply bop_plus_congruence; auto. 
Qed.

Lemma bop_nat_min_pseudo_associative (ceiling : nat) : bop_pseudo_associative nat brel_eq_nat (uop_nat ceiling)  min.
Proof. Admitted.

(* Lemma bop_nat_plus_pseudo_associative (ceiling : nat) : bop_pseudo_associative nat brel_eq_nat (uop_nat ceiling)  plus.
Proof. Admitted. *)

Lemma bop_nat_min_associative (ceiling : nat) : bop_associative nat (brel_reduce (uop_nat ceiling) brel_eq_nat) (bop_nat_min ceiling).
Proof. apply bop_full_reduce_pseudo_associative_implies_associative; auto.
  apply brel_eq_nat_reflexive; auto.
  apply brel_eq_nat_symmetric; auto.
  apply brel_eq_nat_transitive; auto. 
  apply uop_nat_idempontent; auto.
  apply uop_nat_congruence; auto.
  apply bop_min_congruence; auto.
  apply (bop_nat_min_pseudo_associative ceiling).
Qed.

Lemma bop_nat_plus_associative (ceiling : nat) : bop_associative nat (brel_reduce (uop_nat ceiling) brel_eq_nat) (bop_nat_plus ceiling).
Proof. apply bop_associative_fpr_compositional.
  apply brel_eq_nat_reflexive; auto.
  apply brel_eq_nat_symmetric; auto.
  apply brel_eq_nat_transitive; auto.
  apply P_true; auto.
  apply P_congruence; auto.
  apply P_plus_compose; auto.
  apply bop_plus_congruence; auto.
  apply bop_plus_associative; auto.
Qed.  

Lemma bop_nat_min_commutative (ceiling : nat) : bop_commutative nat (brel_reduce (uop_nat ceiling) brel_eq_nat) (bop_nat_min ceiling).
Proof. apply bop_full_reduce_commutative; auto.
  apply uop_predicate_reduce_congruence; auto.       
  apply brel_eq_nat_reflexive; auto.
  unfold pred_congruence. apply P_congruence.
  apply bop_min_commutative; auto.
Qed.

Lemma bop_nat_plus_commutative (ceiling : nat) : bop_commutative nat (brel_reduce (uop_nat ceiling) brel_eq_nat) (bop_nat_plus ceiling).
Proof. apply bop_full_reduce_commutative; auto.
  apply uop_predicate_reduce_congruence; auto.       
  apply brel_eq_nat_reflexive; auto.
  unfold pred_congruence. apply P_congruence.
  apply bop_plus_commutative; auto.
Qed.

End MinPlusCeiling.