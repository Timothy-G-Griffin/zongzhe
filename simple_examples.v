Require Coq.Arith.EqNat.         (* beq_nat *) 
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Min.   
Require Export Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.   
Require Import CAS.basic. 
Require Import CAS.properties. 
Require Import CAS.structures.
Require Import CAS.rsemigroup.

Open Scope nat.

Definition brel_eq_nat  : brel nat  := Arith.EqNat.beq_nat.  

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

Definition eqv_proofs_eq_nat : eqv_proofs nat brel_eq_nat 
:= {| 

     eqv_reflexive   := brel_eq_nat_reflexive 
   ; eqv_transitive  := brel_eq_nat_transitive 
   ; eqv_symmetric   := brel_eq_nat_symmetric
   ; eqv_congruence  := brel_eq_nat_congruence
   ; eqv_witness     := 0
   |}. 



Definition bop_min    : binary_op nat := min.

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
Defined. 

Lemma bop_min_congruence : bop_congruence nat brel_eq_nat bop_min.
Proof. unfold bop_congruence. unfold brel_eq_nat, bop_min.
       exact beq_nat_min_congruence. 
Defined. 


Lemma bop_min_associative : bop_associative nat brel_eq_nat bop_min.
Proof. unfold bop_associative. intros. unfold brel_eq_nat, bop_min. 
       rewrite (Min.min_assoc s t u). apply brel_eq_nat_reflexive.        
Defined. 

Lemma bop_min_commutative : bop_commutative nat brel_eq_nat bop_min.
Proof. unfold bop_commutative, bop_min. intros s t. 
       rewrite Min.min_comm at 1. apply brel_eq_nat_reflexive. 
Defined.

Definition sg_proofs_min : commutative_semigroup_proofs nat brel_eq_nat bop_min := 
{| 
  csg_associative  := bop_min_associative
; csg_congruence   := bop_min_congruence
; csg_commutative  := bop_min_commutative
|}. 

Definition sg_min : commutative_semigroup nat 
:= {|
   ceq   := brel_eq_nat 
;  cbop  := bop_min
;  ceqv  := eqv_proofs_eq_nat
;  csgp  := sg_proofs_min
|}. 


Definition nat_rep : unary_op nat := λ x, if brel_eq_nat x 0 then 0 else 1.

Lemma fact1 : uop_congruence nat brel_eq_nat nat_rep.
Proof. intros n1 n2.
       destruct n1; destruct n2; intro H.
       compute. reflexivity.
       compute in H. discriminate. 
       compute in H. discriminate. 
       compute. reflexivity.
Qed.

Lemma fact2 : uop_idempotent nat brel_eq_nat nat_rep.
Proof. intro n. destruct n. 
       compute.   reflexivity.
       compute. reflexivity.
Qed.

Lemma fact3 : bop_left_uop_invariant nat brel_eq_nat (bop_reduce nat_rep bop_min) nat_rep.
Proof. intros n1 n2. 
       destruct n1. 
       compute. reflexivity. 
       destruct n2.
       compute. reflexivity.
       unfold nat_rep at 2.
       simpl. reflexivity. 
Qed.

Lemma fact4 : bop_right_uop_invariant nat brel_eq_nat (bop_reduce nat_rep bop_min) nat_rep.
Proof. intros n1 n2. 
       destruct n1. 
       compute. reflexivity. 
       destruct n2.
       compute. reflexivity.
       unfold nat_rep at 2.
       simpl. reflexivity. 
Qed.

Definition nat_rep_reduction_eqv_proofs : reduction_eqv_proofs nat brel_eq_nat nat_rep :=
{|
  rep_cong  := fact1
; rep_idem  := fact2
|}.

Definition nat_rep_reduction_bop_proofs : reduction_bop_proofs nat brel_eq_nat nat_rep (bop_reduce nat_rep bop_min) :=
{|
   rb_left  := fact3
; rb_right := fact4
|}.


Definition nat_rep_rsg := commutative_semigroup_reduction nat sg_min nat_rep nat_rep_reduction_eqv_proofs nat_rep_reduction_bop_proofs.

(*
Check nat_rep_rsg. 

Definition b := cbop nat nat_rep_rsg.
Compute (b 0 99).
Compute (b 88 99).
*) 
