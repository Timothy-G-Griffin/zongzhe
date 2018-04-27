Require Export Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.   
Require Import CAS.basic. 
Require Import CAS.properties. 
Require Import CAS.structures.
Require Import CAS.product.
Require Import CAS.facts.
Require Import CAS.bop_full_reduce.
Require Import CAS.reduction_theory. 
Require Import CAS.predicate_reduce.

Section Explore.

Variable S : Type.
Variable P : S -> bool.

Variable eq : brel S. 
Variable refS : brel_reflexive S eq.
Variable symS : brel_symmetric S eq.
Variable tranS : brel_transitive S eq.

Lemma bop_fpr_left_pseudo_distributive :
  ∀ (s : S) (add mul : binary_op S),
(*    
     pred_bop_decompose S P add ->
     pred_bop_decompose S P mul ->          
     bop_congruence S eq add ->     
     bop_congruence S eq mul -> 
 *)
    pred_true S P s ->
    pred_congruence S eq P ->
    bop_is_id S eq add s ->     
    bop_is_ann S eq mul s ->    
    bop_left_distributive S eq add mul ->
       bop_pseudo_left_distributive S (brel_reduce (uop_predicate_reduce s P) eq) (uop_predicate_reduce s P) (bop_fpr s P add) (bop_fpr s P mul).
Proof. intros s add mul Ps P_cong id ann ldist a b c. compute.
       assert (PAL : ∀ (x : S), P(add s x) = P x). intro x. destruct (id x) as [H _]. apply P_cong in H. exact H. 
       assert (PAR : ∀ (x : S), P(add x s) = P x). intro x. destruct (id x) as [_ H]. apply P_cong in H. exact H. 
       assert (PML : ∀ (x : S), P(mul s x) = true). intro x. destruct (ann x) as [H _]. apply P_cong in H. rewrite Ps in H. exact H. 
       assert (PMR : ∀ (x : S), P(mul x s) = true). intro x. destruct (ann x) as [_ H]. apply P_cong in H. rewrite Ps in H. exact H.               
       case_eq(P a); intro Pa; case_eq(P b); intro Pb; case_eq(P c); intro Pc;
         repeat ( try rewrite Ps;
                  try rewrite Pa;
                  try rewrite Pb;
                  try rewrite Pc;
                  try rewrite PAL;
                  try rewrite PAR;                   
                  try rewrite PML;
                  try rewrite PMR;                   
                  try auto
                ).
       assert (H1 : P (mul a (add s c)) = false). admit. rewrite H1.
       case_eq(P (mul a c)); intro Pmac; repeat (try rewrite H1; try rewrite Ps; try rewrite Pmac; try auto).
       admit. (* ? *)
       assert (H2 : P (add s (mul a c)) = false). admit. rewrite H2.   rewrite H2.     
       admit. (* ? *)

       assert (H3 : P (mul a (add b s)) = P(mul a b)). admit.
       assert (H4 : P (add (mul a b) s) = P(mul a b)). admit.        
       case_eq(P (mul a b)); intro H1; repeat (try rewrite Ps; try rewrite Pa; try rewrite Pc; try rewrite H3; try rewrite H4; try rewrite H1; try auto).
       admit. (* OK *) 
 
       (* 1 subgoal *)
       assert (LD := ldist a b c). apply symS in LD. 
       assert (PLD := P_cong _ _ LD).
       case_eq(P(add a b)); intro J1; case_eq(P(add b c)); intro J2;
       case_eq(P(mul a b)); intro J3; case_eq(P(mul a c)); intro J4;
       case_eq(P(mul a (add b c))); intro J5; 
         repeat (try rewrite Ps;
                 try rewrite Pa;
                 try rewrite Pb;
                 try rewrite Pc;
                 try rewrite J1;
                 try rewrite J2;
                 try rewrite J3;
                 try rewrite J4;
                 try rewrite PLD;                                                  
                 try rewrite J5;
                  try rewrite PAL;
                  try rewrite PAR;                   
                  try rewrite PML;
                  try rewrite PMR;                   
                  try auto).
       admit. (* need contra *)
       admit. (* need contra *)
       admit. (* need contra *)       
       admit. (* need contra *)       
       admit. (* need contra *)
       admit. (* need contra *)
       admit. (* need contra *)       
       admit. (* need contra *)       
       admit. (* need contra *)
       admit. (* need contra *)
       admit. (* need contra *)       
       admit. (* need contra *)       
       admit. (* need contra *)
       admit. (* need contra *)
       admit. (* need contra *)
(*
  J1 : P (add a b) = false
  J2 : P (add b c) = false
*)
       admit. (* need contra *)       
       admit. (* need contra *)
       admit. (* need contra *)
       admit. (* need contra *)       
       admit. (* need contra *)       
Admitted.

End Explore. 


Section Experiments.

  Variable S : Type.
  Variable eq : brel S.
  Variable refS : brel_reflexive S eq.  
  Variable symS : brel_symmetric S eq.
  Variable tranS : brel_transitive S eq.   

  Variable r : unary_op S.
  Variable r_cong : uop_congruence S eq r.
  Variable r_idem : uop_idempotent S eq r.
  
  Variable b : binary_op S.
  Variable b_cong : bop_congruence S eq b.  

  Definition T : Type := red_Type S r eq.
  Definition eqT : brel T := red_eq S r eq.
  Definition bT : binary_op T := red_bop S b r eq r_idem.   

  Definition bop_pseudo_idempotent  
      := ∀ (s : S), eq (r (b (r s) (r s))) (r s) = true. 
  
  Lemma iso_idem : bop_idempotent T eqT bT <-> bop_pseudo_idempotent . 
  Proof. split. intros H s.
         assert (K := H (inj S r eq r_idem s)).
         compute in K. 
         exact K. 
         intros H [s p]. compute.
         assert (K := H s). unfold Pr in p. 
         assert (J := b_cong _ _ _ _ p p). apply r_cong in J.
         apply symS in J.
         assert (L := tranS _ _ _ J K).
         assert (M := tranS _ _ _ L p).
         exact M.
  Qed.          


  Lemma iso_idem2 : bop_pseudo_idempotent <-> bop_idempotent S (brel_reduce r eq) (bop_reduce_args r b).  
  Proof. split; compute. intros H s.
         assert (K := H s).
         exact K. 
         intros H s. 
         assert (K := H s). 
         exact K. 
  Qed.

  Lemma iso_idem3 : bop_idempotent S (brel_reduce r eq) (bop_full_reduce r b)  <-> bop_idempotent S (brel_reduce r eq) (bop_reduce_args r b).  
  Proof. split; compute. intros H s.
         assert (K := H s).
         assert (J := r_idem (b (r s) (r s))).  apply symS in J.
         assert (N := tranS _ _ _ J K). 
         exact N. 
         intros H s. 
         assert (K := H s).
         apply r_cong in K.
         assert (J := r_idem s).
         assert (N := tranS _ _ _ K J). 
         exact N.          
  Qed.          
  

  (*
  Lemma iso_idem3 : bop_idempotent S eq (bop_full_reduce r b)  <-> bop_idempotent S (brel_reduce r eq) (bop_reduce_args r b).  
  Proof. split; compute. intros H s.
         assert (K := H s).
         assert (J := r_idem s).         
         exact K. 
         intros H s. 
         assert (K := H s). 
         exact K. 
  Qed.          
*) 
  
  Lemma test_commutative : bop_commutative T eqT bT <-> bop_commutative S (brel_reduce r eq) (bop_reduce_args r b).
  Proof. split;compute.  intros H s1 s2.
         assert (K := H (inj S r eq r_idem s1) (inj S r eq r_idem s2)).
         compute in K. 
         exact K. 
         intros H [s1 p1] [s2 p2]. compute. unfold Pr in p1, p2. 
         assert (K := H s1 s2).
         assert (J1 := b_cong _ _ _ _ p1 p2). apply r_cong in J1.
         assert (J2 := b_cong _ _ _ _ p2 p1). apply r_cong in J2.         
         apply symS in J1.
         assert (J3 := tranS _ _ _ J1 K).
         assert (J4 := tranS _ _ _ J3 J2).
         exact J4.
  Qed.          

  Lemma test_not_commutative_1 : bop_not_commutative T eqT bT -> bop_not_commutative S (brel_reduce r eq) (bop_reduce_args r b).
  Proof. intros [[[s1 p1] [s2 p2]] Q]. compute in Q.
         exists (s1, s2). compute.
         assert (J1 := b_cong _ _ _ _ p1 p2). apply r_cong in J1. 
         assert (J2 := b_cong _ _ _ _ p2 p1). apply r_cong in J2.
         assert (J3 := brel_transitive_f2 S eq symS tranS _ _ _ J1 Q). apply symS in J2.
         assert (J4 := brel_transitive_f1 S eq symS tranS _ _ _ J3 J2).
         exact J4. 
  Qed.          

  Lemma test_not_commutative_2 : bop_not_commutative S (brel_reduce r eq) (bop_reduce_args r b) -> bop_not_commutative T eqT bT. 
  Proof. intros [[s1 s2] Q]. compute in Q.
         exists (inj S r eq r_idem s1, inj S r eq r_idem s2). compute.
         exact Q. 
  Qed.          
  

  
  
  Variable add mul : binary_op S.
  Variable add_cong : bop_congruence S eq add.
  Variable mul_cong : bop_congruence S eq mul.   
  Definition addT : binary_op T := red_bop S add r eq r_idem. 
  Definition mulT : binary_op T := red_bop S mul r eq r_idem.


  Lemma test_ldist : bop_left_distributive S (brel_reduce r eq) (bop_reduce_args r add) (bop_reduce_args r mul)
                     <->
                     bop_pseudo_left_distributive S eq r add mul.
  Proof. split. intros H s1 s2 s3. 
         assert (K := H s1 s2 s3). compute in K. 
         exact K. 
         intros H s1 s2 s3. compute.
         assert (K := H s1 s2 s3). 
         exact K.
  Qed.

  Lemma test_ldist2 : bop_left_distributive S (brel_reduce r eq) (bop_reduce_args r add) (bop_reduce_args r mul)
                     <->
                     bop_left_distributive S (brel_reduce r eq) (bop_full_reduce r add) (bop_full_reduce r mul).
  Proof. split. intros H s1 s2 s3. 
         assert (K := H s1 s2 s3). compute in K. compute. apply r_cong in K. 
         admit. 
         intros H s1 s2 s3. compute.
         assert (K := H s1 s2 s3). compute in K. 
         admit. 
Admitted. 

  
  Lemma testing: bop_associative S (brel_reduce r eq) (bop_full_reduce r add).
   Proof. intros a b c. compute.
         assert (K : bop_pseudo_associative S eq r add). admit.
         assert (J := K a b c). 
         

  Lemma addT_not_commutative (z : T * T) : bop_not_commutative T eqT addT.
  Proof. unfold bop_not_commutative. exists z. 
         destruct z as [[s1 p1] [s2 p2]].
         compute. 


End Experiments.   