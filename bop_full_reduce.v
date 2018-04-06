Require Export Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.   
Require Import CAS.basic. 
Require Import CAS.properties. 


Lemma bop_full_reduce_congruence (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
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



(*
   Some sufficient conditions ... 
*)

(* 
    Commutativity 
*)
Lemma bop_full_reduce_commutative (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
      uop_congruence S eqS r -> 
      bop_commutative S eqS bS ->
           bop_commutative S (brel_reduce r eqS) (bop_full_reduce r bS). 
Proof.  intros H C a b. compute. apply H. apply H. apply C. Qed. 
(* 
      idempotence 
*)   
Lemma bop_full_reduce_idempotent (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
  brel_transitive S eqS -> 
  uop_congruence S eqS r ->
  uop_idempotent S eqS r ->   
  bop_idempotent S eqS bS -> bop_idempotent S (brel_reduce r eqS) (bop_full_reduce r bS). 
Proof. intros transS r_cong r_idem idemS s. compute.
       assert (H1 := idemS (r s)). apply r_cong in H1. 
       assert (H2 := r_idem s). 
       assert (H3 := transS _ _ _ H1 H2).  apply r_cong in H3.
       assert (H4 := transS _ _ _ H3 H2).       
       exact H4. 
Qed.                                  
(* 
    Selectivity 
*)   
Lemma bop_full_reduce_selective (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
  brel_transitive S eqS -> 
  uop_congruence S eqS r ->
  uop_idempotent S eqS r ->   
  bop_selective S eqS bS -> bop_selective S (brel_reduce r eqS) (bop_full_reduce r bS). 
Proof. intros transS r_cong r_idem selS s1 s2. compute.
         destruct (selS (r s1) (r s2)) as [H1 | H1].
         left.
         apply r_cong in H1. 
         assert (H2 := r_idem s1).
         assert (H3 := transS _ _ _ H1 H2). apply r_cong in H3.
         assert (H4 := transS _ _ _ H3 H2). 
         exact H4.
         right.
         apply r_cong in H1. 
         assert (H2 := r_idem s2).
         assert (H3 := transS _ _ _ H1 H2). apply r_cong in H3.
         assert (H4 := transS _ _ _ H3 H2). 
         exact H4.         
Qed.                                  
(* 
      Id 
*)   
Lemma bop_full_reduce_exists_id (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
  brel_reflexive S eqS ->  
  brel_transitive S eqS -> 
  uop_congruence S eqS r ->
  uop_idempotent S eqS r ->
  bop_congruence S eqS bS ->  
  uop_preserves_id S eqS bS r -> bop_exists_id S eqS bS -> bop_exists_id S (brel_reduce r eqS) (bop_full_reduce r bS). 
Proof. intros refS transS r_cong r_idem congS H [id p].
       assert (K := H id p).
       exists id. compute. 
       intros t. 
       destruct (p (r t)) as [H1  H2]. split. 
       assert (H3 := congS _ _ _ _ K (refS (r t))).
       assert (H4 := transS _ _ _ H3 H1). apply r_cong in H4. 
       assert (H5 := r_idem t). 
       assert (H6 := transS _ _ _ H4 H5). apply r_cong in H6. 
       assert (H7 := transS _ _ _ H6 H5).
       exact H7.
       assert (H3 := congS _ _ _ _ (refS (r t)) K).
       assert (H4 := transS _ _ _ H3 H2). apply r_cong in H4. 
       assert (H5 := r_idem t). 
       assert (H6 := transS _ _ _ H4 H5). apply r_cong in H6. 
       assert (H7 := transS _ _ _ H6 H5).
       exact H7.
Qed.
(* 
      Ann 
*)   
Lemma bop_full_reduce_exists_ann (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
  brel_reflexive S eqS ->  
  brel_transitive S eqS -> 
  uop_congruence S eqS r ->
  bop_congruence S eqS bS ->  
  uop_preserves_ann S eqS bS r -> bop_exists_ann S eqS bS -> bop_exists_ann S (brel_reduce r eqS) (bop_full_reduce r bS). 
Proof. intros refS transS r_cong congS H [ann p].
       assert (K := H ann p).
       exists ann. compute. 
       intros t. 
       destruct (p (r t)) as [H1  H2]. split. 
       assert (H3 := congS _ _ _ _ K (refS (r t))).
       assert (H4 := transS _ _ _ H3 H1). apply r_cong in H4. 
       assert (H6 := transS _ _ _ H4 K). apply r_cong in H6. 
       exact H6.
       assert (H3 := congS _ _ _ _ (refS (r t)) K).
       assert (H4 := transS _ _ _ H3 H2). apply r_cong in H4. 
       assert (H6 := transS _ _ _ H4 K). apply r_cong in H6. 
       exact H6.
Qed.
