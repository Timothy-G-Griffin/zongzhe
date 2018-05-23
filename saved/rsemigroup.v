Require Export Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.   
Require Import CAS.basic. 
Require Import CAS.properties. 
Require Import CAS.structures.
Require Import CAS.facts.
Require Import CAS.reduction_theory.
Require Import CAS.product.

Section Reduced_Semigroup.

Lemma bop_reduce_associative (S : Type) (eq : brel S) (r : unary_op S) (b : binary_op S) :
  brel_symmetric S eq ->
  brel_transitive S eq ->   
  uop_congruence S eq r ->
  bop_congruence S eq b ->
  bop_left_uop_invariant S eq (bop_reduce r b) r ->
  bop_right_uop_invariant S eq (bop_reduce r b) r ->   
  bop_associative S eq b ->
     bop_associative S eq (bop_full_reduce r b).
Proof. intros symS tranS r_cong b_cong bli bri H s1 s2 s3.
       compute.
       assert (H3 := bli (r (b (r s1) (r s2))) (r s3)). compute in H3.
       assert (H4 := bli ((b (r s1) (r s2))) (r s3)). compute in H4.
       assert (H5 := tranS _ _ _ H3 H4).
       assert (H6 := bri (r s1) (r (b (r s2) (r s3)))). compute in H6.
       assert (H7 := bri (r s1) (b (r s2) (r s3))). compute in H7.
       assert (H8 := tranS _ _ _ H6 H7).
       assert (H9 := H (r s1) (r s2) (r s3)). apply r_cong in H9.
       assert (H10 := tranS _ _ _ H5 H9). apply symS in H8.
       assert (H11 := tranS _ _ _ H10 H8).
       exact H11.
Qed.

Lemma bop_reduce_congruence (S : Type) (eq : brel S) (r : unary_op S) (b : binary_op S) :
  brel_symmetric S eq ->  
  brel_transitive S eq ->     
  uop_congruence S eq r ->
  bop_congruence S eq b ->
  bop_congruence S eq (bop_full_reduce r b). 
Proof. intros symS tranS r_cong b_cong s1 s2 s3 s4. compute. intros H1 H2. 
       apply r_cong. apply r_cong in H1. apply r_cong in H2.
       assert (H3 := b_cong _ _ _ _ H1 H2). 
       exact H3. 
Qed.



Lemma red_bop_comm2 (S : Type) (eqS : brel S) (r : unary_op S) (b : binary_op S) :
    uop_congruence S eqS r ->
     bop_commutative S eqS b -> bop_commutative S eqS (bop_full_reduce r b).
Proof. intros r_cong H1 s1 s2. compute.
       apply r_cong. apply H1.  
Qed.


Definition red_commutative_semigroup_proofs (S : Type) (eq : brel S) (r : unary_op S) (b : binary_op S) :
  uop_congruence S eq r ->
  bop_left_uop_invariant S eq (bop_reduce r b) r ->
  bop_right_uop_invariant S eq (bop_reduce  r b) r ->
  eqv_proofs S eq  -> 
  commutative_semigroup_proofs S eq b ->
     commutative_semigroup_proofs S eq (bop_full_reduce r b)
:= λ r_cong bli bri eqv sg,
{|
  csg_associative   := bop_reduce_associative S eq r b
                         (eqv_symmetric S eq eqv)
                         (eqv_transitive S eq eqv)                                             
                         r_cong 
                         (csg_congruence S eq b sg)
                         bli
                         bri
                         (csg_associative S eq b sg)                    
; csg_congruence    := bop_reduce_congruence S eq r b
                         (eqv_symmetric S eq eqv)
                         (eqv_transitive S eq eqv)                                             
                         r_cong
                         (csg_congruence S eq b sg)
; csg_commutative   := red_bop_comm2 S eq r b r_cong (csg_commutative S eq b sg)
|}.


Definition commutative_semigroup_reduction :
  ∀ (S : Type) 
     (csg : commutative_semigroup S)
     (r : unary_op S),
     reduction_eqv_proofs S (ceq S csg) r ->
     reduction_bop_proofs S (ceq S csg) r (bop_reduce r (cbop S csg)) ->
         commutative_semigroup S
:= λ S csg r req rb,
let rcong := rep_cong _ _ _ req in   
(* NEVER USED : let ridem := rep_idem _ _ _ req in *) 
let bli   := rb_left _ _ _ _ rb in
let blr   := rb_right _ _ _ _ rb in          
{|
   ceq   := ceq S csg
;  cbop  := bop_full_reduce r (cbop S csg)
;  ceqv  := ceqv S csg
;  csgp  := red_commutative_semigroup_proofs S (ceq S csg) r (cbop S csg)
                                  rcong
                                  bli
                                  blr
                                  (ceqv S csg)
                                  (csgp S csg)                                  
|}.

End Reduced_Semigroup.   


(* ******************************************************************************** *) 


Section Product_Rsemigroup.

Lemma uop_idempotent_product (S T : Type) (eqS : brel S) (eqT : brel T) (repS : unary_op S) (repT : unary_op T) : 
    uop_idempotent S eqS repS -> uop_idempotent T eqT repT -> uop_idempotent (S * T) (brel_product eqS eqT) (uop_product repS repT).
Proof. intros uiS uiT [s t]. compute. rewrite uiS. apply uiT. Qed.

Lemma uop_congruence_product (S T : Type) (eqS : brel S) (eqT : brel T) (repS : unary_op S) (repT : unary_op T) : 
    uop_congruence S eqS repS -> uop_congruence T eqT repT -> uop_congruence (S * T) (brel_product eqS eqT) (uop_product repS repT).
Proof. intros uiS uiT [s1 t1] [s2 t2]. compute.
       case_eq (eqS s1 s2); intro H.
       intro K. apply uiT in K. apply uiS in H. 
       rewrite H. exact K. 
       intro F. discriminate. 
Qed. 
Definition reduction_eqv_proofs_product (S T : Type) (eqS : brel S) (eqT : brel T) (repS : unary_op S) (repT : unary_op T) : 
  reduction_eqv_proofs S eqS repS ->
  reduction_eqv_proofs T eqT repT ->
      reduction_eqv_proofs (S * T) (brel_product eqS eqT) (uop_product repS repT)
:= λ rpS rpT,                                                               
   {|
       rep_idem := uop_idempotent_product S T eqS eqT repS repT (rep_idem S eqS repS rpS) (rep_idem T eqT repT rpT)
     ; rep_cong := uop_congruence_product S T eqS eqT repS repT (rep_cong S eqS repS rpS) (rep_cong T eqT repT rpT)                                        
   |}.

(* a simple rsemigroup combinator! *) 
Definition rsemigroup_product : ∀ {S T : Type},  rsemigroup S -> rsemigroup T -> rsemigroup (S * T)
:= λ {S T} sgS sgT,
{|
    r_eq := brel_product (r_eq S sgS) (r_eq T sgT)
;  r_rep := uop_product (r_rep S sgS) (r_rep T sgT)                          
;  r_bop := bop_product (r_bop S sgS) (r_bop T sgT) 
;  r_eqv := eqv_proofs_product S T (r_eq S sgS) (r_eq T sgT) (r_eqv S sgS) (r_eqv T sgT)
;  r_rpv := reduction_eqv_proofs_product S T (r_eq S sgS) (r_eq T sgT) (r_rep S sgS) (r_rep T sgT) (r_rpv S sgS) (r_rpv T sgT) 
;  r_sgp := sg_proofs_product S T (r_eq S sgS) (r_eq T sgT) (r_eqv S sgS) (r_eqv T sgT) (r_bop S sgS) (r_bop T sgT) (r_sgp S sgS) (r_sgp T sgT) 
|}.

End Product_Rsemigroup.


