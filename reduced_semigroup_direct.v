Require Export Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.   
Require Import CAS.basic. 
Require Import CAS.properties. 
Require Import CAS.structures.
Require Import CAS.reduction_theory.


Section Reduced_Semigroup_Direct.

(*  Note on types: 
  red_Type : ∀ S : Type, unary_op S → brel S → Type 
  red_eq   : ∀ (S : Type) (r : unary_op S) (eqS : brel S), brel (red_Type S r eqS)
  red_bop  : ∀ S : Type, binary_op S → ∀ (r : unary_op S) (eqS : brel S), uop_idempotent S eqS r → binary_op (red_Type S r eqS) 
*)

Definition reduced_eqv_proofs : ∀ (S : Type) (eq : brel S) (r : unary_op S) (b : binary_op S),  
    eqv_proofs S eq -> reduction_eqv_proofs S eq r -> eqv_proofs (red_Type S r eq) (red_eq S r eq)
:= λ S eq r b eqv red,
{|
  eqv_reflexive      := red_ref S r eq (eqv_reflexive S eq eqv) 
; eqv_transitive     := red_trans S r eq (eqv_transitive S eq eqv) 
; eqv_symmetric      := red_sym S r eq (eqv_symmetric S eq eqv)
; eqv_witness        := inj S r eq (rep_idem S eq r red) (eqv_witness S eq eqv)                         
|}.

Definition reduced_semigroup_proofs :
  ∀ (S : Type)
    (eq : brel S)
    (r : unary_op S)
    (b : binary_op S)
    (eqv : eqv_proofs S eq)
    (csg : semigroup_proofs S eq b)
    (req : reduction_eqv_proofs S eq r)     
    (rb  : reduction_bop_proofs S eq r (bop_reduce r b)) 
    (dec : bop_commutative_decidable (red_Type S r eq) (red_eq S r eq) (red_bop S b r eq (rep_idem _ _ _ req))), 
         semigroup_proofs (red_Type S r eq) (red_eq S r eq) (red_bop S b r eq (rep_idem _ _ _ req))
:= λ S eq r b eqv csg req rb dec,
{|
  sg_associative := red_bop_ass S b r eq
                           (eqv_symmetric S eq eqv)
                           (eqv_transitive S eq eqv)
                           (sg_associative S eq b csg)
                           (rep_cong S eq r req)
                           (rep_idem S eq r req)
                           (rb_left S eq r _ rb)
                           (rb_right S eq r _ rb)                            
  ; sg_congruence  := red_bop_cong S b r eq
                           (sg_congruence S eq b csg)
                           (rep_cong S eq r req)
                           (rep_idem S eq r req)

  ; sg_commutative_d  := dec 
|}.

Definition reduced_commutative_semigroup_proofs :
  ∀ (S : Type)
    (eq : brel S)
    (r : unary_op S)
    (b : binary_op S)
    (eqv : eqv_proofs S eq)
    (csg : commutative_semigroup_proofs S eq b)
    (req : reduction_eqv_proofs S eq r)     
    (rb  : reduction_bop_proofs S eq r (bop_reduce r b)), 
         commutative_semigroup_proofs (red_Type S r eq) (red_eq S r eq) (red_bop S b r eq (rep_idem _ _ _ req))
:= λ S eq r b eqv csg req rb,
{|
  csg_associative := red_bop_ass S b r eq
                           (eqv_symmetric S eq eqv)
                           (eqv_transitive S eq eqv)
                           (csg_associative S eq b csg)
                           (rep_cong S eq r req)
                           (rep_idem S eq r req)
                           (rb_left S eq r _ rb)
                           (rb_right S eq r _ rb)                            
  ; csg_congruence  := red_bop_cong S b r eq
                           (csg_congruence S eq b csg)
                           (rep_cong S eq r req)
                           (rep_idem S eq r req)

  ; csg_commutative  := red_bop_comm S b r eq
                           (rep_cong S eq r req)
                           (rep_idem S eq r req)
                           (csg_commutative S eq b csg)                           
|}.


(* semigroup combinators for reductions --- not extaction friendly! *) 
Definition semigroup_reduced:
  ∀ (S : Type)
     (csg : semigroup S)
     (r : unary_op S)
     (req : reduction_eqv_proofs S (eq S csg) r)
     (rb  : reduction_bop_proofs S (eq S csg) r (bop_reduce r (bop S csg)))
     (dec : bop_commutative_decidable (red_Type S r (eq S csg)) (red_eq S r (eq S csg)) (red_bop S (bop S csg) r (eq S csg) (rep_idem _ _ _ req))),      
           semigroup (red_Type S r (eq S csg))
:= λ S csg r req rb dec,
{|
   eq   := red_eq S r (eq S csg)
;  bop  := red_bop S (bop S csg) r (eq S csg) (rep_idem _ _ _ req)
;  eqv  := reduced_eqv_proofs S (eq S csg) r (bop S csg) (eqv S csg) req
;  sgp  := reduced_semigroup_proofs S (eq S csg) r (bop S csg) (eqv S csg) (sgp S csg) req rb dec
|}.


Definition commutative_semigroup_direct_reduction :
  ∀ (S : Type)
     (csg : commutative_semigroup S)
     (r : unary_op S)
     (req : reduction_eqv_proofs S (ceq S csg) r)     
     (rb  : reduction_bop_proofs S (ceq S csg) r (bop_reduce r (cbop S csg))),
         commutative_semigroup (red_Type S r (ceq S csg))
:= λ S csg r req rb,
{|
   ceq   := red_eq S r (ceq S csg)
;  cbop  := red_bop S (cbop S csg) r (ceq S csg) (rep_idem _ _ _ req)
;  ceqv  := reduced_eqv_proofs S (ceq S csg) r (cbop S csg) (ceqv S csg) req
;  csgp  := reduced_commutative_semigroup_proofs S (ceq S csg) r (cbop S csg) (ceqv S csg) (csgp S csg) req rb
|}.
End Reduced_Semigroup_Direct.
