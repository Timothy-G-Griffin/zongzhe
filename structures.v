Require Import CAS.basic. 
Require Import CAS.properties. 


Record eqv_proofs (S : Type) (eq : brel S) :=
{
  eqv_reflexive      : brel_reflexive S eq            
; eqv_transitive     : brel_transitive S eq           
; eqv_symmetric      : brel_symmetric S eq
; eqv_witness        : S                                      
}.

Record semigroup_proofs (S: Type) (eq : brel S) (b : binary_op S) := 
{
  sg_associative   : bop_associative S eq b
; sg_congruence    : bop_congruence S eq b
; sg_commutative_d : bop_commutative_decidable S eq b                                      
}.

Record commutative_semigroup_proofs (S: Type) (eq : brel S) (b : binary_op S) := 
{
  csg_associative   : bop_associative S eq b
; csg_congruence    : bop_congruence S eq b
; csg_commutative   : bop_commutative S eq b                                      
}.

Record commutative_semigroup_with_ann_proofs (S: Type) (eq : brel S) (b : binary_op S) (ann : S) := 
{
  csgwa_associative   : bop_associative S eq b
; csgwa_congruence    : bop_congruence S eq b
; csgwa_commutative   : bop_commutative S eq b
; csgwa_is_ann        : bop_is_ann S eq b ann
}.

(* this captures our normal understanding of a semigroup over 
   a carrier set S. 
*) 
Record semigroup (S : Type) :=
{
   eq   : brel S      
;  bop  : binary_op S
;  eqv  : eqv_proofs S eq               
;  sgp  : semigroup_proofs S eq bop
}.

Record commutative_semigroup (S : Type) :=
{
   ceq   : brel S      
;  cbop  : binary_op S
;  ceqv  : eqv_proofs S ceq               
;  csgp  : commutative_semigroup_proofs S ceq cbop
}.

Record commutative_semigroup_with_ann (S : Type) :=
{
   ceqa   : brel S      
;  cbopa  : binary_op S
;  canna  : S
;  ceqva  : eqv_proofs S ceqa               
;  csgpa  : commutative_semigroup_with_ann_proofs S ceqa cbopa canna
}.


(* bundle reduction properties in a record
*) 

Record reduction_eqv_proofs (S : Type) (eq : brel S) (r : unary_op S) :=
{
  rep_cong  : uop_congruence S eq r 
; rep_idem  : uop_idempotent S eq r 
}.

Record reduction_bop_proofs (S : Type) (eq : brel S) (r : unary_op S) (b : binary_op S) :=
{
  rb_left  : bop_left_uop_invariant S eq b r
; rb_right : bop_right_uop_invariant S eq b r
}.


(* There is a problem with the approach of the last section. 
   We have lost the reduction r --- but this is needed for 
   injecting elements of S into the reduced subset of S. 
   This section introduces a new structure, rsemigroup, that 
   remembers r. 

   rsemigroups are just like semigroups, but the come with 
   a representation function r_rep : S -> S 
   and some proofs (r_rpv) about r_rep
*)


Record rsemigroup (S : Type) :=
{
   r_eq   : brel S
;  r_rep  : unary_op S                      
;  r_bop  : binary_op S
;  r_eqv  : eqv_proofs S r_eq
;  r_rpv  : reduction_eqv_proofs S r_eq r_rep                        
;  r_sgp  : semigroup_proofs S r_eq r_bop
}.

Record commutative_rsemigroup (S : Type) :=
{
   cr_eq   : brel S
;  cr_rep  : unary_op S                      
;  cr_bop  : binary_op S
;  cr_eqv  : eqv_proofs S cr_eq
;  cr_rpv  : reduction_eqv_proofs S cr_eq cr_rep                        
;  cr_sgp  : commutative_semigroup_proofs S cr_eq cr_bop
}.

(* these translations just forget the rep function and its associated proofs *)

Definition rsemigroup_to_semigroup (S : Type): rsemigroup S -> semigroup S
:= λ rsg,
{|    
   eq   := r_eq S rsg 
;  bop  := r_bop S rsg 
;  eqv  := r_eqv S rsg 
;  sgp  := r_sgp S rsg
|}.

Definition commutative_rsemigroup_to_commutative_semigroup (S : Type): commutative_rsemigroup S -> commutative_semigroup S
:= λ crsg,
{|    
   ceq   := cr_eq S crsg 
;  cbop  := cr_bop S crsg 
;  ceqv  := cr_eqv S crsg 
;  csgp  := cr_sgp S crsg
|}.

