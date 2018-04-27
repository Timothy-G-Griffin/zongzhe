Require Import CAS.basic. 
Require Import CAS.properties. 

Record eqv_proofs (S : Type) (eq : brel S) :=
{
  eqv_reflexive      : brel_reflexive S eq            
; eqv_transitive     : brel_transitive S eq           
; eqv_symmetric      : brel_symmetric S eq
; eqv_congruence     : brel_congruence S eq eq                                      
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


Record commutative_selective_semigroup_proofs (S: Type) (eq : brel S) (b : binary_op S) := 
{
  cssg_associative   : bop_associative S eq b
; cssg_congruence    : bop_congruence S eq b
; cssg_commutative   : bop_commutative S eq b
; cssg_selective     : bop_selective S eq b                                                                            
}.

Record commutative_semigroup_with_ann_proofs (S: Type) (eq : brel S) (b : binary_op S) (ann : S) := 
{
  csgwa_associative   : bop_associative S eq b
; csgwa_congruence    : bop_congruence S eq b
; csgwa_commutative   : bop_commutative S eq b
; csgwa_is_ann        : bop_is_ann S eq b ann
; csgwa_div           : bop_self_divisor S eq b ann                                         
}.

Record commutative_semigroup_with_id_proofs (S: Type) (eq : brel S) (b : binary_op S) (id : S) := 
{
  csgwi_associative   : bop_associative S eq b
; csgwi_congruence    : bop_congruence S eq b
; csgwi_commutative   : bop_commutative S eq b
; csgwi_is_id         : bop_is_id S eq b id
; csgwi_squ           : bop_self_square S eq b id                                        
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

Record commutative_semigroup_with_id (S : Type) :=
{
   ceqi   : brel S      
;  cbopi  : binary_op S
;  cidi   : S
;  ceqvi  : eqv_proofs S ceqi               
;  csgpi  : commutative_semigroup_with_id_proofs S ceqi cbopi cidi
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


(* C = commutative
   S = selective 
   M = monoid 
   A = with annihilator 
 *)

Record sg_MA_proofs (S: Type) (eq : brel S) (b : binary_op S) (id : S) (ann : S) := 
{
  sg_MA_associative   : bop_associative S eq b
; sg_MA_congruence    : bop_congruence S eq b
; sg_MA_is_id         : bop_is_id S eq b id
; sg_MA_squ           : bop_self_square S eq b id                                                                           
; sg_MA_is_ann        : bop_is_ann S eq b ann
; sg_MA_div           : bop_self_divisor S eq b ann                                                                                                           }.

Record sg_CMA_proofs (S: Type) (eq : brel S) (b : binary_op S) (id : S) (ann : S) := 
{
  sg_CMA_associative   : bop_associative S eq b
; sg_CMA_congruence    : bop_congruence S eq b
; sg_CMA_commutative   : bop_commutative S eq b
; sg_CMA_is_id         : bop_is_id S eq b id
; sg_CMA_squ           : bop_self_square S eq b id                                                                           
; sg_CMA_is_ann        : bop_is_ann S eq b ann
; sg_CMA_div           : bop_self_divisor S eq b ann
; sg_CMA_one_not_zero  : eq ann id = false 
}.

Record sg_CSMA_proofs (S: Type) (eq : brel S) (b : binary_op S) (id : S) (ann : S) := 
{
  sg_CSMA_associative   : bop_associative S eq b
; sg_CSMA_congruence    : bop_congruence S eq b
; sg_CSMA_commutative   : bop_commutative S eq b
; sg_CSMA_selective     : bop_selective S eq b                                          
; sg_CSMA_is_id         : bop_is_id S eq b id
; sg_CSMA_is_ann        : bop_is_ann S eq b ann                             
}.


Record sg_CSMA (S : Type) := {
  sg_CSMA_eq         : brel S  
; sg_CSMA_bop        : binary_op S
; sg_CSMA_id         : S
; sg_CSMA_ann        : S
; sg_CSMA_eqv        : eqv_proofs S sg_CSMA_eq
; sg_CSMA_pfs        : sg_CSMA_proofs S sg_CSMA_eq sg_CSMA_bop sg_CSMA_id sg_CSMA_ann
}.


Record dioid_proofs (S: Type) (eq : brel S) (add mul : binary_op S) (zero : S) (one : S) :=
{  
  dioid_left_distributive  : bop_left_distributive S eq add mul
; dioid_right_distributive : bop_right_distributive S eq add mul
; dioid_zero_is_add_id     : bop_is_id S eq add zero
; dioid_one_is_mul_id      : bop_is_id S eq mul one                                                      
; dioid_zero_is_mul_ann    : bop_is_ann S eq mul zero
; dioid_one_is_add_ann     : bop_is_ann S eq add one
}.


Record dioid (S : Type) := {
    dioid_eq         : brel S  
  ; dioid_add        : binary_op S
  ; dioid_mul        : binary_op S                                   
  ; dioid_zero       : S
  ; dioid_one        : S
  ; diode_eqv        : eqv_proofs S dioid_eq
  ; diode_add_pfs    : commutative_semigroup_proofs S dioid_eq dioid_add 
  ; diode_mul_pfs    : semigroup_proofs S dioid_eq dioid_mul 
  ; dioid_pfs        : dioid_proofs S dioid_eq dioid_add dioid_mul dioid_zero dioid_one
}.

Record commutative_dioid (S : Type) := {
    cdioid_eq         : brel S  
  ; cdioid_add        : binary_op S
  ; cdioid_mul        : binary_op S                                   
  ; cdioid_zero       : S
  ; cdioid_one        : S
  ; cdiode_eqv        : eqv_proofs S cdioid_eq
  ; cdiode_add_pfs    : commutative_semigroup_proofs S cdioid_eq cdioid_add 
  ; cdiode_mul_pfs    : commutative_semigroup_proofs S cdioid_eq cdioid_mul 
  ; cdioid_pfs        : dioid_proofs S cdioid_eq cdioid_add cdioid_mul cdioid_zero cdioid_one
}.


Record commutative_selective_dioid (S : Type) := {
    csdioid_eq         : brel S  
  ; csdioid_add        : binary_op S
  ; csdioid_mul        : binary_op S                                   
  ; csdioid_zero       : S
  ; csdioid_one        : S
  ; csdiode_eqv        : eqv_proofs S csdioid_eq
  ; csdiode_add_pfs    : commutative_selective_semigroup_proofs S csdioid_eq csdioid_add 
  ; csdiode_mul_pfs    : commutative_semigroup_proofs S csdioid_eq csdioid_mul 
  ; csdioid_pfs        : dioid_proofs S csdioid_eq csdioid_add csdioid_mul csdioid_zero csdioid_one
}.


