Require Export Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.   
Require Import CAS.basic. 
Require Import CAS.properties. 
Require Import CAS.structures.
Require Import CAS.predicate_reduce.
Require Import CAS.reduce_annihilators_redux.
Require Import CAS.reduce_annihilators_semigroup. 


Definition dioid_rap_proofs (S T : Type)
           (eqS : brel S) (eqT : brel T)
           (eqvS : eqv_proofs S eqS) (eqvT : eqv_proofs T eqT)                                  
           (addS mulS : binary_op S) (addT mulT : binary_op T)
           (dS : dioid_rap_proofs S) (dT : dioid_rap_proofs T)
           (zeroS : S) (zeroT : T)
           (oneS : S)  (oneT : T)
:=
let refS       := eqv_reflexive S eqS eqvS in
let symS       := eqv_symmetric S eqS eqvS in
let tranS      := eqv_transitive S eqS eqvS in
let refT       := eqv_reflexive T eqT eqvT in
let symT       := eqv_symmetric T eqT eqvT in
let tranT      := eqv_transitive T eqT eqvT in
let aS         := zeroS in
let aT         := zeroT in
let addS_cong  := in
let addT_cong  := in
let mulS_cong  := in
let mulT_cong  := in
let aS_is_addS_id := in 
let aT_is_addT_id := in 
let aS_is_mulS_ann := in 
let aT_is_mulT_ann := in 
let ssquare_addS := in 
let ssquare_mulT := in 
let sdiv_addS := in 
let sdiv_mulT := in 
let ldist := dioid_left_distributive _ _ _ _ _ _ dS in
let rdist := dioid_right_distributive _ _ _ _ _ _ dS in   
{|  
  dioid_left_distributive  :=
; dioid_right_distributive := bop_rap_add_mul_right_distributive S T eqS eqT refS symS tranS refT symT tranT aS aT addS addT addS_cong addT_cong mulS mulT mulS_cong mulT_cong aS_is_addS_id aT_is_addT_id aS_is_mulS_ann aT_is_mulT_ann ssquare_addS ssquare_mulT  sdiv_addS sdiv_mulT  rdistS rdistT 
; dioid_zero_is_mul_ann    : bop_is_ann S eq mul zero
; dioid_one_is_add_ann     : bop_is_ann S eq add one
|}.

Definition dioid_rap (S T : Type) : dioid S ->  dioid T -> dioid (S * T) 
:= λ dS dT,
let eqS      := dioid_eq S dS in
let eqT      := dioid_eq T dT in
let eqvS     := dioid_eqv S dS in
let eqvT     := dioid_eqv T dT in
let addS     := dioid_add S dS in
let addT     := dioid_add T dT in
let mulS     := dioid_mul S dS in
let mukT     := dioid_mul T dT in
let addS_pfs := dioid_add_pfs S dS in
let addT_pfs := dioid_add_pfs T dT in
let mulS_pfs := dioid_mul_pfs S dS in
let mulT_pfs := dioid_mul_pfs T dT in
let zeroS    := dioid_zero S dS in
let zeroT    := dioid_zero T dT in
let oneS     := dioid_zero S dS in
let oneT     := dioid_zero T dT in  
{|
    dioid_eq         := brel_reduce (uop_rap S T eqS eqT iS iT) (brel_product eqS eqT)
  ; dioid_add        := bop_rap_add S T eqS eqT zeroS oneT oneS addT 
  ; dioid_mul        := bop_rap_mul S T eqS eqT oneS oneT mulS mulT 
  ; dioid_zero       := (zeroS, zeroT)
  ; dioid_one        := (oneS, oneT)
  ; diode_eqv        := reduce_rap_eqv_proofs S T eqS eqT eqvS eqvT aS aT
  ; diode_add_pfs    := rap_add_product_sg_CMA_proofs S T eqS eqT eqvS eqvT oneS oneT addS addT addS_pfs addT_pfs
  ; diode_mul_pfs    := rap_mul_product_sg_MA_proofs S T eqS eqT eqvS eqvT oneS oneT addS addT addT_pfs addT_pfs
  ; dioid_pfs        := dioid_rap_proofs ??? 
|}.