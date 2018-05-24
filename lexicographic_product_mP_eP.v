Require Import CAS.basic.
Require Import CAS.properties. 
Require Import CAS.structures.
Require Import CAS.product.
Require Import CAS.facts.
Require Import CAS.brel_reduce.
Require Import CAS.bop_full_reduce.
Require Import CAS.predicate_reduce.
Require Import CAS.reduce_annihilators.
Require Import CAS.reduction_theory.
Require Import CAS.min_plus_ceiling_reduction.
Require Import CAS.elementary_path.

Section Lexicographic_product_minPlusWithCeiling_ElementaryPath.


Variable ceiling : nat.
Variable c : cas_constant.
Close Scope nat.
Definition T := cas_constant + list nat.

Definition min_plus_ceiling_dioid := min_plus_dioid ceiling.
Definition elementary_path_bioid := min_app_non_distributive_dioid brel_eq_nat_reflexive brel_eq_nat_symmetric brel_eq_nat_transitive c.

Definition add1 := csdioid_add nat min_plus_ceiling_dioid.
Definition mul1 := csdioid_mul nat min_plus_ceiling_dioid.
Definition add2 := sbioid_add T elementary_path_bioid.
Definition mul2 := sbioid_mul T elementary_path_bioid.

Definition eqN := csdioid_eq nat min_plus_ceiling_dioid.
Definition eqT := sbioid_eq T elementary_path_bioid.

Definition M := nat * T.

Definition eqM : brel M := brel_product eqN eqT.


Definition add :binary_op M := bop_llex eqN add1 add2.
Definition mul :binary_op M:= bop_product mul1 mul2.

(* Definition N := cas_constant + M.

Definition addN : binary_op N := bop_add_id add c.
Definition mulN : binary_op N := bop_add_ann mul c. *)

Open Scope nat.
Definition zero1 : nat := ceiling.
Definition one1  : nat := 0.
Definition zero2 : T := inl c.
Definition one2  : T := inr nil.
Definition zero  : M := (zero1,zero2).
Definition one   : M := (one1,one2).

Definition P := reduce_annihilators.P nat T eqN eqT zero1 zero2.
Definition P_congruence := reduce_annihilators.P_congruence.
Definition P_true := reduce_annihilators.P_true.
Definition uop_rap : unary_op M := reduce_annihilators.uop_rap nat T eqN eqT zero1 zero2.
Definition brel_eq_M :brel M := brel_reduce uop_rap eqM. 

Definition bop_rap_add : binary_op M := bop_fpr zero P add.
Definition bop_rap_mul : binary_op M := bop_fpr zero P mul.

Lemma brel_eq_M_reflexive : brel_reflexive M brel_eq_M.
Proof. apply brel_reduce_reflexive.
    apply brel_product_reflexive; auto.
    apply min_plus_ceiling_reduction.brel_reduce_nat_reflexive.
    apply elementary_path.brel_reduce_list_const_reflexive.
    apply brel_eq_nat_reflexive.
Qed.   

Lemma brel_eq_M_symmetric : brel_symmetric M brel_eq_M.
Proof. apply brel_reduce_symmetric.
    apply brel_product_symmetric; auto.
    apply min_plus_ceiling_reduction.brel_reduce_nat_symmetric.
    apply elementary_path.brel_reduce_list_const_symmetric.
    apply brel_eq_nat_reflexive.
    apply brel_eq_nat_symmetric.
    apply brel_eq_nat_transitive.
Qed.  

Lemma brel_eq_M_transitive : brel_transitive M brel_eq_M.
Proof. apply brel_reduce_transitive.
    apply brel_product_transitive; auto.
    apply min_plus_ceiling_reduction.brel_reduce_nat_transitive.
    apply elementary_path.brel_reduce_list_const_transitive.
    apply brel_eq_nat_reflexive.
    apply brel_eq_nat_symmetric.
    apply brel_eq_nat_transitive.
Qed.  

Lemma brel_eq_M_congruence : brel_congruence M brel_eq_M brel_eq_M.
Proof. apply brel_reduce_congruence; auto. 
    apply brel_product_congruence; auto. 
    apply min_plus_ceiling_reduction.brel_reduce_nat_congruence.
    apply elementary_path.brel_reduce_list_const_congruence.
    apply brel_eq_nat_reflexive.
    apply brel_eq_nat_symmetric.
    apply brel_eq_nat_transitive.
Qed.  

       
Lemma bop_rap_mul_associative :  bop_associative M brel_eq_M bop_rap_mul.
Proof.
Admitted.


Lemma bop_rap_mul_congruence : bop_congruence M brel_eq_M bop_rap_mul.
Proof. apply bop_full_reduce_congruence; auto.
       apply uop_predicate_reduce_congruence; auto.
       apply brel_product_reflexive; auto.
       apply min_plus_ceiling_reduction.brel_reduce_nat_reflexive; auto.
       apply elementary_path.brel_reduce_list_const_reflexive;auto.
       apply brel_eq_nat_reflexive; auto.
       unfold pred_congruence. apply P_congruence.
       apply min_plus_ceiling_reduction.brel_reduce_nat_symmetric; auto.
       apply min_plus_ceiling_reduction.brel_reduce_nat_transitive; auto.
       apply elementary_path.brel_reduce_list_const_symmetric;auto.
       apply brel_eq_nat_reflexive; auto.
       apply brel_eq_nat_symmetric.
       apply brel_eq_nat_transitive.
       apply elementary_path.brel_reduce_list_const_transitive;auto.
       apply brel_eq_nat_reflexive; auto.
       apply brel_eq_nat_symmetric.
       apply brel_eq_nat_transitive.
       apply bop_product_congruence; auto.
       apply min_plus_ceiling_reduction.bop_nat_plus_congruence.
       apply elementary_path.bop_list_app_congruence.
       apply brel_eq_nat_reflexive.
        apply brel_eq_nat_symmetric.
        apply brel_eq_nat_transitive.
Qed.

Lemma bop_rap_mul_not_commutative : bop_not_commutative M brel_eq_M bop_rap_mul.
Proof.
Admitted.

Lemma bop_rap_mul_commutative_decidable : bop_commutative_decidable M brel_eq_M bop_rap_mul.
Proof. right. apply bop_rap_mul_not_commutative.
Qed.

Lemma bop_is_id_add_zero : bop_is_id M eqM add zero.
Proof.
Admitted.

Lemma bop_is_ann_add_one : bop_is_ann M eqM add one.
Proof.
Admitted.

Lemma bop_is_id_mul_one : bop_is_id M eqM mul one.
Proof.
Admitted.

Lemma bop_is_ann_mul_zero : bop_is_ann M eqM mul zero.
Proof.
Admitted.

Definition eqv_proofs_eq_T : eqv_proofs M brel_eq_M
:= {| 
     eqv_reflexive   := brel_eq_M_reflexive
   ; eqv_transitive  := brel_eq_M_transitive
   ; eqv_symmetric   := brel_eq_M_symmetric
   ; eqv_congruence  := brel_eq_M_congruence
   ; eqv_witness     := zero
|}. 


Definition min_proofs  : 
commutative_selective_semigroup_proofs T (brel_reduce uop_list brel_list_const) bop_list_min
:= {|
  cssg_associative   := bop_list_min_associative
; cssg_congruence    := bop_list_min_congruence
; cssg_commutative   := bop_list_min_commutative
; cssg_selective     := bop_list_min_selective                                        
|}.

Definition app_proofs: 
semigroup_proofs M brel_eq_M bop_rap_mul
:= {|
sg_associative   := bop_rap_mul_associative
  ; sg_congruence    := bop_rap_mul_congruence
; sg_commutative_d    := bop_rap_mul_commutative_decidable                                                
|}.


Definition min_app_non_distributive_dioid_proofs : 
bioid_proof T (brel_reduce uop_list brel_list_const) bop_list_min bop_list_app (inl c) (inr nil)
:= {|  
bioid_left_distributive_decidable := bop_left_distributive_min_app_decidable
; bioid_right_distributive_decidable := bop_right_distributive_min_app_decidable
; bioid_zero_is_add_id     := bop_is_id_min
; bioid_one_is_mul_id      := bop_is_id_app 
; bioid_zero_is_mul_ann     := bop_is_ann_app
; bioid_one_is_add_ann    := bop_is_ann_min
|}.


Definition min_app_non_distributive_dioid : selective_bioid T
:= {|
    sbioid_eq         := brel_reduce uop_list brel_list_const
  ; sbioid_add        := bop_list_min
  ; sbioid_mul        := bop_list_app                                 
  ; sbioid_zero       := inl c
  ; sbioid_one        := inr nil
  ; sbioid_eqv        := eqv_proofs_eq_T
  ; sbioid_add_pfs    := min_proofs
  ; sbioid_mul_pfs    := app_proofs
  ; sbioid_pfs        := min_app_non_distributive_dioid_proofs
|}.

End Lexicographic_product_minPlusWithCeiling_ElementaryPath.