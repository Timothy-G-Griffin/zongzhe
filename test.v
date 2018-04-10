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

Section Test.

  Variable S : Type.  
  Variable eqS : brel S.
  Variable refS : brel_reflexive S eqS.
  Variable symS : brel_symmetric S eqS.
  Variable tranS : brel_transitive S eqS.
  Variable eqS_cong : brel_congruence S eqS eqS.           
  Variable iS : S.
  Variable aS : S.

  Variable addS : binary_op S.
  Variable cong_addS : bop_congruence S eqS addS.
  Variable ass_addS : bop_associative S eqS addS.
  Variable com_addS : bop_commutative S eqS addS.
  Variable sel_addS : bop_selective S eqS addS.

  Variable mulS : binary_op S.
  Variable cong_mulS : bop_congruence S eqS mulS.
  Variable ass_mulS : bop_associative S eqS mulS.
  Variable com_mulS : bop_commutative S eqS mulS.
  Variable sel_mulS : bop_selective S eqS mulS.

  Variable is_idAddS : bop_is_id S eqS addS iS.
  Variable is_annAddS : bop_is_ann S eqS addS aS.

  Variable is_idMulS : bop_is_id S eqS mulS aS.
  Variable is_annMulS : bop_is_ann S eqS mulS iS.

  
  Variable no_idS_div_add : bop_self_square S eqS addS iS. (* ∀ a b : S,  eqS (addS a b) aS = true -> (eqS a aS = true) * (eqS b aS = true).  *) 
  Variable no_idS_div_mul : bop_self_square S eqS mulS aS.

  Variable no_annS_div_add : bop_self_divisor S eqS addS aS. (* ∀ a b : S,  eqS (mulS a b) aS = true -> (eqS a aS = true) + (eqS b aS = true).  *) 
  Variable no_annS_div_mul : bop_self_divisor S eqS mulS iS.

  Definition Padd : S -> bool := λ s, (eqS s aS).
  Definition Pmul : S -> bool := λ s, (eqS s iS).
  Definition uop_addS : unary_op S := uop_predicate_reduce aS Padd.
  Definition bop_fpr_addS : binary_op S := bop_fpr aS Padd addS .
  Definition uop_mulS : unary_op S := uop_predicate_reduce iS Pmul.
  Definition bop_fpr_mulS : binary_op S := bop_fpr iS Pmul mulS .
  Lemma Padd_true : Padd aS = true. Proof. compute; auto. Qed.
  Lemma Pmul_true : Pmul iS = true. Proof. compute; auto. Qed.
  Lemma Padd_cong : ∀ (p1 p2 : S), eqS p1 p2 = true -> Padd p1 = Padd p2.
  Proof. intros p1 p2 H. compute. apply eqS_cong; auto. Qed.
  Lemma Padd_false_preservation : ∀ (p1 p2 : S), Padd p1 = false -> Padd p2 = false -> Padd (addS p1 p2) = false.
  Proof. intros p1 p2 H1 H2. compute. compute in H1,H2. compute in no_annS_div_add.
        assert (H := no_annS_div_add p1 p2).
        admit.
        Admitted.

  Lemma idProof : bop_is_id S (brel_reduce (uop_predicate_reduce aS Padd) eqS) (bop_fpr aS Padd addS) iS.
  Proof. compute; intro s.
         case_eq(eqS iS aS); intro K.
         case_eq(eqS s aS); intro L.
         assert (J:= is_annAddS aS). destruct J as [J _]. rewrite J. rewrite (refS aS). auto.
         assert (A:= is_annAddS s). assert (B := is_idAddS s).
       destruct A as [A _]; destruct B as [B _]. apply symS in A.
       assert (M := brel_transitive_f2 S eqS symS tranS (addS iS s) s aS B L).
       assert (N := brel_transitive_f1 S eqS symS tranS (addS iS s) aS (addS aS s) M A).
       assert (R := cong_addS iS s aS s K (refS s)). rewrite N in R. discriminate R.
       case_eq(eqS s aS); intro L.
       assert (J:= is_annAddS iS). destruct J as [Jl Jr]. rewrite Jl,Jr. rewrite (refS aS). auto.
       assert (J:= is_idAddS s). destruct J as [Jl Jr].
       assert (A := brel_transitive_f2 S eqS symS tranS (addS iS s) s aS Jl L). rewrite A. rewrite A.
       assert (B := brel_transitive_f2 S eqS symS tranS (addS s iS) s aS Jr L). rewrite B. rewrite B. rewrite Jl,Jr. auto.
  Qed.



  Lemma annProof : bop_is_ann S (brel_reduce (uop_predicate_reduce aS Padd) eqS) (bop_fpr aS Padd addS) aS.
  Proof. compute. intro s. rewrite (refS aS).
        case_eq(eqS s aS); intro K.
        assert (J:= is_annAddS aS). destruct J as [J _]. rewrite J. rewrite (refS aS). auto.
        assert (J:= is_annAddS s). destruct J as [Jl Jr]. rewrite Jl,Jr. rewrite (refS aS). auto.
  Qed.

  Record sg_CSMA_proofs (S: Type) (eq : brel S) (b : binary_op S) (id : S) (ann : S) := 
{
  sg_CSMA_associative   : bop_associative S eq b
; sg_CSMA_congruence    : bop_congruence S eq b
; sg_CSMA_commutative   : bop_commutative S eq b
; sg_CSMA_selective     : bop_selective S eq b                                          
; sg_CSMA_is_id         : bop_is_id S eq b id
; sg_CSMA_is_ann        : bop_is_ann S eq b ann                             
}.

Check bop_associative_fpr_ann_v2 S Padd eqS refS aS addS Padd_true Padd_cong Padd_false_preservation cong_addS is_annAddS ass_addS. 
Check uop_predicate_reduce_congruence S Padd eqS refS aS Padd_cong.
Check bop_full_reduce_congruence S eqS (uop_predicate_reduce aS Padd) addS (uop_predicate_reduce_congruence S Padd eqS refS aS Padd_cong) cong_addS.
(* Check bop_fpr_congruence S Padd eqS refS aS addS Padd_cong cong_addS. *)
Check bop_fpr_selective S Padd eqS refS aS addS Padd_true Padd_cong Padd_false_preservation is_annAddS sel_addS.
Check bop_full_reduce_commutative S eqS (uop_predicate_reduce aS Padd) addS (uop_predicate_reduce_congruence S Padd eqS refS aS Padd_cong) com_addS.
Check bop_full_reduce_exists_id S eqS (uop_predicate_reduce aS Padd) addS refS tranS
(uop_predicate_reduce_congruence S Padd eqS refS aS Padd_cong) (uop_predicate_reduce_idempoent S Padd eqS refS aS) cong_addS.

Definition add_CSMA_proofs : sg_CSMA_proofs S (brel_reduce (uop_predicate_reduce aS Padd) eqS) bop_fpr_addS iS aS :=
{|
sg_CSMA_associative   := bop_associative_fpr_ann_v2 S Padd eqS refS aS addS Padd_true Padd_cong Padd_false_preservation cong_addS is_annAddS ass_addS
; sg_CSMA_congruence    := bop_full_reduce_congruence S eqS (uop_predicate_reduce aS Padd) addS (uop_predicate_reduce_congruence S Padd eqS refS aS Padd_cong) cong_addS
; sg_CSMA_commutative   := bop_full_reduce_commutative S eqS (uop_predicate_reduce aS Padd) addS (uop_predicate_reduce_congruence S Padd eqS refS aS Padd_cong) com_addS
; sg_CSMA_selective     := bop_fpr_selective S Padd eqS refS aS addS Padd_true Padd_cong Padd_false_preservation is_annAddS sel_addS                                          
; sg_CSMA_is_id         := idProof
; sg_CSMA_is_ann        := annProof 
|}.

Record sg_CSMA (S : Type) := {
  sg_CSMA_eq         : brel S  
; sg_CSMA_bop        : binary_op S
; sg_CSMA_id         : S
; sg_CSMA_ann        : S
; sg_CSMA_eqv        : eqv_proofs S sg_CSMA_eq
; sg_CSMA_pfs        : sg_CSMA_proofs S sg_CSMA_eq sg_CSMA_bop sg_CSMA_id sg_CSMA_ann
}.

Definition s_eqv_proof : eqv_proofs S eqS :=
{|
eqv_reflexive      := refS         
; eqv_transitive     := tranS         
; eqv_symmetric      := symS
; eqv_congruence     := eqS_cong                                      
; eqv_witness        := iS  
|}.

Definition add_CSMA : sg_CSMA S :=
{|
sg_CSMA_eq         := eqS  
; sg_CSMA_bop        := addS
; sg_CSMA_id         := iS
; sg_CSMA_ann        := aS
; sg_CSMA_eqv        := s_eqv_proof
; sg_CSMA_pfs        := add_CSMA_proofs
|}.


Definition mul_CSMA_proofs : sg_CSMA_proofs S eqS mulS aS iS :=
{|
sg_CSMA_associative   := ass_mulS
; sg_CSMA_congruence    := cong_mulS
; sg_CSMA_commutative   := com_mulS
; sg_CSMA_selective     := sel_mulS                                          
; sg_CSMA_is_id         := is_idMulS
; sg_CSMA_is_ann        := is_annMulS  
|}.

Definition mul_CSMA : sg_CSMA S :=
{|
sg_CSMA_eq         := eqS  
; sg_CSMA_bop        := mulS
; sg_CSMA_id         := aS
; sg_CSMA_ann        := iS
; sg_CSMA_eqv        := s_eqv_proof
; sg_CSMA_pfs        := mul_CSMA_proofs
|}.



End Test.



