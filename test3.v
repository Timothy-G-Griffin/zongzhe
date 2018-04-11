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

  Definition P : S -> bool := λ s, (eqS s iS).
  Definition uop_red : unary_op S := uop_predicate_reduce aS P.
  Definition bop_fpr_addS : binary_op S := bop_fpr iS P addS .
  Definition bop_fpr_mulS : binary_op S := bop_fpr iS P mulS .
  Lemma P_true : P iS = true. Proof. compute; auto. Qed.
  Lemma P_cong : ∀ (p1 p2 : S), eqS p1 p2 = true -> P p1 = P p2.
  Proof. intros p1 p2 H. compute. apply eqS_cong; auto. Qed.
  Lemma P_false_preservation : ∀ (p1 p2 : S), P p1 = false -> P p2 = false -> P (addS p1 p2) = false.
  Proof. intros p1 p2 H1 H2. compute. compute in H1,H2. compute in no_idS_div_add.
        assert (H := no_idS_div_add p1 p2).
        case_eq(eqS (addS p1 p2) iS); intro K.
        assert (L := H K). destruct L.
        rewrite H1 in e. discriminate. auto.
  Qed.

  Lemma idProof : bop_is_id S (brel_reduce (uop_predicate_reduce aS P) eqS) (bop_fpr aS P addS) iS.
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



  Lemma annProof : bop_is_ann S (brel_reduce (uop_predicate_reduce aS P) eqS) (bop_fpr aS P addS) aS.
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

Definition add_CSMA_proofs : sg_CSMA_proofs S (brel_reduce (uop_predicate_reduce aS P) eqS) bop_fpr_addS iS aS :=
{|
sg_CSMA_associative   := bop_associative_fpr_ann_v2 S P eqS refS aS addS P_true P_cong P_false_preservation cong_addS is_annAddS ass_addS
; sg_CSMA_congruence    := bop_full_reduce_congruence S eqS (uop_predicate_reduce aS P) addS (uop_predicate_reduce_congruence S P eqS refS aS P_cong) cong_addS
; sg_CSMA_commutative   := bop_full_reduce_commutative S eqS (uop_predicate_reduce aS P) addS (uop_predicate_reduce_congruence S P eqS refS aS P_cong) com_addS
; sg_CSMA_selective     := bop_fpr_selective S P eqS refS aS addS P_true P_cong P_false_preservation is_annAddS sel_addS                                          
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

Lemma brel_reduce_reflexive : brel_reflexive S (brel_reduce (uop_predicate_reduce aS P) eqS). 
  Proof. intros s. compute.
         case_eq(eqS s aS); intro J1.
         rewrite refS. auto. 
         rewrite refS. auto.         
  Qed.

  Lemma brel_reduce_symmetric : brel_symmetric S (brel_reduce (uop_predicate_reduce aS P) eqS).  
  Proof. intros s1 s2. compute.
         case_eq(eqS s1 aS); intro J1; case_eq(eqS s2 aS); intro J2; auto.
  Qed.           


  Lemma brel_reduce_transitive : brel_transitive S (brel_reduce (uop_predicate_reduce aS P) eqS). 
  Proof. intros s1 s2 s3. compute.
         case_eq(eqS s1 aS); intro J1; case_eq(eqS s2 aS); intro J2; case_eq(eqS s3 aS); intro J3; auto; intros M N. 
         assert (L := tranS _ _ _ M N); auto.      
         assert (L := tranS _ _ _ M N); auto.
         assert (L := tranS _ _ _ M N); auto.
         assert (L := tranS _ _ _ M N); auto.
  Qed.

    Lemma brel_reduce_congruence_add :  brel_congruence S (brel_reduce (uop_predicate_reduce aS P) eqS) (brel_reduce (uop_predicate_reduce aS P) eqS).
    Proof. apply brel_reduce_congruence. exact eqS_cong.
    Qed.


Definition s_eqv_proof : eqv_proofs S (brel_reduce (uop_predicate_reduce aS P) eqS) :=
{|
eqv_reflexive      := brel_reduce_reflexive         
; eqv_transitive     := brel_reduce_transitive         
; eqv_symmetric      := brel_reduce_symmetric
; eqv_congruence     := brel_reduce_congruence_add                                      
; eqv_witness        := iS  
|}.

Definition add_CSMA : sg_CSMA S :=
{|
sg_CSMA_eq         := (brel_reduce (uop_predicate_reduce aS P) eqS)
; sg_CSMA_bop        := bop_fpr_addS
; sg_CSMA_id         := iS
; sg_CSMA_ann        := aS
; sg_CSMA_eqv        := s_eqv_proof
; sg_CSMA_pfs        := add_CSMA_proofs
|}.


Record sg_MA_proofs (S: Type) (eq : brel S) (b : binary_op S) (id : S) (ann : S) := 
{
  sg_MA_associative   : bop_associative S eq b
; sg_MA_congruence    : bop_congruence S eq b
; sg_MA_is_id         : bop_is_id S eq b id
; sg_MA_is_ann        : bop_is_ann S eq b ann                             
}.

Lemma P_false_preservation_mul : ∀ (p1 p2 : S), P p1 = false -> P p2 = false -> P (mulS p1 p2) = false.
  Proof. intros p1 p2 H1 H2. compute. compute in H1,H2. compute in no_annS_div_mul.
        assert (H := no_idS_div_mul p1 p2).
        case_eq(eqS (mulS p1 p2) aS); intro K.
        assert (L := H K). destruct L.
        rewrite H1 in e. discriminate. auto.
  Qed.

  Lemma idProof_mul : bop_is_id S (brel_reduce (uop_predicate_reduce aS P) eqS) (bop_fpr aS P mulS) aS.
  Proof. compute; intro s. rewrite (refS aS).
         case_eq (eqS s aS); intro K.
         assert (J:= is_idMulS aS). destruct J as [J _]. rewrite J. rewrite (refS aS). auto.
         assert (A:= is_idMulS s). destruct A as [Al Ar].
         assert (B := brel_transitive_f2 S eqS symS tranS (mulS aS s) s aS Al K). rewrite B. rewrite B. 
         assert (C := brel_transitive_f2 S eqS symS tranS (mulS s aS) s aS Ar K). rewrite C. rewrite C. auto.
  Qed.

  Lemma annProof_mul : bop_is_ann S (brel_reduce (uop_predicate_reduce aS P) eqS) (bop_fpr aS P mulS) iS.
  Proof. compute. intro s.
         case_eq(eqS iS aS); intro K.
         case_eq(eqS s aS); intro L.
         assert (J:= is_idMulS aS). destruct J as [J _]. rewrite J. rewrite (refS aS). auto.
         assert (A:= is_idMulS s).  assert (B := is_annMulS s).
       destruct A as [A _]; destruct B as [B _].
       assert (M := brel_transitive_f2 S eqS symS tranS (mulS aS s) s aS A L). 
       assert (N := tranS (mulS iS s) iS aS B K). apply symS in N.
       assert (I := brel_transitive_f1 S eqS symS tranS (mulS aS s) aS (mulS iS s) M N). apply symS in K.
       assert (R := cong_mulS aS s iS s K (refS s)). rewrite I in R. discriminate R.
       case_eq(eqS s aS); intro L.
       assert (J:= is_idMulS iS). destruct J as [Jl Jr].
       assert (B := brel_transitive_f2 S eqS symS tranS (mulS aS iS) iS aS Jl K). rewrite B. rewrite B. 
       assert (C := brel_transitive_f2 S eqS symS tranS (mulS iS aS) iS aS Jr K). rewrite C. rewrite C. auto.       
       assert (J:= is_annMulS s). destruct J as [Jl Jr].
       assert (A := brel_transitive_f2 S eqS symS tranS (mulS iS s) iS aS Jl K). rewrite A. rewrite A.
       assert (B := brel_transitive_f2 S eqS symS tranS (mulS s iS) iS aS Jr K). rewrite B. rewrite B. rewrite Jl,Jr. auto.
  Qed.

Definition mul_MA_proofs : sg_MA_proofs S (brel_reduce (uop_predicate_reduce aS P) eqS) bop_fpr_mulS aS iS :=
{|
sg_MA_associative   := bop_associative_fpr_id_v2 S P eqS refS symS aS mulS P_true P_cong P_false_preservation_mul cong_mulS is_idMulS ass_mulS
; sg_MA_congruence    := bop_full_reduce_congruence S eqS (uop_predicate_reduce aS P) mulS (uop_predicate_reduce_congruence S P eqS refS aS P_cong) cong_mulS
; sg_MA_is_id         := idProof_mul 
; sg_MA_is_ann        := annProof_mul
|}.


Record sg_MA (S : Type) := {
  sg_MA_eq         : brel S  
; sg_MA_bop        : binary_op S
; sg_MA_id         : S
; sg_MA_ann        : S
; sg_MA_eqv        : eqv_proofs S sg_MA_eq
; sg_MA_pfs        : sg_MA_proofs S sg_MA_eq sg_MA_bop sg_MA_id sg_MA_ann
}.

Definition mul_MA : sg_MA S :=
{|
sg_MA_eq         := (brel_reduce (uop_predicate_reduce aS P) eqS) 
; sg_MA_bop        := bop_fpr_mulS
; sg_MA_id         := aS
; sg_MA_ann        := iS
; sg_MA_eqv        := s_eqv_proof
; sg_MA_pfs        := mul_MA_proofs
|}.

Record dioid_proofs (S: Type) (eq : brel S) (add mul : binary_op S) (zero : S) (one : S) :=
{  
  dioid_left_distributive  : bop_left_distributive S eq add mul
; dioid_right_distributive : bop_right_distributive S eq add mul                             
; dioid_zero_is_mul_ann    : bop_is_ann S eq mul zero
; dioid_one_is_add_ann     : bop_is_ann S eq add one
}.

Record dioid_S (S : Type) := {
    dioid_S_eq         : brel S  
  ; dioid_S_add        : binary_op S
  ; dioid_S_mul        : binary_op S                                   
  ; dioid_S_zero       : S
  ; dioid_S_one        : S
  ; diode_S_eqv        : eqv_proofs S dioid_S_eq
  ; diode_S_add_pfs    : sg_CSMA_proofs S dioid_S_eq dioid_S_add dioid_S_zero dioid_S_one
  ; diode_S_mul_pfs    : sg_MA_proofs   S dioid_S_eq dioid_S_mul dioid_S_one  dioid_S_zero                                        
  ; dioid_S_pfs        : dioid_proofs S dioid_S_eq dioid_S_add dioid_S_mul dioid_S_zero dioid_S_one
}.


Check bop_left_distributive_fpr_v2 S P eqS refS symS tranS aS addS mulS P_true P_cong P_false_preservation P_false_preservation_mul cong_addS cong_mulS.

Definition add_mul_dioid_proofs : dioid_proofs S (brel_reduce (uop_predicate_reduce aS P) eqS) bop_fpr_addS bop_fpr_mulS iS aS :=
{|
dioid_left_distributive  := bop_left_distributive S eqS addS mulS
; dioid_right_distributive := bop_right_distributive S eqS addS mulS                             
; dioid_zero_is_mul_ann    := is_annMulS
; dioid_one_is_add_ann     := is_annAddS
|}.

Definition add_mul_dioid_S : dioid_S (S : Type) :=
{|
dioid_S_eq         := brel_reduce (uop_predicate_reduce aS P) eqS 
; dioid_S_add        := bop_fpr_addS
; dioid_S_mul        := bop_fpr_mulS                                  
; dioid_S_zero       := iS
; dioid_S_one        := aS
; diode_S_eqv        := s_eqv_proof
; diode_S_add_pfs    := add_CSMA_proofs
; diode_S_mul_pfs    := mul_MA_proofs                                      
; dioid_S_pfs        : dioid_proofs S dioid_S_eq dioid_S_add dioid_S_mul dioid_S_zero dioid_S_one
|}.


End Test.



