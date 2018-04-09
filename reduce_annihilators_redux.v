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

Section ReduceAnnihilators.

  Variable S : Type.
  Variable T : Type.     
  Variable eqS : brel S.
  Variable eqT : brel T.
  Variable refS : brel_reflexive S eqS.
  Variable symS : brel_symmetric S eqS.
  Variable tranS : brel_transitive S eqS.
  Variable eqS_cong : brel_congruence S eqS eqS.      
  Variable refT : brel_reflexive T eqT.
  Variable symT : brel_symmetric T eqT.
  Variable tranT : brel_transitive T eqT.
  Variable eqT_cong : brel_congruence T eqT eqT.        
  Variable aS : S.
  Variable aT : T.

  Variable addS : binary_op S.
  Variable addT : binary_op T.
  Variable cong_addS : bop_congruence S eqS addS.
  Variable cong_addT : bop_congruence T eqT addT.
  Variable ass_addS : bop_associative S eqS addS.
  Variable ass_addT : bop_associative T eqT addT.
  

  Variable mulS : binary_op S.
  Variable mulT : binary_op T.
  Variable cong_mulS : bop_congruence S eqS mulS.
  Variable cong_mulT : bop_congruence T eqT mulT.
  Variable ass_mulS : bop_associative S eqS mulS.
  Variable ass_mulT : bop_associative T eqT mulT.

  Variable is_idS : bop_is_id S eqS addS aS.
  Variable is_idT : bop_is_id T eqT addT aT.  

  Variable is_annS : bop_is_ann S eqS mulS aS.
  Variable is_annT : bop_is_ann T eqT mulT aT. 

  Variable no_idS_div : bop_self_square S eqS addS aS. (* ∀ a b : S,  eqS (addS a b) aS = true -> (eqS a aS = true) * (eqS b aS = true).  *) 
  Variable no_idT_div : bop_self_square T eqT addT aT. (* ∀ a b : T,  eqT (addT a b) aT = true -> (eqT a aT = true) * (eqT b aT = true).  *) 

  Variable no_annS_div : bop_self_divisor S eqS mulS aS. (* ∀ a b : S,  eqS (mulS a b) aS = true -> (eqS a aS = true) + (eqS b aS = true).  *) 
  Variable no_annT_div : bop_self_divisor T eqT mulT aT. (* ∀ a b : T,  eqT (mulT a b) aT = true -> (eqT a aT = true) + (eqT b aT = true).  *) 

  Definition P : (S *T) -> bool := λ p, match p with (s, t) => orb (eqS s aS) (eqT t aT) end.

  Definition uop_rap : unary_op (S * T) := uop_predicate_reduce (aS, aT) P.



  Lemma brel_reduce_rap_reflexive : brel_reflexive (S * T) (brel_reduce uop_rap (brel_product eqS eqT)). 
  Proof. intros [s t]. compute.
         case_eq(eqS s aS); intro J1.
         rewrite refS. rewrite refT; auto.
         case_eq(eqT t aT); intro J2.
         rewrite refS. rewrite refT; auto.         
         rewrite refS. apply refT.
  Qed.

  Lemma brel_reduce_rap_symmetric : brel_symmetric (S * T) (brel_reduce uop_rap (brel_product eqS eqT)). 
  Proof. intros [s1 t1] [s2 t2]. compute.
         case_eq(eqS s1 aS); intro J1; case_eq(eqS s2 aS); intro J2. 
         rewrite refS. rewrite refT; auto.
         case_eq(eqT t2 aT); intro J3.
         rewrite refS. rewrite refT; auto.         
         apply brel_symmetric_false in J2; auto. rewrite J2. intro F. discriminate F.
         case_eq(eqT t1 aT); intro J3.
         rewrite refS. rewrite refT; auto.
         rewrite J1. intro F. discriminate F.
         case_eq(eqT t1 aT); intro J3; case_eq(eqT t2 aT); intro J4.
             rewrite refS. rewrite refT; auto.
             apply brel_symmetric_false in J2; auto. rewrite J2. intro F. discriminate F.
             rewrite J1. intro F. discriminate F.
             case_eq(eqS s1 s2); intro J5; case_eq(eqT t1 t2); intro J6; intro H; auto. 
             apply symS in J5. apply symT in J6. rewrite J5, J6; auto.
             discriminate H.
             discriminate H.
             discriminate H.              
  Qed.


  Lemma brel_reduce_rap_transitive : brel_transitive (S * T) (brel_reduce uop_rap (brel_product eqS eqT)). 
  Proof. intros [s1 t1] [s2 t2] [s3 t3]. compute.
         case_eq(eqS s1 aS); intro J1; case_eq(eqS s2 aS); intro J2; case_eq(eqS s3 aS); intro J3. 
         rewrite refS. rewrite refT; auto.
         intro H1. 
         case_eq(eqT t3 aT); intro J4.
         rewrite refS. rewrite refT; auto.         
         apply brel_symmetric_false in J3; auto. 
         case_eq(eqT t2 aT); intro J4.
         rewrite refS. rewrite refT; auto.
         apply brel_symmetric_false in J2; auto. rewrite J2. intro F. discriminate F.
         case_eq(eqT t2 aT); intro J4; case_eq(eqT t3 aT); intro J5; auto.         
         apply brel_symmetric_false in J2; auto. rewrite J2. intro F. discriminate F.
         apply brel_symmetric_false in J2; auto. rewrite J2. intro F. discriminate F.
         rewrite refS. rewrite refT. 
         case_eq(eqT t1 aT); intro J4.
         rewrite refS. rewrite refT; auto. 
         rewrite J1. intro F. discriminate F.
         case_eq(eqT t1 aT); intro J4; case_eq(eqT t3 aT); intro J5.
         rewrite refS. rewrite refT; auto.
         rewrite refS. rewrite refT; auto.
         rewrite J1. intro F. discriminate F.
         rewrite J1. intro F. discriminate F.
         case_eq(eqT t1 aT); intro J4; case_eq(eqT t2 aT); intro J5.
         rewrite refS. rewrite refT; auto.
         rewrite refS. rewrite refT; auto.
         rewrite J1. intro F. discriminate F.
         rewrite J1. rewrite J2.
         intros H1 H2. exact H2.
         case_eq(eqT t1 aT); intro J4; case_eq(eqT t2 aT); intro J5; case_eq(eqT t3 aT); intro J6.
         rewrite refS. rewrite refT; auto.
         rewrite refS. rewrite refT; auto.
         rewrite refS. rewrite refT; auto.
         apply brel_symmetric_false in J2; auto. rewrite J2. intro F. discriminate F.
         rewrite J1. intro F. discriminate F.
         rewrite J1. intro F. discriminate F.
         rewrite J1. rewrite J2.
         intros H1 H2. exact H2.
         case_eq(eqS s1 s2); intro J7; case_eq(eqS s2 s3); intro J8; case_eq(eqS s1 s3); intro J9; auto.
         apply tranT.
         intros H1 H2. rewrite (tranS _ _ _ J7 J8) in J9. discriminate J9.
         intros H1 H2. discriminate H2.
         intro H. discriminate H.
         intro H. discriminate H.         
  Qed.

    Lemma brel_reduce_rap_congruence : brel_congruence (S * T) (brel_reduce uop_rap (brel_product eqS eqT)) (brel_reduce uop_rap (brel_product eqS eqT)). 
    Proof. apply brel_reduce_congruence.
           apply brel_product_congruence.
           apply eqS_cong.
           apply eqT_cong.            
    Qed. 


             
Definition reduce_rap_eqv_proofs : eqv_proofs (S * T) (brel_reduce uop_rap (brel_product eqS eqT)) := 
{| eqv_reflexive  := brel_reduce_rap_reflexive
 ; eqv_transitive := brel_reduce_rap_transitive
 ; eqv_symmetric  := brel_reduce_rap_symmetric
 ; eqv_congruence :=  brel_reduce_rap_congruence
 ; eqv_witness    := (aS, aT) 
|}.



  
  
  Lemma P_congruence_v1 : ∀ (p1 p2 : S * T), brel_product eqS eqT p1 p2 = true -> P p1 = P p2.
  Proof. intros [s1 t1] [s2 t2]; compute; intro H.
         case_eq(eqS s1 aS); intro J1; case_eq(eqS s2 aS); intro J2; auto.
         assert (J3 := brel_transitive_f1 S eqS symS tranS s2 aS s1 J2 (symS _ _ J1)).         
         case_eq(eqS s1 s2); intro J4. apply symS in J4. rewrite J4 in J3. discriminate J3. 
         rewrite J4 in H. discriminate H. 
         assert (J3 := brel_transitive_f1 S eqS symS tranS _ _ _ J1 (symS _ _ J2)). 
         rewrite J3 in H. discriminate H. 
         case_eq(eqT t1 aT); intro J3; case_eq(eqT t2 aT); intro J4; auto. 
         assert (J5 := brel_transitive_f1 T eqT symT tranT _ _ _ J4 (symT _ _ J3)).                 
         case_eq(eqS s1 s2); intro J6. rewrite J6 in H.  apply symT in H. rewrite J5 in H. discriminate H.
         rewrite J6 in H. discriminate H.
         case_eq(eqS s1 s2); intro J5. rewrite J5 in H.
         assert (K := tranT _ _ _ H J4). rewrite K in J3. discriminate J3. 
         rewrite J5 in H. discriminate H.                  
  Qed.
  
 Lemma P_congruence_v2 : ∀ (p1 p2 : S * T), brel_reduce uop_rap (brel_product eqS eqT) p1 p2 = true -> P p1 = P p2.
  Proof. intros [s1 t1] [s2 t2]; compute; intro H.
         case_eq(eqS s1 aS); intro J1; case_eq(eqS s2 aS); intro J2; auto.
         assert (J3 := brel_transitive_f1 S eqS symS tranS s2 aS s1 J2 (symS _ _ J1)).
         case_eq(eqS s1 s2); intro J4. apply symS in J4. rewrite J4 in J3. discriminate J3. 
         rewrite J1 in H. rewrite J2 in H. 
         case_eq(eqT t2 aT); intro J5. reflexivity. rewrite J5 in H. apply brel_symmetric_false in J2. rewrite J2 in H. discriminate H.
         apply symS. rewrite J1 in H. rewrite J2 in H.
         case_eq(eqT t1 aT); intro J3. reflexivity. rewrite J3 in H. rewrite J1 in H. discriminate H. 
         rewrite J1 in H. rewrite J2 in H. 
         case_eq(eqT t1 aT); intro J3;  case_eq(eqT t2 aT); intro J4; rewrite J3 in H; rewrite J4 in H; auto.
         apply brel_symmetric_false in J2; auto. rewrite J2 in H. discriminate H. rewrite J1 in H. discriminate H. 
Qed. 

  Lemma uop_rap_congruence_v1 : 
  uop_congruence (S * T) (brel_product eqS eqT) (uop_predicate_reduce (aS, aT) P).
  Proof. apply uop_predicate_reduce_congruence; auto.
         apply brel_product_reflexive; auto.
         apply P_congruence_v1.
  Qed.

  
  Lemma uop_rap_congruence_v2 : 
  uop_congruence (S * T) (brel_reduce uop_rap (brel_product eqS eqT)) (uop_predicate_reduce (aS, aT) P).
  Proof. apply uop_predicate_reduce_congruence; auto.
         apply brel_reduce_reflexive; auto. 
         apply brel_product_reflexive; auto.
         apply P_congruence_v2.
  Qed.

  
Lemma P_true : P(aS, aT) = true. Proof. compute; auto. rewrite refS; auto. Qed.


Lemma P_false_preservation_add : ∀ (p1 p2 : S * T), P p1 = false -> P p2 = false -> P (bop_product addS addT p1 p2) = false.
  Proof. intros [s1 t1] [s2 t2]; compute.
         case_eq(eqS s1 aS); intro J1;
         case_eq(eqS s2 aS); intro J2;           
           intros H1 H2.
         discriminate H1.
         discriminate H1.
         discriminate H2.
         case_eq(eqS (addS s1 s2) aS); intro K1.
         destruct (no_idS_div s1 s2 K1) as [L R]. 
            rewrite L in J1. discriminate J1. 
         case_eq(eqT (addT t1 t2) aT); intro K2.            
         destruct (no_idT_div t1 t2 K2) as [L  R]. 
            rewrite L in H1. discriminate H1. 
         reflexivity. 
  Qed.
  

Lemma P_false_preservation_mul : ∀ (p1 p2 : S * T), P p1 = false -> P p2 = false -> P (bop_product mulS mulT p1 p2) = false.
  Proof. intros [s1 t1] [s2 t2]; compute.
         case_eq(eqS s1 aS); intro J1;
         case_eq(eqS s2 aS); intro J2;         
           intros H1 H2.
         discriminate H1.
         discriminate H1.
         discriminate H2.
         case_eq(eqS (mulS s1 s2) aS); intro K1.
         destruct (no_annS_div s1 s2 K1) as [L | R]. 
            rewrite L in J1. discriminate J1. 
            rewrite R in J2. discriminate J2.
         case_eq(eqT (mulT t1 t2) aT); intro K2.            
         destruct (no_annT_div t1 t2 K2) as [L | R]. 
            rewrite L in H1. discriminate H1. 
            rewrite R in H2. discriminate H2.             
         reflexivity. 
  Qed.


Definition bop_rap_mul : binary_op (S * T) := bop_fpr (aS, aT) P (bop_product mulS mulT).


Lemma bop_rap_mul_associative :  bop_associative (S * T) (brel_reduce uop_rap (brel_product eqS eqT)) bop_rap_mul.
Proof. apply bop_associative_fpr_ann_v2; auto.
       apply brel_product_reflexive; auto. 
       apply P_true; auto. 
       apply P_congruence_v1; auto. 
       apply P_false_preservation_mul; auto.
       apply bop_product_congruence; auto.  
       apply bop_product_is_ann; auto.
       apply bop_product_associative; auto.
Qed.

Lemma bop_rap_mul_congruence : bop_congruence (S * T) (brel_reduce uop_rap (brel_product eqS eqT)) bop_rap_mul.
Proof. unfold bop_rap_mul. unfold bop_fpr. 
       apply bop_full_reduce_congruence; auto.
       apply uop_predicate_reduce_congruence; auto.
       apply brel_product_reflexive; auto.
       apply P_congruence_v1. 
       apply bop_product_congruence; auto. 
Qed.

(*
Lemma  bop_rap_mul_is_ann : bop_is_ann (S * T) (brel_product eqS eqT) bop_rap_mul (aS, aT).
Proof.  intros [s t]; compute. rewrite refS.
        case_eq(eqS s aS); intro J1. 
        destruct (is_annS aS) as [LS RS]. destruct (is_annT aT) as [LT RT].
        rewrite LS.  split; rewrite refS; rewrite refT; auto.
        case_eq(eqT t aT); intro J2. 
        destruct (is_annS aS) as [LS RS]. destruct (is_annT aT) as [LT RT].
        rewrite LS.  split; rewrite refS; rewrite refT; auto.
        destruct (is_annS s) as [LS RS]. destruct (is_annT t) as [LT RT].
       rewrite LS, RS. split; rewrite refS; rewrite refT; auto.
Qed.  
*) 

Lemma  bop_rap_mul_is_ann_v2 : bop_is_ann (S * T) (brel_reduce uop_rap (brel_product eqS eqT)) bop_rap_mul (aS, aT).
Proof.  intros [s t]; compute. rewrite refS. 
        case_eq(eqS s aS); intro J1. 
        destruct (is_annS aS) as [LS RS]. destruct (is_annT aT) as [LT RT].
        rewrite LS.  split; rewrite refS; rewrite refT; auto. rewrite refS; auto. rewrite refS; auto. 
        case_eq(eqT t aT); intro J2. 
        destruct (is_annS aS) as [LS RS]. destruct (is_annT aT) as [LT RT].
        rewrite LS.  split; rewrite refS; rewrite refT; auto. rewrite refS; auto. rewrite refS; auto. 
        destruct (is_annS s) as [LS RS]. destruct (is_annT t) as [LT RT].
        rewrite LS, RS. split; rewrite refS; rewrite refT; auto.
        rewrite refS; auto. rewrite refS; auto. 
Qed.  


(*
Lemma bop_rap_mul_commutative :  bop_commutative S eqS mulS -> bop_commutative T eqT mulT -> bop_commutative (S * T) (brel_product eqS eqT) bop_rap_mul.
Proof. intros C1 C2 [s1 t1] [s2 t2]. unfold bop_rap_mul. unfold bop_fpr.
       apply bop_full_reduce_commutative; auto. 
       apply uop_predicate_reduce_congruence; auto.
       apply brel_product_reflexive; auto.
       apply P_congruence_v1; auto.
       apply bop_product_commutative; auto.
Qed.
*) 
Lemma bop_rap_mul_commutative_v2 :
         bop_commutative S eqS mulS -> bop_commutative T eqT mulT ->
                                    bop_commutative (S * T) (brel_reduce uop_rap (brel_product eqS eqT)) bop_rap_mul.
Proof. intros C1 C2 [s1 t1] [s2 t2]. unfold bop_rap_mul. unfold bop_fpr.
       apply bop_full_reduce_commutative; auto. 
       apply uop_predicate_reduce_congruence; auto.
       apply brel_product_reflexive; auto.
       apply P_congruence_v1; auto.
       apply bop_product_commutative; auto.
Qed.



Definition bop_rap_add : binary_op (S * T) := bop_fpr (aS, aT) P (bop_product addS addT).
Definition bop_rap_lexicographic_add : brel S -> binary_op (S * T) := λ eqS, bop_fpr (aS, aT) P (bop_llex eqS addS addT).


Lemma bop_rap_add_congruence : bop_congruence (S * T) (brel_reduce uop_rap (brel_product eqS eqT)) bop_rap_add.
Proof. unfold bop_rap_add. unfold bop_fpr. 
       apply bop_full_reduce_congruence; auto.
       apply uop_rap_congruence_v1; auto.
       apply bop_product_congruence; auto. 
Qed.

Lemma bop_rap_add_associative :  bop_associative (S * T) (brel_reduce uop_rap (brel_product eqS eqT)) bop_rap_add.
Proof. apply bop_associative_fpr_id_v2; auto.
       apply brel_product_reflexive; auto.
       apply brel_product_symmetric; auto. 
       apply P_true; auto. 
       apply P_congruence_v1; auto. 
       apply P_false_preservation_add; auto.
       apply bop_product_congruence; auto.
       apply bop_product_is_id; auto.
       apply bop_product_associative; auto.
Qed.


Lemma bop_rap_add_associative_pseudo: bop_pseudo_associative (S * T) (brel_product eqS eqT) uop_rap (bop_product addS addT).
Proof. apply bop_full_reduce_associative_implies_pseudo_associative.
       apply brel_product_reflexive; auto.
       apply brel_product_symmetric; auto.
       apply brel_product_transitive; auto.
       apply uop_predicate_reduce_idempoent. apply brel_product_reflexive; auto.
       apply uop_predicate_reduce_congruence. apply brel_product_reflexive; auto.  apply P_congruence_v1.  
       apply bop_product_congruence; auto. 
       apply bop_rap_add_associative.
Qed.

Lemma bop_rap_add_commutative :
     bop_commutative S eqS addS -> bop_commutative T eqT addT ->
            bop_commutative (S * T) (brel_reduce uop_rap (brel_product eqS eqT)) bop_rap_add.
Proof. intros C1 C2 [s1 t1] [s2 t2]. unfold bop_rap_mul. unfold bop_fpr.
       apply bop_full_reduce_commutative; auto. 
       apply uop_predicate_reduce_congruence; auto.
       apply brel_product_reflexive; auto.
       apply P_congruence_v1; auto.
       apply bop_product_commutative; auto.
Qed.

(* NB: this requires equality to be (brel_reduce uop_rap (brel_product eqS eqT)) *) 
Lemma  bop_rap_add_is_id : bop_is_id (S * T) (brel_reduce uop_rap (brel_product eqS eqT)) bop_rap_add (aS, aT).
Proof.  intros [s t]. compute. rewrite refS.
        case_eq(eqS s aS); intro J1. 
        destruct (is_idS aS) as [LS RS]. destruct (is_idT aT) as [LT RT].
        rewrite LS.  split; rewrite refS. rewrite refS. rewrite refT.
        reflexivity. rewrite refS. rewrite refT. reflexivity.
        case_eq(eqT t aT); intro J2.
        destruct (is_idS aS) as [LS RS]. destruct (is_idT aT) as [LT RT].
        rewrite LS.  split; rewrite refS. rewrite refS. rewrite refT.        
        reflexivity. rewrite refS. rewrite refT. reflexivity.
        destruct (is_idS s) as [LS RS]. destruct (is_idT t) as [LT RT].        
        assert (A1 : eqS (addS aS s) aS = false).
           case_eq (eqS (addS aS s) aS); intro K.
           apply symS in LS.
           rewrite (tranS _ _ _ LS K) in J1. discriminate J1.
           reflexivity. 
           assert (A2 : eqS (addS s aS) aS = false).
              apply symS in RS.
              apply brel_symmetric_false in J1; auto. 
              assert (K := brel_transitive_f1 S eqS symS tranS _ _ _ J1 RS).
              apply brel_symmetric_false in K; auto. 
           assert (A3 : eqT (addT aT t) aT = false).
              apply symT in LT.
              apply brel_symmetric_false in J2; auto. 
              assert (K := brel_transitive_f1 T eqT symT tranT _ _ _ J2 LT).
              apply brel_symmetric_false in K; auto. 
           assert (A4 : eqT (addT t aT) aT = false).
              apply symT in RT.
              apply brel_symmetric_false in J2; auto. 
              assert (K := brel_transitive_f1 T eqT symT tranT _ _ _ J2 RT).
              apply brel_symmetric_false in K; auto. 
        rewrite A1. rewrite A2. rewrite A3. rewrite A4. rewrite A1. rewrite A3. rewrite A2. rewrite A4. split.
        destruct (is_idS s) as [Ls Rs]. destruct (is_idT t) as [Lt Rt].
        rewrite Ls. rewrite Lt. reflexivity.
        destruct (is_idS s) as [Ls Rs]. destruct (is_idT t) as [Lt Rt].
        rewrite Rs. rewrite Rt. reflexivity.        
Qed. 


End ReduceAnnihilators.
