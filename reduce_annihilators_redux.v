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
  Proof. apply brel_reduce_reflexive.
         apply brel_product_reflexive; auto.
  Qed.

  Lemma brel_reduce_rap_symmetric : brel_symmetric (S * T) (brel_reduce uop_rap (brel_product eqS eqT)).
  Proof. apply brel_reduce_symmetric.
         apply brel_product_symmetric; auto.
  Qed.

  Lemma brel_reduce_rap_transitive : brel_transitive (S * T) (brel_reduce uop_rap (brel_product eqS eqT)).
  Proof. apply brel_reduce_transitive.
         apply brel_product_transitive; auto.
  Qed.

  Lemma brel_reduce_rap_congruence : brel_congruence (S * T) (brel_reduce uop_rap (brel_product eqS eqT)) (brel_reduce uop_rap (brel_product eqS eqT)). 
  Proof. apply brel_reduce_congruence; auto. 
         apply brel_product_congruence; auto. 
  Qed. 

             
Definition reduce_rap_eqv_proofs : eqv_proofs (S * T) (brel_reduce uop_rap (brel_product eqS eqT)) := 
{| eqv_reflexive  := brel_reduce_rap_reflexive
 ; eqv_transitive := brel_reduce_rap_transitive
 ; eqv_symmetric  := brel_reduce_rap_symmetric
 ; eqv_congruence :=  brel_reduce_rap_congruence
 ; eqv_witness    := (aS, aT) 
|}.

  
Lemma P_congruence : ∀ (p1 p2 : S * T), (brel_product eqS eqT) p1 p2 = true -> P p1 = P p2.
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
  

Lemma uop_rap_congruence : 
  uop_congruence (S * T) (brel_product eqS eqT) (uop_predicate_reduce (aS, aT) P).
Proof. apply uop_predicate_reduce_congruence; auto.
       apply brel_product_reflexive; auto.
       unfold pred_congruence. apply P_congruence.
Qed.
  
Lemma P_true : pred_true (S * T) P (aS, aT).
Proof. compute; auto. rewrite refS; auto. Qed.


Lemma P_add_decompose : pred_bop_decompose (S * T) P (bop_product addS addT).
Proof. intros [s1 t1] [s2 t2]; compute.
       intro H.
       case_eq(eqS s1 aS); intro H1; case_eq(eqS s2 aS); intro H2; auto.  
       case_eq(eqS (addS s1 s2) aS); intro K1.
       destruct (no_idS_div s1 s2 K1) as [L R]. 
       rewrite L in H1. discriminate H1.
       rewrite K1 in H. 
       case_eq(eqT t1 aT); intro H3; case_eq(eqT t2 aT); intro H4; auto.  
       destruct (no_idT_div t1 t2 H) as [L  R]. 
       rewrite L in H3. discriminate H3. 
Qed.

Lemma P_mul_decompose : pred_bop_decompose (S * T) P (bop_product mulS mulT).
Proof. intros [s1 t1] [s2 t2]; compute.
       intro H.
       case_eq(eqS s1 aS); intro H1; case_eq(eqS s2 aS); intro H2; auto.  
       case_eq(eqS (mulS s1 s2) aS); intro K1.
       destruct (no_annS_div s1 s2 K1) as [L | R]. 
         rewrite L in H1. discriminate H1.
         rewrite R in H2. discriminate H2.       
       rewrite K1 in H. 
       case_eq(eqT t1 aT); intro H3; case_eq(eqT t2 aT); intro H4; auto.  
       destruct (no_annT_div t1 t2 H) as [L | R]. 
          rewrite L in H3. discriminate H3.
          rewrite R in H4. discriminate H4.        
Qed.

Definition bop_rap_add : binary_op (S * T) := bop_fpr (aS, aT) P (bop_product addS addT).
Definition bop_rap_lexicographic_add : brel S -> binary_op (S * T) := λ eqS, bop_fpr (aS, aT) P (bop_llex eqS addS addT).
Definition bop_rap_mul : binary_op (S * T) := bop_fpr (aS, aT) P (bop_product mulS mulT).

Lemma bop_rap_add_congruence : bop_congruence (S * T) (brel_reduce uop_rap (brel_product eqS eqT)) bop_rap_add.
Proof. apply bop_full_reduce_congruence; auto.
       apply uop_predicate_reduce_congruence; auto.
       apply brel_product_reflexive; auto.
       unfold pred_congruence. apply P_congruence. 
       apply bop_product_congruence; auto. 
Qed.

Lemma bop_rap_mul_congruence : bop_congruence (S * T) (brel_reduce uop_rap (brel_product eqS eqT)) bop_rap_mul.
Proof. apply bop_full_reduce_congruence; auto.
       apply uop_predicate_reduce_congruence; auto.
       apply brel_product_reflexive; auto.
       unfold pred_congruence. apply P_congruence. 
       apply bop_product_congruence; auto. 
Qed.

Lemma bop_rap_add_associative :  bop_associative (S * T) (brel_reduce uop_rap (brel_product eqS eqT)) bop_rap_add.
Proof. apply bop_associative_fpr_decompositional_id; auto. 
       apply brel_product_reflexive; auto.
       apply brel_product_symmetric; auto.       
       apply brel_product_transitive; auto.
       apply P_true. 
       unfold pred_congruence. apply P_congruence.
       apply bop_product_congruence; auto.
       apply bop_product_associative; auto.
       apply P_add_decompose.
       apply bop_product_is_id; auto. 
Qed.

Lemma bop_rap_mul_associative :  bop_associative (S * T) (brel_reduce uop_rap (brel_product eqS eqT)) bop_rap_mul.
Proof. apply bop_associative_fpr_decompositional_ann; auto. 
       apply brel_product_reflexive; auto.
       apply brel_product_symmetric; auto.       
       apply brel_product_transitive; auto.
       apply P_true. 
       unfold pred_congruence. apply P_congruence.
       apply bop_product_congruence; auto.
       apply bop_product_associative; auto.
       apply P_mul_decompose.
       apply bop_product_is_ann; auto. 
Qed.



Lemma bop_rap_add_commutative :
  bop_commutative S eqS addS ->
  bop_commutative T eqT addT ->
     bop_commutative (S * T) (brel_reduce uop_rap (brel_product eqS eqT)) bop_rap_add.
Proof. intros C1 C2. 
       apply bop_full_reduce_commutative; auto.
       apply uop_predicate_reduce_congruence; auto.       
       apply brel_product_reflexive; auto.
       unfold pred_congruence. apply P_congruence.
       apply bop_product_commutative; auto.
Qed.


Lemma bop_rap_mul_commutative :
  bop_commutative S eqS mulS ->
  bop_commutative T eqT mulT ->
     bop_commutative (S * T) (brel_reduce uop_rap (brel_product eqS eqT)) bop_rap_mul.
Proof. intros C1 C2. 
       apply bop_full_reduce_commutative; auto.
       apply uop_predicate_reduce_congruence; auto.       
       apply brel_product_reflexive; auto.
       unfold pred_congruence. apply P_congruence.
       apply bop_product_commutative; auto.
Qed.

Lemma uop_rap_preserves_id :
 uop_preserves_id (S * T) (brel_product eqS eqT) (bop_product addS addT) uop_rap. 
Proof. unfold uop_preserves_id.
       intros [idS idT]. intro H.
       assert (J1 : bop_is_id S eqS addS idS). apply (bop_product_is_id_left S T eqS eqT addS addT idS idT H); auto. 
       assert (J2 : bop_is_id T eqT addT idT). apply (bop_product_is_id_right S T eqS eqT addS addT idS idT H); auto. 
       assert (J3 : eqS aS idS  = true). apply (bop_is_id_unique _ _ symS tranS aS idS addS is_idS J1). 
       assert (J4 : eqT aT idT = true).  apply (bop_is_id_unique _ _ symT tranT aT idT addT is_idT J2). 
       assert (J5 : P (idS, idT) = true).
          compute. apply symS in J3. rewrite J3; auto.  
       unfold brel_product. unfold uop_rap. unfold uop_predicate_reduce. 
       rewrite J5. rewrite J3. rewrite J4. compute; auto. 
Qed. 
       
Lemma uop_rap_preserves_ann :
 uop_preserves_ann (S * T) (brel_product eqS eqT) (bop_product mulS mulT) uop_rap. 
Proof. unfold uop_preserves_ann.
       intros [annS annT]. intro H.
       assert (J1 : bop_is_ann S eqS mulS annS). apply (bop_product_is_ann_left S T eqS eqT mulS mulT annS annT H); auto. 
       assert (J2 : bop_is_ann T eqT mulT annT). apply (bop_product_is_ann_right S T eqS eqT mulS mulT annS annT H); auto. 
       assert (J3 : eqS aS annS  = true).  apply (bop_is_ann_unique _ _ symS tranS aS annS mulS is_annS J1). 
       assert (J4 : eqT aT annT = true). apply (bop_is_ann_unique _ _ symT tranT aT annT mulT is_annT J2). 
       unfold brel_product. unfold uop_rap. unfold uop_predicate_reduce.        
       assert (J5 : P (annS, annT) = true).
          compute. apply symS in J3. rewrite J3; auto.  
       rewrite J5. rewrite J3. rewrite J4. compute; auto. 
Qed. 


Lemma  bop_rap_add_is_id : bop_is_id (S * T)
                                     (brel_reduce uop_rap (brel_product eqS eqT))
                                     bop_rap_add
                                     (aS, aT).
Proof.  apply bop_full_reduce_is_id; auto. 
        apply brel_product_reflexive; auto.
        apply brel_product_transitive; auto.
        apply uop_predicate_reduce_congruence; auto.
        apply brel_product_reflexive; auto.
        unfold pred_congruence. apply P_congruence.
        apply uop_predicate_reduce_idempotent; auto.
        apply brel_product_reflexive; auto.
        apply bop_product_congruence; auto.
        apply uop_rap_preserves_id; auto. 
        apply bop_product_is_id; auto. 
Qed.  

Lemma  bop_rap_mul_is_ann : bop_is_ann (S * T)
                                     (brel_reduce uop_rap (brel_product eqS eqT))
                                     bop_rap_mul
                                     (aS, aT).
Proof.  apply bop_full_reduce_is_ann; auto. 
        apply brel_product_reflexive; auto.
        apply brel_product_transitive; auto.
        apply uop_predicate_reduce_congruence; auto.
        apply brel_product_reflexive; auto.
        unfold pred_congruence. apply P_congruence.
        apply bop_product_congruence; auto.
        apply uop_rap_preserves_ann; auto.
        apply bop_product_is_ann; auto. 
Qed.  


End ReduceAnnihilators.
