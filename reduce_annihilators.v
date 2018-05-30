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
  Variable zeroS oneS: S.
  Variable zeroT oneT : T.

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

  Variable zeroS_is_add_id  : bop_is_id S eqS addS zeroS.
  Variable oneS_is_mul_id   : bop_is_id S eqS mulS oneS.
  Variable zeroS_is_mul_ann : bop_is_ann S eqS mulS zeroS.
  Variable oneS_is_add_ann  : bop_is_ann S eqS addS oneS.

  Variable zeroT_is_add_id  : bop_is_id T eqT addT zeroT.
  Variable oneT_is_mul_id   : bop_is_id T eqT mulT oneT.
  Variable zeroT_is_mul_ann : bop_is_ann T eqT mulT zeroT.
  Variable oneT_is_add_ann  : bop_is_ann T eqT addT oneT.

  Variable oneS_not_zeroS : eqS oneS zeroS = false.
  Variable oneT_not_zeroT : eqT oneT zeroT = false.   

  Variable zeroS_squ : bop_self_square S eqS addS zeroS. (* ∀ a b : S,  eqS (addS a b) zeroS = true -> (eqS a zeroS = true) * (eqS b zeroS = true).  *) 
  Variable zeroT_squ : bop_self_square T eqT addT zeroT. (* ∀ a b : T,  eqT (addT a b) zeroT = true -> (eqT a zeroT = true) * (eqT b zeroT = true).  *) 
  
  Variable zeroS_div : bop_self_divisor S eqS mulS zeroS. (* ∀ a b : S,  eqS (mulS a b) zeroS = true -> (eqS a zeroS = true) + (eqS b zeroS = true).  *) 
  Variable zeroT_div : bop_self_divisor T eqT mulT zeroT. (* ∀ a b : T,  eqT (mulT a b) zeroT = true -> (eqT a zeroT = true) + (eqT b zeroT = true).  *) 




  Definition P : (S *T) -> bool := λ p, match p with (s, t) => orb (eqS s zeroS) (eqT t zeroT) end.

  Definition uop_rap : unary_op (S * T) := uop_predicate_reduce (zeroS, zeroT) P.

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

              
Lemma P_congruence : pred_congruence (S * T) (brel_product eqS eqT) P. 
Proof. intros [s1 t1] [s2 t2]; compute; intro H.
         case_eq(eqS s1 zeroS); intro J1; case_eq(eqS s2 zeroS); intro J2; auto.
         assert (J3 := brel_transitive_f1 S eqS symS tranS s2 zeroS s1 J2 (symS _ _ J1)).         
         case_eq(eqS s1 s2); intro J4. apply symS in J4. rewrite J4 in J3. discriminate J3. 
         rewrite J4 in H. discriminate H. 
         assert (J3 := brel_transitive_f1 S eqS symS tranS _ _ _ J1 (symS _ _ J2)). 
         rewrite J3 in H. discriminate H. 
         case_eq(eqT t1 zeroT); intro J3; case_eq(eqT t2 zeroT); intro J4; auto. 
         assert (J5 := brel_transitive_f1 T eqT symT tranT _ _ _ J4 (symT _ _ J3)).                 
         case_eq(eqS s1 s2); intro J6. rewrite J6 in H.  apply symT in H. rewrite J5 in H. discriminate H.
         rewrite J6 in H. discriminate H.
         case_eq(eqS s1 s2); intro J5. rewrite J5 in H.
         assert (K := tranT _ _ _ H J4). rewrite K in J3. discriminate J3. 
         rewrite J5 in H. discriminate H.                  
Qed.
  

Lemma uop_rap_congruence : 
  uop_congruence (S * T) (brel_product eqS eqT) (uop_predicate_reduce (zeroS, zeroT) P).
Proof. apply uop_predicate_reduce_congruence; auto.
       apply brel_product_reflexive; auto.
       unfold pred_congruence. apply P_congruence.
Qed.
  
Lemma P_true : pred_true (S * T) P (zeroS, zeroT).
Proof. compute; auto. rewrite refS; auto. Qed.


Lemma P_add_decompose : pred_bop_decompose (S * T) P (bop_product addS addT).
Proof. intros [s1 t1] [s2 t2]; compute.
       intro H.
       case_eq(eqS s1 zeroS); intro H1; case_eq(eqS s2 zeroS); intro H2; auto.  
       case_eq(eqS (addS s1 s2) zeroS); intro K1.
       destruct (zeroS_squ s1 s2 K1) as [L R]. 
       rewrite L in H1. discriminate H1.
       rewrite K1 in H. 
       case_eq(eqT t1 zeroT); intro H3; case_eq(eqT t2 zeroT); intro H4; auto.  
       destruct (zeroT_squ t1 t2 H) as [L  R]. 
       rewrite L in H3. discriminate H3. 
Qed.

Lemma P_mul_decompose : pred_bop_decompose (S * T) P (bop_product mulS mulT).
Proof. intros [s1 t1] [s2 t2]; compute.
       intro H.
       case_eq(eqS s1 zeroS); intro H1; case_eq(eqS s2 zeroS); intro H2; auto.  
       case_eq(eqS (mulS s1 s2) zeroS); intro K1.
       destruct (zeroS_div s1 s2 K1) as [L | R]. 
         rewrite L in H1. discriminate H1.
         rewrite R in H2. discriminate H2.       
       rewrite K1 in H. 
       case_eq(eqT t1 zeroT); intro H3; case_eq(eqT t2 zeroT); intro H4; auto.  
       destruct (zeroT_div t1 t2 H) as [L | R]. 
          rewrite L in H3. discriminate H3.
          rewrite R in H4. discriminate H4.        
Qed.

(* important!! mul is always not decompose but compose!! *)
Lemma P_mul_compose : pred_bop_compose (S * T) P (bop_product mulS mulT).
Proof. intros [s1 t1] [s2 t2]; compute.
       intro H.
       case_eq(eqS s1 zeroS); intro H1; case_eq(eqS s2 zeroS); intro H2; auto.
       assert (A := cong_mulS s1 s2 zeroS zeroS H1 H2).
       assert (B := zeroS_is_mul_ann zeroS). destruct B as [B _].
       assert (C := tranS _ _ _ A B). rewrite C. auto.
       assert (A := cong_mulS s1 s2 zeroS s2 H1 (refS s2)).
       assert (B := zeroS_is_mul_ann s2). destruct B as [B _].
       assert (C := tranS _ _ _ A B). rewrite C. auto.
       assert (A := cong_mulS s1 s2 s1 zeroS (refS s1) H2).
       assert (B := zeroS_is_mul_ann s1). destruct B as [_ B].
       assert (C := tranS _ _ _ A B). rewrite C. auto.
       rewrite H2 in H. rewrite H1 in H.   
       case_eq(eqS (mulS s1 s2) zeroS); intro K. auto.
       destruct H as [H | H].
       assert (A := cong_mulT t1 t2 zeroT t2 H (refT t2)).
       assert (B := zeroT_is_mul_ann t2). destruct B as [B _].
       assert (C := tranT _ _ _ A B). rewrite C. auto.
       assert (A := cong_mulT t1 t2 t1 zeroT (refT t1) H).
       assert (B := zeroT_is_mul_ann t1). destruct B as [_ B].
       assert (C := tranT _ _ _ A B). rewrite C. auto.
Qed.

Definition bop_rap_add : binary_op (S * T) := bop_fpr (zeroS, zeroT) P (bop_product addS addT).
Definition bop_rap_lexicographic_add : brel S -> binary_op (S * T) := λ eqS, bop_fpr (zeroS, zeroT) P (bop_llex eqS addS addT).
Definition bop_rap_mul : binary_op (S * T) := bop_fpr (zeroS, zeroT) P (bop_product mulS mulT).

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

Lemma bop_rap_mul_associative_compositional :  bop_associative (S * T) (brel_reduce uop_rap (brel_product eqS eqT)) bop_rap_mul.
Proof. apply bop_associative_fpr_compositional; auto. 
       apply brel_product_reflexive; auto.
       apply brel_product_symmetric; auto.       
       apply brel_product_transitive; auto.
       apply P_true. 
       unfold pred_congruence. apply P_congruence.
       apply P_mul_compose.
       apply bop_product_congruence; auto.
       apply bop_product_associative; auto.
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


Lemma uop_rap_add_preserves_id :
 uop_preserves_id (S * T) (brel_product eqS eqT) (bop_product addS addT) uop_rap. 
Proof. unfold uop_preserves_id.
       intros [idS idT]. intro H.
       assert (J1 : bop_is_id S eqS addS idS). apply (bop_product_is_id_left S T eqS eqT addS addT idS idT H); auto. 
       assert (J2 : bop_is_id T eqT addT idT). apply (bop_product_is_id_right S T eqS eqT addS addT idS idT H); auto. 
       assert (J3 : eqS zeroS idS  = true). apply (bop_is_id_unique _ _ symS tranS zeroS idS addS zeroS_is_add_id J1). 
       assert (J4 : eqT zeroT idT = true).  apply (bop_is_id_unique _ _ symT tranT zeroT idT addT zeroT_is_add_id J2). 
       assert (J5 : P (idS, idT) = true).
          compute. apply symS in J3. rewrite J3; auto.  
       unfold brel_product. unfold uop_rap. unfold uop_predicate_reduce. 
       rewrite J5. rewrite J3. rewrite J4. compute; auto. 
Qed.

Lemma uop_rap_add_preserves_ann :
 uop_preserves_ann (S * T) (brel_product eqS eqT) (bop_product addS addT) uop_rap. 
Proof. unfold uop_preserves_ann.
       intros [annS annT]. intro H.
       assert (J1 : bop_is_ann S eqS addS annS). apply (bop_product_is_ann_left S T eqS eqT addS addT annS annT H); auto. 
       assert (J2 : bop_is_ann T eqT addT annT). apply (bop_product_is_ann_right S T eqS eqT addS addT annS annT H); auto. 
       assert (J3 : eqS oneS annS  = true).  apply (bop_is_ann_unique _ _ symS tranS oneS annS addS oneS_is_add_ann J1). 
       assert (J4 : eqT oneT annT = true). apply (bop_is_ann_unique _ _ symT tranT oneT annT addT oneT_is_add_ann J2). 
       unfold brel_product. unfold uop_rap. unfold uop_predicate_reduce.        
       assert (J5 : P (annS, annT) = false). 
          compute. apply symS in J3. 
          assert(J5 : eqS annS zeroS = false). exact (brel_transitive_f2 _ eqS symS tranS _ _ _ J3 oneS_not_zeroS).
          rewrite J5. apply symT in J4.
          assert(J6 : eqT annT zeroT = false).  exact (brel_transitive_f2 _ eqT symT tranT _ _ _ J4 oneT_not_zeroT).
          rewrite J6. reflexivity. 
       rewrite J5. rewrite refS. rewrite refT. compute; auto. 
Qed. 

Lemma uop_rap_mul_preserves_ann :
 uop_preserves_ann (S * T) (brel_product eqS eqT) (bop_product mulS mulT) uop_rap. 
Proof. unfold uop_preserves_ann.
       intros [annS annT]. intro H.
       assert (J1 : bop_is_ann S eqS mulS annS). apply (bop_product_is_ann_left S T eqS eqT mulS mulT annS annT H); auto. 
       assert (J2 : bop_is_ann T eqT mulT annT). apply (bop_product_is_ann_right S T eqS eqT mulS mulT annS annT H); auto. 
       assert (J3 : eqS zeroS annS  = true).  apply (bop_is_ann_unique _ _ symS tranS zeroS annS mulS zeroS_is_mul_ann J1). 
       assert (J4 : eqT zeroT annT = true). apply (bop_is_ann_unique _ _ symT tranT zeroT annT mulT zeroT_is_mul_ann J2). 
       unfold brel_product. unfold uop_rap. unfold uop_predicate_reduce.        
       assert (J5 : P (annS, annT) = true).
          compute. apply symS in J3. rewrite J3; auto.  
       rewrite J5. rewrite J3. rewrite J4. compute; auto. 
Qed. 

Lemma uop_rap_mul_preserves_id :
 uop_preserves_id (S * T) (brel_product eqS eqT) (bop_product mulS mulT) uop_rap. 
Proof. unfold uop_preserves_id.
       intros [idS idT]. intro H.
       assert (J1 : bop_is_id S eqS mulS idS). apply (bop_product_is_id_left S T eqS eqT mulS mulT idS idT H); auto. 
       assert (J2 : bop_is_id T eqT mulT idT). apply (bop_product_is_id_right S T eqS eqT mulS mulT idS idT H); auto. 
       assert (J3 : eqS oneS idS  = true).  apply (bop_is_id_unique _ _ symS tranS oneS idS mulS oneS_is_mul_id J1). 
       assert (J4 : eqT oneT idT = true). apply (bop_is_id_unique _ _ symT tranT oneT idT mulT oneT_is_mul_id J2). 
       unfold brel_product. unfold uop_rap. unfold uop_predicate_reduce.        
       assert (J5 : P (idS, idT) = false). 
          compute. apply symS in J3. 
          assert(J5 : eqS idS zeroS = false). exact (brel_transitive_f2 _ eqS symS tranS _ _ _ J3 oneS_not_zeroS).
          rewrite J5. apply symT in J4.
          assert(J6 : eqT idT zeroT = false).  exact (brel_transitive_f2 _ eqT symT tranT _ _ _ J4 oneT_not_zeroT).
          rewrite J6. reflexivity. 
       rewrite J5. rewrite refS. rewrite refT. compute; auto. 
Qed. 

Lemma  bop_rap_add_is_id : bop_is_id (S * T)
                                     (brel_reduce uop_rap (brel_product eqS eqT))
                                     bop_rap_add
                                     (zeroS, zeroT).
Proof.  apply bop_full_reduce_is_id; auto. 
        apply brel_product_reflexive; auto.
        apply brel_product_transitive; auto.
        apply uop_predicate_reduce_congruence; auto.
        apply brel_product_reflexive; auto.
        apply P_congruence.
        apply uop_predicate_reduce_idempotent; auto.
        apply brel_product_reflexive; auto.
        apply bop_product_congruence; auto.
        apply uop_rap_add_preserves_id; auto. 
        apply bop_product_is_id; auto. 
Qed.  

Lemma  bop_rap_add_is_ann : bop_is_ann (S * T)
                                     (brel_reduce uop_rap (brel_product eqS eqT))
                                     bop_rap_add
                                     (oneS, oneT).
Proof.  apply bop_full_reduce_is_ann; auto. 
        apply brel_product_reflexive; auto.
        apply brel_product_transitive; auto.
        apply uop_predicate_reduce_congruence; auto.
        apply brel_product_reflexive; auto.
        apply P_congruence.
        apply bop_product_congruence; auto.        
        apply uop_rap_add_preserves_ann; auto. 
        apply bop_product_is_ann; auto. 
Qed.  

Lemma  bop_rap_mul_is_ann : bop_is_ann (S * T)
                                     (brel_reduce uop_rap (brel_product eqS eqT))
                                     bop_rap_mul
                                     (zeroS, zeroT).
Proof.  apply bop_full_reduce_is_ann; auto. 
        apply brel_product_reflexive; auto.
        apply brel_product_transitive; auto.
        apply uop_predicate_reduce_congruence; auto.
        apply brel_product_reflexive; auto.
        unfold pred_congruence. apply P_congruence.
        apply bop_product_congruence; auto.
        apply uop_rap_mul_preserves_ann; auto.
        apply bop_product_is_ann; auto. 
Qed.

Lemma  bop_rap_mul_is_id : bop_is_id (S * T)
                                     (brel_reduce uop_rap (brel_product eqS eqT))
                                     bop_rap_mul
                                     (oneS, oneT).
Proof.  apply bop_full_reduce_is_id; auto. 
        apply brel_product_reflexive; auto.
        apply brel_product_transitive; auto.
        apply uop_predicate_reduce_congruence; auto.
        apply brel_product_reflexive; auto.
        apply P_congruence.
        apply uop_predicate_reduce_idempotent; auto.        
        apply brel_product_reflexive; auto.
        apply bop_product_congruence; auto.
        apply uop_rap_mul_preserves_id; auto.
        apply bop_product_is_id; auto. 
Qed.


Lemma bop_rap_add_mul_left_distributive :
  bop_left_distributive S eqS addS mulS ->
  bop_left_distributive T eqT addT mulT ->   
      bop_left_distributive (S * T) (brel_reduce uop_rap (brel_product eqS eqT)) bop_rap_add bop_rap_mul. 
Proof. intros ldistS ldistT.
       apply bop_fpr_left_distributive. 
       apply brel_product_reflexive; auto.
       apply brel_product_symmetric; auto.       
       apply brel_product_transitive; auto.
       apply P_true.
       apply P_congruence.
       apply P_add_decompose.
       apply P_mul_decompose.        
       apply bop_product_congruence; auto.
       apply bop_product_congruence; auto.
       apply bop_product_is_id; auto.
       apply bop_product_is_ann; auto.        
       apply bop_product_left_distributive; auto.  
Qed.


Lemma bop_rap_add_mul_right_distributive :
  bop_right_distributive S eqS addS mulS ->
  bop_right_distributive T eqT addT mulT ->   
     bop_right_distributive (S * T) (brel_reduce uop_rap (brel_product eqS eqT)) bop_rap_add bop_rap_mul.
Proof. intros rdistS rdistT.
       apply bop_fpr_right_distributive. 
       apply brel_product_reflexive; auto.
       apply brel_product_symmetric; auto.       
       apply brel_product_transitive; auto.
       apply P_true.
       apply P_congruence.
       apply P_add_decompose.
       apply P_mul_decompose.        
       apply bop_product_congruence; auto.
       apply bop_product_congruence; auto.
       apply bop_product_is_id; auto.
       apply bop_product_is_ann; auto.        
       apply bop_product_right_distributive; auto.  
Qed.


End ReduceAnnihilators.
