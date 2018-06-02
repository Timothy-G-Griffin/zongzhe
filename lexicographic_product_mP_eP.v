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
Require Import CAS.lexicographic_product.

Section Lexicographic_product_minPlusWithCeiling_ElementaryPath.


Variable ceiling : nat.
Variable c : cas_constant.
Close Scope nat.
Definition T := cas_constant + list nat.

Definition min_plus_ceiling_dioid := min_plus_dioid ceiling.
Definition elementary_path_bioid := min_app_non_distributive_dioid c.

Definition add1 := csdioid_add nat min_plus_ceiling_dioid.
Definition mul1 := csdioid_mul nat min_plus_ceiling_dioid.
Definition add2 := sbioid_add T elementary_path_bioid.
Definition mul2 := sbioid_mul T elementary_path_bioid.

Definition eqN := csdioid_eq nat min_plus_ceiling_dioid.

Lemma refN: brel_reflexive nat eqN.
Proof. apply brel_reduce_nat_reflexive.
Qed.

Lemma symN: brel_symmetric nat eqN.
Proof. apply brel_reduce_nat_symmetric.
Qed.

Lemma transN: brel_transitive nat eqN.
Proof. apply brel_reduce_nat_transitive.
Qed.

Lemma congN: brel_congruence nat eqN eqN.
Proof. apply brel_reduce_nat_congruence.
Qed.

Definition eqT := sbioid_eq T elementary_path_bioid.

Lemma refT: brel_reflexive T eqT.
Proof. apply brel_reduce_list_const_reflexive.
Qed.

Lemma symT: brel_symmetric T eqT.
Proof. apply brel_reduce_list_const_symmetric.
Qed.

Lemma transT: brel_transitive T eqT.
Proof. apply brel_reduce_list_const_transitive.
Qed.

Lemma congT: brel_congruence T eqT eqT.
Proof. apply brel_reduce_list_const_congruence.
Qed.

Definition M := nat * T.
Definition eqM : brel M := brel_product eqN eqT.

Definition add :binary_op M := bop_llex eqN add1 add2.
Definition mul :binary_op M:= bop_product mul1 mul2.

Lemma bop_congruence_M_add : bop_congruence M eqM add.
Proof. apply bop_lexicographic_product_congruence.
       exact ceiling.
       exact (inl c).
       exact congN.
       exact congT.
       exact refN.
       exact symN.
       exact transN.
       exact refT.
       exact symT.
       exact transT.
       exact (bop_nat_min_associative ceiling).
       exact (bop_nat_min_commutative ceiling).
       exact (bop_nat_min_selective ceiling).
       exact (bop_nat_min_congruence ceiling).
       exact (bop_list_min_congruence c).
Qed.

Lemma bop_associative_M_add : bop_associative M eqM add.
Proof. apply bop_lexicographic_product_associative.
       exact ceiling.
       exact (inl c).
       exact congN.
       exact congT.
       exact refN.
       exact symN.
       exact transN.
       exact refT.
       exact symT.
       exact transT.
       exact (bop_nat_min_associative ceiling).
       exact (bop_nat_min_commutative ceiling).
       exact (bop_nat_min_selective ceiling).
       exact (bop_list_min_associative c).
Qed.

Open Scope nat.
Definition zero1 : nat := ceiling.
Definition one1  : nat := 0.
Definition zero2 : T := inl c.
Definition one2  : T := inr nil.
Definition zero  : M := (zero1,zero2).
Definition one   : M := (one1,one2).

Variable  One_not_Zero : eqN one1 zero1 = false. 

Definition P := reduce_annihilators.P nat T eqN eqT zero1 zero2.
Definition P_congruence_ann := reduce_annihilators.P_congruence.
Definition P_true_ann := reduce_annihilators.P_true.

Lemma P_true : pred_true M P zero.
Proof. apply P_true_ann.
       exact refN.
Qed. 

Lemma P_cong : pred_congruence M eqM P.
Proof. apply P_congruence_ann.
       exact symN.
       exact transN.
       exact symT.
       exact transT.
Qed.

Definition uop_rap : unary_op M := reduce_annihilators.uop_rap nat T eqN eqT zero1 zero2.
Definition brel_eq_M :brel M := brel_reduce uop_rap eqM. 

Definition bop_rap_add : binary_op M := bop_fpr zero P add.
Definition bop_rap_mul : binary_op M := bop_fpr zero P mul.

Lemma brel_M_reflexive: brel_reflexive M eqM.
Proof.  apply brel_product_reflexive.
    exact refN.
    exact refT.
Qed.

Lemma brel_M_symmetric : brel_symmetric M eqM.
Proof. 
    apply brel_product_symmetric.
       exact symN.
       exact symT.
Qed.

Lemma brel_M_transitive : brel_transitive M eqM.
Proof. 
    apply brel_product_transitive.
       exact transN.
       exact transT.
Qed.

Lemma brel_M_congruence : brel_congruence M eqM eqM.
Proof. 
    apply brel_product_congruence.
       exact congN.
       exact congT.
Qed.

Lemma brel_eq_M_reflexive : brel_reflexive M brel_eq_M.
Proof. apply brel_reduce_reflexive.
       exact brel_M_reflexive.
Qed.

Lemma brel_eq_M_symmetric : brel_symmetric M brel_eq_M.
Proof. apply brel_reduce_symmetric.
       exact brel_M_symmetric.
Qed.
 

Lemma brel_eq_M_transitive : brel_transitive M brel_eq_M.
Proof. apply brel_reduce_transitive.
       exact brel_M_transitive.
Qed. 

Lemma brel_eq_M_congruence : brel_congruence M brel_eq_M brel_eq_M.
Proof. apply brel_reduce_congruence; auto.
      exact  brel_M_congruence.
Qed.  

Lemma P_decompose_add : pred_bop_decompose M P add.
Proof. intros s1 s2 H1.
        assert (A : bop_selective M eqM add).
        apply bop_lexicographic_product_selective; auto.
        exact symN.
        exact transN.
        exact refT.
       apply bop_nat_min_selective.
       apply bop_list_min_selective;auto.
       assert (B := A s1 s2).
       destruct B;
       assert (C := P_cong _ _ e); rewrite C in H1. left. auto. right. auto.
Qed.

Open Scope bool.

Lemma orb_is_true_left : ∀ b1 b2 : bool, b1 || b2 = true → (b1 = true) + (b2 = true). 
Proof. induction b1; induction b2; simpl; intros.  
       left; reflexivity. 
       left. reflexivity. 
       right. reflexivity. 
       left. assumption. 
Defined. 

Lemma orb_is_true_right : ∀ b1 b2 : bool, (b1 = true) + (b2 = true) → b1 || b2 = true. 
Proof. induction b1; induction b2; simpl; intros [H | H]; auto. Defined. 

Lemma P_compose_mul : pred_bop_compose M P mul.
Proof. intros s1 s2 H1. destruct s1,s2.
       unfold mul,bop_product.
       unfold P,reduce_annihilators.P in H1.
       destruct H1;
       apply orb_is_true_left in e;
       destruct e; unfold P,reduce_annihilators.P.
       unfold zero1,mul1,csdioid_mul,csdioid_mul,min_plus_ceiling_dioid,min_plus_dioid.
       assert (A := bop_is_ann_ceiling_plus_ceiling ceiling n0).
       destruct A as [A _].
       assert (B := bop_nat_plus_congruence ceiling n n0 ceiling n0 e (refN n0)).
       assert (C := transN _ _ _ B A).
       rewrite C. auto.
       unfold zero2,mul2,sbioid_mul,elementary_path_bioid,min_app_non_distributive_dioid.
       assert (A := bop_is_ann_app c t0).
       destruct A as [A _].
       assert (B := bop_list_app_congruence c t t0 (inl c) t0 e (refT t0)).
       assert (C := transT _ _ _ B A).
       apply orb_is_true_right. right.
       exact C.
       unfold zero1,mul1,csdioid_mul,csdioid_mul,min_plus_ceiling_dioid,min_plus_dioid.
       assert (A := bop_is_ann_ceiling_plus_ceiling ceiling n).
       destruct A as [_ A].
       assert (B := bop_nat_plus_congruence ceiling n n0 n ceiling (refN n) e).
       assert (C := transN _ _ _ B A).
       rewrite C. auto.
       unfold zero2,mul2,sbioid_mul,elementary_path_bioid,min_app_non_distributive_dioid.
       assert (A := bop_is_ann_app c t).
       destruct A as [_ A].
       assert (B := bop_list_app_congruence c t t0 t (inl c) (refT t) e).
       assert (C := transT _ _ _ B A).
       apply orb_is_true_right. right.
       exact C.
Qed.



Lemma bop_rap_add_associative :  bop_associative M brel_eq_M bop_rap_add.
Proof. apply bop_associative_fpr_decompositional_id.
    apply brel_M_reflexive;auto.
    apply brel_M_symmetric;auto.
    apply brel_M_transitive;auto.
    apply P_true.
    apply P_cong.
    exact bop_congruence_M_add.
    exact bop_associative_M_add.
       apply P_decompose_add.
       apply bop_lexicographic_product_is_id.
       exact symN.
       exact transN.
       exact refT.
          apply bop_is_id_ceiling_min_ceiling.
          apply bop_is_id_min.
Qed.


Lemma bop_rap_add_commutative :  bop_commutative M brel_eq_M bop_rap_add.
Proof. apply bop_full_reduce_commutative.
    apply uop_predicate_reduce_congruence; auto.
    apply brel_product_reflexive; auto.
       apply min_plus_ceiling_reduction.brel_reduce_nat_reflexive; auto.
       apply elementary_path.brel_reduce_list_const_reflexive;auto.
       apply P_cong.
      apply bop_lexicographic_product_commutative.
      exact symN.
      exact transN.
      exact refT.
       apply bop_nat_min_selective.
       apply bop_nat_min_commutative.
       apply bop_list_min_commutative.
Qed.


       
Lemma bop_rap_add_congruence : bop_congruence M brel_eq_M bop_rap_add.
Proof. apply bop_full_reduce_congruence; auto.
       apply uop_predicate_reduce_congruence; auto.
       exact brel_M_reflexive.
       exact P_cong.
       exact bop_congruence_M_add.
Qed.

Lemma bop_rap_add_selective : bop_selective M brel_eq_M bop_rap_add.
Proof. apply bop_full_reduce_selective; auto.
       apply brel_M_transitive;auto.
       apply uop_predicate_reduce_congruence; auto.
       apply brel_M_reflexive;auto.
       exact P_cong.
       apply uop_predicate_reduce_idempotent;auto.
       apply brel_M_reflexive.
       apply bop_lexicographic_product_selective; auto.
       exact symN.
       exact transN.
       exact refT.
       apply bop_nat_min_selective.
       apply bop_list_min_selective;auto.
Qed.

Lemma bop_rap_mul_associative :  bop_associative M brel_eq_M bop_rap_mul.
Proof. apply bop_rap_mul_associative_compositional.
       exact refN.
       exact symN.
       exact transN.
       exact refT.
       exact symT.
       exact transT.
       apply min_plus_ceiling_reduction.bop_nat_plus_congruence.
       apply elementary_path.bop_list_app_congruence.
        apply min_plus_ceiling_reduction.bop_nat_plus_associative.
        apply elementary_path.bop_list_app_associative.
        apply bop_is_ann_ceiling_plus_ceiling.
        apply bop_is_ann_app.
Qed.


Lemma bop_rap_mul_congruence : bop_congruence M brel_eq_M bop_rap_mul.
Proof. apply bop_full_reduce_congruence; auto.
       apply uop_predicate_reduce_congruence; auto.
       exact brel_M_reflexive.
       exact P_cong.
       apply bop_product_congruence; auto.
       apply min_plus_ceiling_reduction.bop_nat_plus_congruence.
       apply elementary_path.bop_list_app_congruence.
Qed.

Lemma bop_mul_not_commutative : bop_not_commutative M eqM mul.
Proof. apply bop_product_not_commutative_right.
       exact ceiling.
       apply min_plus_ceiling_reduction.brel_reduce_nat_reflexive; auto.
       apply bop_list_app_not_commutative.
Qed.

Lemma bop_rap_mul_not_commutative : bop_not_commutative M brel_eq_M bop_rap_mul.
Proof. exists ((0,inr(1::nil)),(0,inr(2::nil))).
       unfold bop_rap_mul,mul,bop_product.
       unfold bop_fpr,uop_predicate_reduce,mul1,mul2.
       unfold csdioid_mul,min_plus_ceiling_dioid,min_plus_dioid,bop_nat_plus.
       unfold bop_fpr,uop_predicate_reduce,bop_full_reduce.
       unfold P,reduce_annihilators.P. 
       assert (A := One_not_Zero). unfold one1 in A. rewrite A. simpl.
       assert (B : min_plus_ceiling_reduction.P ceiling 0 = false).
       case_eq(ceiling); intro C. unfold zero1 in A. rewrite C in A. compute in A. rewrite C in A. discriminate A.
       compute. auto.
       rewrite B. unfold plus. simpl. rewrite B.
       rewrite A. simpl.
       unfold bop_list_app,elementary_path.P,bop_fpr,uop_predicate_reduce.
       unfold appT,bop_add_ann,appS,bop_full_reduce,app. simpl.
       unfold brel_eq_M,uop_rap,reduce_annihilators.uop_rap,reduce_annihilators.P.
       unfold brel_reduce,uop_predicate_reduce. rewrite A; simpl.
       unfold eqT,sbioid_eq,elementary_path_bioid,min_app_non_distributive_dioid.
       unfold uop_list,uop_predicate_reduce,elementary_path.P,brel_reduce. simpl.
       rewrite refN. simpl.
       auto.                     
Qed.

Lemma bop_rap_mul_commutative_decidable : bop_commutative_decidable M brel_eq_M bop_rap_mul.
Proof. right. apply bop_rap_mul_not_commutative.
Qed.


Lemma bop_is_id_add_zero : bop_is_id M brel_eq_M bop_rap_add zero.
Proof. apply bop_full_reduce_is_id.
       apply brel_M_reflexive.
       apply brel_M_transitive.
       apply uop_predicate_reduce_congruence; auto.
       apply brel_M_reflexive;auto.
       exact P_cong.
       apply uop_predicate_reduce_idempotent;auto.
       apply brel_M_reflexive.
       exact bop_congruence_M_add.
       unfold uop_preserves_id. intros s H.
       assert (A : bop_is_id M eqM add zero). 
       apply bop_lexicographic_product_is_id.
       apply min_plus_ceiling_reduction.brel_reduce_nat_symmetric; auto.
       apply min_plus_ceiling_reduction.brel_reduce_nat_transitive; auto.
       apply elementary_path.brel_reduce_list_const_reflexive;auto.
       apply bop_is_id_ceiling_min_ceiling.
       apply bop_is_id_min.
       assert (B := bop_is_id_unique M eqM brel_M_symmetric brel_M_transitive _ _ add H A).
       unfold uop_predicate_reduce.
       assert (C := P_cong _ _ B).
       assert (D := P_true). unfold pred_true in D.
       rewrite D in C. rewrite C. apply brel_M_symmetric. exact B.
       apply bop_lexicographic_product_is_id.
       apply min_plus_ceiling_reduction.brel_reduce_nat_symmetric; auto.
       apply min_plus_ceiling_reduction.brel_reduce_nat_transitive; auto.
       apply elementary_path.brel_reduce_list_const_reflexive;auto.
       apply bop_is_id_ceiling_min_ceiling.
       apply bop_is_id_min.
Qed.

Lemma andb_is_true_elim : ∀ b1 b2 : bool, b1 && b2 = true → (b1 = true) * (b2 = true). 
Proof. induction b1; induction b2; simpl; intros.  
       split; reflexivity. 
       split. reflexivity. assumption. 
       split. assumption. reflexivity. 
       split. assumption. assumption. 
Defined. 

Lemma bop_is_ann_add_one : bop_is_ann M brel_eq_M bop_rap_add one.
Proof. apply bop_full_reduce_is_ann.
    apply brel_M_reflexive.
    apply brel_M_transitive.
    apply uop_predicate_reduce_congruence; auto.
    apply brel_M_reflexive;auto.
    exact P_cong.
    exact bop_congruence_M_add.
    unfold uop_preserves_ann. intros s H.
       assert (A : bop_is_ann M eqM add one). 
       apply bop_lexicographic_product_is_ann.
       apply min_plus_ceiling_reduction.brel_reduce_nat_symmetric; auto.
       apply min_plus_ceiling_reduction.brel_reduce_nat_transitive; auto.
       apply elementary_path.brel_reduce_list_const_reflexive;auto.
       apply bop_is_ann_ceiling_min_zero.
       apply bop_is_ann_min.
       assert (B := bop_is_ann_unique M eqM brel_M_symmetric brel_M_transitive _ _ add H A).
       unfold uop_predicate_reduce,P,reduce_annihilators.P.
       destruct s. unfold one in B. unfold eqM,brel_product in B.
       apply andb_is_true_elim in B. destruct B as [B C].
       assert (D := brel_transitive_f2 nat eqN symN transN _ _ _ B One_not_Zero).
       rewrite D; simpl.
       assert (E : eqT t zero2 = false).
       assert (F : eqT one2 zero2 = false).
       compute. auto.
       assert (G := brel_transitive_f2 T eqT symT transT _ _ _ C F).
       exact G. rewrite E. apply brel_M_reflexive.
    apply bop_lexicographic_product_is_ann.
    apply min_plus_ceiling_reduction.brel_reduce_nat_symmetric; auto.
       apply min_plus_ceiling_reduction.brel_reduce_nat_transitive; auto.
       apply elementary_path.brel_reduce_list_const_reflexive;auto.
       apply bop_is_ann_ceiling_min_zero.
       apply bop_is_ann_min.
Qed.

Lemma bop_is_id_mul_one : bop_is_id M brel_eq_M bop_rap_mul one.
Proof. apply bop_rap_mul_is_id. 
    apply min_plus_ceiling_reduction.brel_reduce_nat_reflexive; auto.
    apply min_plus_ceiling_reduction.brel_reduce_nat_symmetric; auto.
    apply min_plus_ceiling_reduction.brel_reduce_nat_transitive; auto.
    apply elementary_path.brel_reduce_list_const_reflexive;auto.
    exact symT.
    exact transT.
       apply min_plus_ceiling_reduction.bop_nat_plus_congruence.
       apply elementary_path.bop_list_app_congruence.
        apply bop_is_id_ceiling_plus_zero.
        apply bop_is_id_app.
        exact One_not_Zero. 
    compute. auto.
Qed. 

Lemma bop_is_ann_mul_zero : bop_is_ann M brel_eq_M bop_rap_mul zero.
Proof. apply bop_rap_mul_is_ann.
    apply min_plus_ceiling_reduction.brel_reduce_nat_reflexive; auto.
    apply min_plus_ceiling_reduction.brel_reduce_nat_symmetric; auto.
    apply min_plus_ceiling_reduction.brel_reduce_nat_transitive; auto.
    apply elementary_path.brel_reduce_list_const_reflexive;auto.
    exact symT.
    exact transT.
       apply min_plus_ceiling_reduction.bop_nat_plus_congruence.
       apply elementary_path.bop_list_app_congruence.
        apply bop_is_ann_ceiling_plus_ceiling.
        apply bop_is_ann_app.
Qed.


Lemma bop_not_left_distributive : properties.bop_not_left_distributive M eqM add mul.
Proof. apply lexicographic_product.bop_not_left_distributive.
       exact ceiling.
       exact (inl c).
       exact congN.
       exact congT.
       exact mul1.
       exact mul2.
       exact refN.
       exact symN.
       exact transN.
       exact refT.
       exact symT.
       exact transT.
       apply bop_not_left_distributive_min_app.
Qed. 

Lemma bop_not_right_distributive : properties.bop_not_right_distributive M eqM add mul.
Proof. apply lexicographic_product.bop_not_right_distributive.
       exact ceiling.
       exact (inl c).
       exact congN.
       exact congT.
       exact mul1.
       exact mul2.
       exact refN.
       exact symN.
       exact transN.
       exact refT.
       exact symT.
       exact transT.
       apply bop_not_right_distributive_min_app.
Qed. 

Lemma bop_not_left_distributive_add_mul : properties.bop_not_left_distributive M brel_eq_M bop_rap_add bop_rap_mul.
Proof. exists ((0,inr (1::nil)), (0,inr (1::nil)),(0,inr (2::3::nil))). 
       unfold bop_rap_add,add,bop_fpr,bop_full_reduce.
       unfold uop_predicate_reduce. simpl.
       assert (A := One_not_Zero). unfold one1 in A. rewrite A. simpl.
       rewrite refN. rewrite refN.
       unfold add1,csdioid_add,min_plus_ceiling_dioid,min_plus_dioid. 
       unfold bop_nat_min,bop_fpr,bop_full_reduce,uop_predicate_reduce.
       assert (B : min_plus_ceiling_reduction.P ceiling 0 = false).
       case_eq(ceiling); intro C. unfold zero1 in A. rewrite C in A. compute in A. rewrite C in A. discriminate A.
       compute. auto. rewrite B. simpl. rewrite B. rewrite A. simpl.
       unfold bop_rap_mul,bop_fpr,uop_predicate_reduce,bop_full_reduce.
       simpl. rewrite A. simpl.
       unfold mul1,csdioid_mul,min_plus_ceiling_dioid,min_plus_dioid.
       unfold bop_nat_plus,bop_fpr,uop_predicate_reduce,bop_full_reduce.
       rewrite B. simpl. rewrite B. rewrite A. simpl.
       rewrite refN. simpl. rewrite A. simpl.
       assert (C := brel_symmetric_false nat eqN symN _ _ A).
       rewrite C. rewrite refN. simpl. rewrite B. unfold zero1.
       assert (D : min_plus_ceiling_reduction.P ceiling ceiling = true). apply min_plus_ceiling_reduction.P_true.
       rewrite D. 
       assert (E : min ceiling 0 = 0).
       case_eq(ceiling). auto. auto.
       rewrite E. rewrite B. unfold zero1 in C. rewrite C. unfold zero1 in A. rewrite A. simpl.
       unfold brel_llt.  unfold brel_conjunction. unfold brel_llte.
       rewrite D. rewrite B. rewrite E. rewrite B. rewrite C. simpl.
       unfold mul2,sbioid_mul,elementary_path_bioid,min_app_non_distributive_dioid.
       unfold bop_list_app,appT,bop_fpr,uop_predicate_reduce,bop_full_reduce. simpl.
       unfold brel_eq_M,uop_rap,brel_reduce,reduce_annihilators.uop_rap,uop_predicate_reduce,reduce_annihilators.P.
       unfold zero. rewrite refN. simpl. unfold zero1. rewrite A. simpl.
       rewrite C. auto.
Qed.


Lemma bop_not_right_distributive_add_mul : properties.bop_not_right_distributive M brel_eq_M bop_rap_add bop_rap_mul.
Proof. exists ((0,inr (1::nil)), (0,inr (1::nil)),(0,inr (2::3::nil))). 
    unfold bop_rap_add,add,bop_fpr,bop_full_reduce.
    unfold uop_predicate_reduce. simpl.
    assert (A := One_not_Zero). unfold one1 in A. rewrite A. simpl.
    rewrite refN. rewrite refN.
    unfold add1,csdioid_add,min_plus_ceiling_dioid,min_plus_dioid. 
    unfold bop_nat_min,bop_fpr,bop_full_reduce,uop_predicate_reduce.
    assert (B : min_plus_ceiling_reduction.P ceiling 0 = false).
    case_eq(ceiling); intro C. unfold zero1 in A. rewrite C in A. compute in A. rewrite C in A. discriminate A.
    compute. auto. rewrite B. simpl. rewrite B. rewrite A. simpl.
    unfold bop_rap_mul,bop_fpr,uop_predicate_reduce,bop_full_reduce.
    simpl. rewrite A. simpl.
    unfold mul1,csdioid_mul,min_plus_ceiling_dioid,min_plus_dioid.
    unfold bop_nat_plus,bop_fpr,uop_predicate_reduce,bop_full_reduce.
    rewrite B. simpl. rewrite B. rewrite A. simpl.
    rewrite refN. simpl. rewrite A. simpl.
    assert (C := brel_symmetric_false nat eqN symN _ _ A).
    rewrite C. rewrite refN. simpl. rewrite B. unfold zero1.
    assert (D : min_plus_ceiling_reduction.P ceiling ceiling = true). apply min_plus_ceiling_reduction.P_true.
    rewrite D. 
    assert (E : min ceiling 0 = 0).
    case_eq(ceiling). auto. auto.
    rewrite E. rewrite B. unfold zero1 in C. rewrite C. unfold zero1 in A. rewrite A. simpl.
    unfold brel_llt.  unfold brel_conjunction. unfold brel_llte.
    rewrite D. rewrite B. rewrite E. rewrite B. rewrite C. simpl.
    unfold mul2,sbioid_mul,elementary_path_bioid,min_app_non_distributive_dioid.
    unfold bop_list_app,appT,bop_fpr,uop_predicate_reduce,bop_full_reduce. simpl.
    unfold brel_eq_M,uop_rap,brel_reduce,reduce_annihilators.uop_rap,uop_predicate_reduce,reduce_annihilators.P.
    unfold zero. rewrite refN. simpl. unfold zero1. rewrite A. simpl.
    rewrite C. auto.
Qed.

Lemma bop_left_distributive_add_mul_decidable : bop_left_distributive_decidable M brel_eq_M bop_rap_add bop_rap_mul.
Proof. right. apply  bop_not_left_distributive_add_mul.
Qed.

Lemma bop_right_distributive_add_mul_decidable : bop_right_distributive_decidable M brel_eq_M bop_rap_add bop_rap_mul.
Proof. right. apply  bop_not_right_distributive_add_mul.
Qed.

Definition eqv_proofs_eq_T : eqv_proofs M brel_eq_M
:= {| 
     eqv_reflexive   := brel_eq_M_reflexive
   ; eqv_transitive  := brel_eq_M_transitive
   ; eqv_symmetric   := brel_eq_M_symmetric
   ; eqv_congruence  := brel_eq_M_congruence
   ; eqv_witness     := zero
|}. 


Definition min_proofs  : 
commutative_selective_semigroup_proofs M brel_eq_M bop_rap_add
:= {|
  cssg_associative   := bop_rap_add_associative
; cssg_congruence    := bop_rap_add_congruence
; cssg_commutative   := bop_rap_add_commutative
; cssg_selective     := bop_rap_add_selective                                       
|}.

Definition app_proofs: 
semigroup_proofs M brel_eq_M bop_rap_mul
:= {|
sg_associative   := bop_rap_mul_associative
  ; sg_congruence    := bop_rap_mul_congruence
; sg_commutative_d    := bop_rap_mul_commutative_decidable                                                
|}.


Definition min_app_non_distributive_dioid_proofs : 
bioid_proof M brel_eq_M bop_rap_add bop_rap_mul zero one
:= {|  
bioid_left_distributive_decidable := bop_left_distributive_add_mul_decidable
; bioid_right_distributive_decidable := bop_right_distributive_add_mul_decidable
; bioid_zero_is_add_id     := bop_is_id_add_zero
; bioid_one_is_mul_id      := bop_is_id_mul_one 
; bioid_zero_is_mul_ann    := bop_is_ann_mul_zero
; bioid_one_is_add_ann     := bop_is_ann_add_one
|}.


Definition min_app_non_distributive_dioid : selective_bioid M
:= {|
    sbioid_eq         := brel_eq_M
  ; sbioid_add        := bop_rap_add
  ; sbioid_mul        := bop_rap_mul                                 
  ; sbioid_zero       := zero
  ; sbioid_one        := one
  ; sbioid_eqv        := eqv_proofs_eq_T
  ; sbioid_add_pfs    := min_proofs
  ; sbioid_mul_pfs    := app_proofs
  ; sbioid_pfs        := min_app_non_distributive_dioid_proofs
|}.

End Lexicographic_product_minPlusWithCeiling_ElementaryPath.