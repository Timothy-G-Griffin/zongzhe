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
Require Import CAS.reduction_theory.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool. 
Require Import Coq.Arith.Arith.
Open Scope nat.
Open Scope list_scope.



Section ElementaryPath.

Definition brel_list (S : Type)(eq : brel S)  := λ x y, brel_list eq x y.

Definition S := nat.
Definition eqS := Arith.EqNat.beq_nat.
Variable refS : brel_reflexive S eqS.
Variable symS : brel_symmetric S eqS.
Variable tranS : brel_transitive S eqS.
Variable c : cas_constant.

Definition brel_list_S  : brel (list S) := brel_list S eqS.


Lemma beq_nat_to_prop  : ∀ s t: nat, beq_nat s t = true -> s = t. 
Proof.  induction s;  induction t; simpl; intro H; auto; discriminate. Defined. 

Lemma brel_list_to_prop  : ∀ s t: list S, brel_list_S s t = true -> s = t.
Proof. intros s t H.
       induction s,t. auto.
       compute in H. discriminate.
       compute in H. discriminate.
       Admitted.


Lemma brel_list_ref : brel_reflexive (list S) brel_list_S.
Proof. intro s. induction s.
       auto.  unfold brel_list_S, brel_list, basic.brel_list. rewrite (refS a);simpl. 
       fold (basic.brel_list eqS s). unfold brel_list_S, brel_list in IHs. exact IHs.
Qed.

Lemma brel_list_sym : brel_symmetric (list S) brel_list_S.
Proof. intros a b H.
       assert(A := brel_list_to_prop a b H). rewrite A. apply brel_list_ref.
Qed.

Lemma brel_list_tran : brel_transitive (list S) brel_list_S.
Proof. intros x y z H1 H2.  
    assert(A := brel_list_to_prop x y H1). rewrite A.
    assert(B := brel_list_to_prop y z H2). rewrite B. 
    apply brel_list_ref.
Qed.

Lemma brel_list_congruence : brel_congruence (list S) brel_list_S brel_list_S.
Proof. intros x y m n H1 H2.
    assert(A := brel_list_to_prop x m H1). rewrite A.
    assert(B := brel_list_to_prop y n H2). rewrite B.
    auto.
Qed. 

Definition brel_list_const : brel (cas_constant + list S ) := brel_add_constant brel_list_S c. 

Lemma brel_list_const_ref : brel_reflexive (cas_constant + list S) brel_list_const.
Proof. intro s. destruct s. compute; auto.
       unfold brel_list_const, brel_add_constant. apply brel_list_ref.
Qed.

Lemma brel_list_const_sym : brel_symmetric (cas_constant + list S) brel_list_const.
Proof. intros a b. unfold brel_list_const, brel_add_constant.
       destruct a,b. auto. intro. discriminate. intro. discriminate.
       apply brel_list_sym.
Qed.

Lemma brel_list_const_tran : brel_transitive (cas_constant + list S) brel_list_const.
Proof. intros x y z. unfold brel_list_const, brel_add_constant.
       destruct x, y, z. auto. 
       intros; discriminate.
       intros; discriminate.
       intros; discriminate.
       intros; discriminate.
       intros; discriminate.
       intros; discriminate.
       apply brel_list_tran.
Qed.


Lemma brel_list_const_congruence : brel_congruence (cas_constant + list S) brel_list_const brel_list_const.
Proof. intros x y m n.
    unfold brel_list_const, brel_add_constant.
    destruct x, y, m, n.
    auto.
    intros; discriminate.
    intros; discriminate.
    intros; discriminate.
    intros; discriminate.
    auto.
    intros; discriminate.
    intros; discriminate.
    intros; discriminate.
    intros; discriminate.
    auto.
    intros; discriminate.
    intros; discriminate.
    intros; discriminate.
    intros; discriminate.
    apply brel_list_congruence.
Qed.

Definition app := List.app.
Definition appS := app S.
Definition appT := bop_add_ann appS c.

Fixpoint elem_in_list  (S : Type)(eqS : brel S)(x : S)(l : list S) : bool :=
match l with
| nil => false
| y :: yl => orb (eqS x y) (elem_in_list S eqS x yl)
end.

Fixpoint dup_in_list (S : Type)(eqS : brel S)(l : list S): bool :=
match l with
| nil => false
| y :: yl =>  orb (elem_in_list S eqS y yl) (dup_in_list S eqS yl)
end.

Lemma dup_list_cong (l1 l2 : list S): brel_list S eqS l1 l2 = true -> dup_in_list S eqS l1 = dup_in_list S eqS l2.
Proof. intros H.
       assert (A := brel_list_to_prop l1 l2 H).
       rewrite A. induction l2. compute. auto. simpl.  
       case_eq(elem_in_list S eqS a l2); intro K;
       case_eq(dup_in_list S eqS l2); intro L; auto.
Qed. 

Close Scope nat.
Definition T := cas_constant + list S.

Definition P : T -> bool :=  λ x,
match x with
| inr xl => dup_in_list S eqS xl
| inl _ => true
end.

Definition uop_list : unary_op T := uop_predicate_reduce (inl c) P.

Lemma brel_reduce_list_const_reflexive : brel_reflexive T (brel_reduce uop_list brel_list_const).
Proof. apply brel_reduce_reflexive.
       apply brel_list_const_ref.
Qed.

Lemma brel_reduce_list_const_symmetric  : brel_symmetric T (brel_reduce uop_list brel_list_const).
Proof. apply brel_reduce_symmetric.
       apply brel_list_const_sym.
Qed.

Lemma brel_reduce_list_const_transitive : brel_transitive T (brel_reduce uop_list brel_list_const).
  Proof. apply brel_reduce_transitive.
         apply brel_list_const_tran; auto.
  Qed.

Lemma brel_reduce_list_const_congruence : brel_congruence T (brel_reduce uop_list brel_list_const) (brel_reduce uop_list brel_list_const).
  Proof. apply brel_reduce_congruence; auto. 
         apply brel_list_const_congruence; auto. 
  Qed.

Lemma P_true : pred_true T P (inl c).
Proof. compute. auto.
Qed.

Lemma P_congruence : pred_congruence T brel_list_const P.
Proof. intros n1 n2; intro H. induction n1,n2. unfold P. auto.
      unfold brel_list_const,brel_add_constant,brel_list_S in H. discriminate.
      unfold brel_list_const,brel_add_constant,brel_list_S in H. discriminate.
      unfold brel_list_const,brel_add_constant,brel_list_S in H.
      apply dup_list_cong. exact H.
Qed.

Lemma beq_list_appS_congruence : 
   ∀ s1 s2 t1 t2 : list S,
   brel_list_S s1 t1 = true
   → brel_list_S s2 t2 = true → brel_list_S (appS s1 s2) (appS t1 t2) = true.
Proof. intros s1 s2 t1 t2 H1 H2.
       assert (A := brel_list_to_prop s1 t1 H1).
       assert (B := brel_list_to_prop s2 t2 H2).
       rewrite A,B. apply brel_list_ref.
Qed.

Lemma bop_list_appS_congruence : bop_congruence (list S) brel_list_S appS.
Proof. unfold bop_congruence. unfold brel_list_S, appS, app.
    intros s1 s2 t1 t2 H1 H2.
    assert (A := brel_list_to_prop s1 t1 H1).
    assert (B := brel_list_to_prop s2 t2 H2).
    rewrite A,B. apply brel_list_ref.
Qed.


Lemma bop_list_appS_associative : bop_associative (list S) brel_list_S appS.
Proof.  unfold bop_associative. intros s t u. unfold appS, app.
        assert (A := app_assoc s t u). rewrite A.      apply brel_list_ref. 
      Qed. 


Lemma beq_list_appT_congruence : 
   ∀ s1 s2 t1 t2 : T,
   brel_list_const s1 t1 = true
   → brel_list_const s2 t2 = true → brel_list_const (appT s1 s2) (appT t1 t2) = true.
Proof. intros s1 s2 t1 t2 H1 H2.
       unfold appT,bop_add_ann.
       destruct s1,t1. unfold brel_list_const, brel_add_constant. auto.
       destruct t2. auto. unfold brel_list_const,brel_add_constant in H1. discriminate.
       destruct s2. auto. unfold brel_list_const,brel_add_constant in H1. discriminate.
       destruct s2,t2. auto. unfold brel_list_const,brel_add_constant in H1. discriminate.
       unfold brel_list_const,brel_add_constant in H1. discriminate.
       unfold brel_list_const,brel_add_constant. 
       unfold brel_list_const,brel_add_constant in H1.
       unfold brel_list_const,brel_add_constant in H2.
       apply bop_list_appS_congruence;auto.
Qed.


Lemma bop_list_appT_congruence : bop_congruence T brel_list_const appT.
Proof. unfold bop_congruence.  unfold brel_list_const,brel_add_constant,appT,bop_add_ann.
    intros s1 s2 t1 t2 H1 H2.
    destruct s1,t1,s2,t2;auto.
    apply bop_list_appS_congruence; auto.
Qed.

Lemma bop_list_appT_associative : bop_associative T brel_list_const appT.
Proof.  unfold bop_congruence.  unfold brel_list_const,brel_add_constant,appT,bop_add_ann.
    intros x y z.
    destruct x, y, z; auto.
    apply bop_list_appS_associative.
Qed.

Lemma elem_app_true (a : S)(l1 l2 : list S): elem_in_list S eqS a l1 = true -> elem_in_list S eqS a (l1 ++ l2) = true.
Proof. intro H. induction l1.  unfold elem_in_list in H. discriminate.
       unfold elem_in_list in H. rewrite <- app_comm_cons.
       case_eq(eqS a a0); intro K. unfold elem_in_list. rewrite K; auto.
       rewrite K in H; simpl in H. fold elem_in_list in H.
       assert (A := IHl1 H).
       unfold elem_in_list.
       case(eqS a a0); simpl; auto.
Qed.

Lemma dup_first_elem (l1 l2: list S): dup_in_list S eqS l1= true -> dup_in_list S eqS (l1 ++ l2) = true.
Proof. intros H.
       induction l1. unfold dup_in_list in H. discriminate.
       rewrite <- app_comm_cons.
       unfold dup_in_list in H. 
       case_eq(elem_in_list S eqS a l1); intro K.
       unfold dup_in_list.
       assert (A := elem_app_true a l1 l2 K). rewrite A. auto. 
       rewrite K in H. simpl in H. fold dup_in_list in H.
       assert (A := IHl1 H).
       unfold dup_in_list.
       case(elem_in_list S eqS a (l1 ++ l2)); simpl; auto.
Qed.

Lemma dup_second_elem (l1 l2: list S): dup_in_list S eqS l2= true -> dup_in_list S eqS (l1 ++ l2) = true.
Proof. intro H.
    induction l1. rewrite app_nil_l. auto.
    rewrite <- app_comm_cons.
    unfold dup_in_list.
    case(elem_in_list S eqS a (l1 ++ l2)); simpl; auto.
Qed.


Lemma P_app_compose : pred_bop_compose T P appT.
Proof. intros n1 n2 H.
        unfold P,appT,bop_add_ann. 
        destruct n1. auto.
        destruct n2. auto.
        unfold P in H. unfold appS,app.
        destruct H.
        apply dup_first_elem; auto.
        apply dup_second_elem; auto.
Qed.
 
Lemma bop_is_ann_app_const : bop_is_ann T brel_list_const appT (inl c).
Proof. compute. intro s. split. auto.
       induction s; auto.
Qed.

Lemma bop_is_id_app_const : bop_is_id T brel_list_const appT (inr nil).
Proof. intro s. destruct s; unfold appT, appS,bop_add_ann,brel_list_const,brel_add_constant; auto.
       unfold app. rewrite app_nil_r. rewrite app_nil_l.
       rewrite (brel_list_ref l). auto.
Qed.

Lemma neq_list_cons (a : S): forall l : list S, brel_list_S (a :: l) l = false.
Proof. intros l. induction l. compute. auto.
       unfold brel_list_S,brel_list,basic.brel_list.
       case_eq (eqS a a0); intros K; simpl. fold (basic.brel_list eqS).
       admit. 
       auto.
Admitted.

Lemma neq_list_app (l : list S): forall a: S, forall l0 : list S, brel_list_S (a::l0 ++ l) l = false.
Proof. intros a l0. induction l0. rewrite app_nil_l. apply neq_list_cons.
       rewrite app_comm_cons.
Admitted.

Lemma uop_app_preserves_ann  :
 uop_preserves_ann T brel_list_const appT  uop_list.
Proof. unfold uop_preserves_ann. intros s H. unfold brel_list_const.
       unfold uop_list. unfold uop_predicate_reduce.
       assert (A := H s). destruct A as [Al Ar].
       destruct s. simpl. auto.
       simpl. simpl in Ar.
       induction l. simpl. apply brel_list_ref.
       simpl in Ar. unfold appS,app in Ar. 
       unfold brel_list_S,brel_list,basic.brel_list in Ar. rewrite refS in Ar. simpl in Ar.
       fold (basic.brel_list eqS) in Ar.
       assert (A := H (inr l)). destruct A as [_ A].
       unfold brel_list_const, appT,bop_add_ann,brel_add_constant in A.
   apply brel_list_sym in A.
   assert (B := brel_list_tran _ _ _ A Ar).
   assert (C := neq_list_cons a l).
   rewrite C in B. discriminate.
Qed.

Lemma uop_app_preserves_id  :
 uop_preserves_id T brel_list_const appT  uop_list.
Proof. unfold uop_preserves_id. intros s H. unfold brel_list_const.
    unfold uop_list. unfold uop_predicate_reduce.
    assert (A := H s). destruct A as [Al Ar].
    destruct s. simpl. auto.
    simpl. simpl in Ar.
    induction l. simpl. apply brel_list_ref.
    simpl in Ar. unfold appS,app in Ar. 
    unfold brel_list_S,brel_list,basic.brel_list in Ar. rewrite refS in Ar. simpl in Ar.
    fold (basic.brel_list eqS) in Ar.
    assert (A := H (inr l)). destruct A as [A _].
    unfold brel_list_const, appT,bop_add_ann,brel_add_constant in A.
assert (C := neq_list_app l a l). unfold appS, app in A.
rewrite app_comm_cons in C.
rewrite C in A. discriminate.
Qed.

Definition bop_list_app : binary_op T := bop_fpr (inl c) P appT.

Lemma bop_list_app_congruence : bop_congruence T (brel_reduce uop_list brel_list_const) bop_list_app.
Proof. apply bop_full_reduce_congruence; auto.
  apply uop_predicate_reduce_congruence; auto.
  apply brel_list_const_ref; auto.
  unfold pred_congruence. apply P_congruence. 
  apply bop_list_appT_congruence; auto. 
Qed.

Lemma bop_left_uop_invariant_app : bop_left_uop_invariant T brel_list_const
(bop_reduce
   (uop_predicate_reduce (inl c) P) appT)
(uop_predicate_reduce (inl c) P).
Proof. intros s1 s2.
    unfold bop_reduce,uop_predicate_reduce.
    destruct s1;simpl. auto.
    destruct s2;simpl.
    case_eq (dup_in_list S eqS l); intros K; simpl; auto. 
    case_eq(dup_in_list S eqS l); intro K; simpl.
    assert (A:= dup_first_elem l l0 K). unfold appS,app. rewrite A. auto.
    case_eq(dup_in_list S eqS (appS l l0)); intro L; simpl; auto.
    apply brel_list_ref.
Qed.

Lemma bop_right_uop_invariant_app : bop_right_uop_invariant T brel_list_const
(bop_reduce
   (uop_predicate_reduce (inl c) P) appT)
(uop_predicate_reduce (inl c) P).
Proof. intros s1 s2.
    unfold bop_reduce,uop_predicate_reduce.
    destruct s1;simpl. auto.
    destruct s2;simpl.
    case_eq (dup_in_list S eqS l); intros K; simpl; auto. 
    case_eq(dup_in_list S eqS l0); intro K; simpl.
    assert (A:= dup_second_elem l l0 K). unfold appS,app. rewrite A. auto.
    case_eq(dup_in_list S eqS (appS l l0)); intro L; simpl; auto.
    apply brel_list_ref.
Qed.


Open Scope nat.

Fixpoint dic_order (l1 l2 : list S) : bool :=
match l1,l2 with
| nil,nil => true
| nil,_ => true
| _,nil => false
| x::xl, y :: yl => if eqS x y then true else dic_order xl yl
end.

Lemma dic_order_eq (l1 l2: list S) : length l1 =? length l2 = true -> dic_order l1 l2 = true -> l1 = l2.
Proof. intros H1 H2. apply beq_nat_true in H1. unfold dic_order in H2.  unfold length in H1.
Admitted.

Lemma dic_order_refl (l: list S) :  dic_order l l = true.
Proof. induction l. auto. unfold dic_order. rewrite (refS a); auto.
Qed.

Lemma dic_order_cov (l1 l2 : list S) :  dic_order l1 l2 = false ->  dic_order l2 l1 = true.
Proof. intro H. induction l1,l2. auto.
   compute in H. discriminate. Admitted.


Definition minS : binary_op (list S) :=
λ l1 l2, if length l1 <? length l2 then l1
         else if length l1 =? length l2 then 
              if dic_order l1 l2 then l1 else l2
         else l2.
Definition minT := bop_add_id minS c.

Lemma beq_list_minS_congruence : 
   ∀ s1 s2 t1 t2 : list S,
   brel_list_S s1 t1 = true
   → brel_list_S s2 t2 = true → brel_list_S (minS s1 s2) (minS t1 t2) = true.
Proof. intros s1 s2 t1 t2 H1 H2.
       assert (A := brel_list_to_prop s1 t1 H1).
       assert (B := brel_list_to_prop s2 t2 H2).
       rewrite A,B. apply brel_list_ref.
Qed.

Lemma bop_list_minS_congruence : bop_congruence (list S) brel_list_S minS.
Proof. unfold bop_congruence. unfold brel_list_S, minS.
    intros s1 s2 t1 t2 H1 H2.
    assert (A := brel_list_to_prop s1 t1 H1).
    assert (B := brel_list_to_prop s2 t2 H2).
    rewrite A,B. apply brel_list_ref.
Qed.


Lemma bop_list_minS_associative : bop_associative (list S) brel_list_S minS.
Proof.  unfold bop_associative. intros s t u. unfold minS.
        case_eq(length s <? length t);intro K.
        case_eq(length t <? length u); intro L. rewrite K. 
        apply Nat.ltb_lt in K. apply Nat.ltb_lt in L.
        assert (A := lt_trans _ _ _ K L).
        apply Nat.ltb_lt in A. rewrite A. apply brel_list_ref.
        case_eq(length s <? length u);intro J.
        case_eq(length t =? length u); intro M. 
        apply beq_nat_true in M.
        case_eq (dic_order t u); intro N.
        rewrite M. rewrite J. apply brel_list_ref.
        rewrite J. apply brel_list_ref.
        rewrite J. apply brel_list_ref.
        case_eq (length s =? length u); intro M.
    assert (A : length t =? length u = false). 
    apply beq_nat_true in M.
    rewrite <- M.
    apply Nat.ltb_lt in K.
    admit.
        rewrite A. rewrite M; simpl. rewrite J. apply brel_list_ref.
        assert (A : length t =? length u = false).
        apply Nat.ltb_lt in K. 
        admit.
        rewrite A. rewrite J,M. apply brel_list_ref.
        case_eq(length s =? length t); intro J.
        case_eq(dic_order s t); intro M.
Admitted.


Lemma bop_list_minS_selective : bop_selective (list S) brel_list_S minS.
Proof.  unfold bop_selective. intros s t. unfold minS.
        case_eq(length s <? length t); intro K. rewrite brel_list_ref; auto.
        case_eq(length s =? length t); intro L.
        case_eq(dic_order s t); intro M; rewrite brel_list_ref; auto.
        rewrite brel_list_ref; auto.
Qed.

Lemma bop_list_minS_commutative : bop_commutative(list S) brel_list_S minS.
Proof.  unfold bop_commutative. intros s t. unfold minS.
    case_eq(length s <? length t); intro K. 
    assert (A : length t <? length s = false). admit.
    rewrite A.
    assert (B : length t =? length s = false). admit.
    rewrite B. rewrite brel_list_ref; auto.
        case_eq(length s =? length t); intro L. assert (L' := L).
        apply beq_nat_true in L. rewrite L. rewrite <- beq_nat_refl.
        rewrite <- L at 1. rewrite K. 
        case_eq (dic_order s t); intro M.
        assert (A := dic_order_eq s t L' M). rewrite A. auto. rewrite dic_order_refl. rewrite brel_list_ref; auto.
        assert (B := dic_order_cov s t M). rewrite B.  rewrite brel_list_ref; auto.
        assert (A:length t <? length s = true). admit.    
        rewrite A.
        rewrite brel_list_ref; auto.
Admitted.

Lemma bop_list_minT_congruence : bop_congruence T brel_list_const minT.
Proof. unfold bop_congruence.  unfold brel_list_const,brel_add_constant,minT, bop_add_id.
    intros s1 s2 t1 t2 H1 H2.
    destruct s1,t1,s2,t2;auto.
    discriminate.
    discriminate.
    discriminate.
    discriminate.
    discriminate.
    discriminate.
    apply bop_list_minS_congruence; auto.
Qed.

Lemma bop_list_minT_associative : bop_associative T brel_list_const minT.
Proof.  unfold bop_congruence.  unfold brel_list_const,brel_add_constant,minT,bop_add_id.
    intros x y z.
    destruct x, y, z; auto.
    rewrite brel_list_ref; auto.
    rewrite brel_list_ref; auto.
    rewrite brel_list_ref; auto.
    rewrite brel_list_ref; auto.
    rewrite brel_list_ref; auto.
    rewrite brel_list_ref; auto.
    apply bop_list_minS_associative.
Qed.

Lemma bop_list_minT_selective : bop_selective T brel_list_const minT.
Proof. unfold bop_selective.  unfold brel_list_const,brel_add_constant,minT, bop_add_id.
    intros s t.
    destruct s, t;auto.
    rewrite brel_list_ref; auto.
    rewrite brel_list_ref; auto.
    apply bop_list_minS_selective; auto.
Qed.

Lemma bop_list_minT_commutative : bop_commutative T brel_list_const minT.
Proof. unfold bop_commutative.  unfold brel_list_const,brel_add_constant,minT, bop_add_id.
    intros s t.
    destruct s, t;auto.
    rewrite brel_list_ref; auto.
    rewrite brel_list_ref; auto.
    apply bop_list_minS_commutative; auto.
Qed.

Lemma P_min_decompose : pred_bop_decompose T P minT.
Proof. intros n1 n2 H.
        unfold P,minT,bop_add_id. 
        destruct n1. auto.
        destruct n2. auto.
        unfold P in H.
        assert (A := bop_list_minT_selective (inr l) (inr l0)).
        destruct A. unfold minT,bop_add_id in H. apply brel_list_to_prop in e. rewrite e in H. left; auto.
        unfold minT,bop_add_id in H. apply brel_list_to_prop in e. rewrite e in H. right; auto.
Qed.


End ElementaryPath.
