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

Lemma brel_list_ref : brel_reflexive (list S) brel_list_S.
Proof. intro s. induction s.
       auto.  unfold brel_list_S, brel_list, basic.brel_list. rewrite (refS a);simpl. 
       fold (basic.brel_list eqS s). unfold brel_list_S, brel_list in IHs. exact IHs.
Qed.

Lemma brel_list_sym : brel_symmetric (list S) brel_list_S.
Proof. intros a b H.
Admitted. 

Lemma brel_list_tran : brel_transitive (list S) brel_list_S.
Admitted. 

Lemma brel_list_congruence : brel_congruence (list S) brel_list_S brel_list_S.
Admitted. 

Lemma brel_list_length_cong (l1 l2 : list S): brel_list_S l1 l2 = true -> length l1 = length l2.
Proof. intro H. unfold length.
Admitted.

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
Admitted. 

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

Lemma uop_list_congruence : uop_congruence (cas_constant + list S) brel_list_const uop_list.
Proof. intros x y H. unfold uop_list,uop_predicate_reduce.
       assert (A := P_congruence x y H).
   case_eq (P x); intro K; rewrite K in A; rewrite <- A.
   apply brel_list_const_ref.
   exact H.
Qed.

Lemma uop_list_idempotent : uop_idempotent (cas_constant + list S) brel_list_const uop_list.
Proof. intros a. unfold uop_list,uop_predicate_reduce.
       destruct a as [a | a].
       unfold P. apply brel_list_const_ref.
       unfold P.
       case_eq(dup_in_list S eqS a); intro K.
       unfold P. apply brel_list_const_ref.
       rewrite K.
       apply brel_list_const_ref.
Qed.


Lemma bop_list_appS_congruence : bop_congruence (list S) brel_list_S appS.
Proof. unfold bop_congruence. intros a b m n H1 H2.
       unfold appS,app.
Admitted.


Lemma bop_list_appS_associative : bop_associative (list S) brel_list_S appS.
Proof.  unfold bop_associative. intros s t u. unfold appS, app.
        assert (A := app_assoc s t u). rewrite A.      apply brel_list_ref. 
      Qed. 

Open Scope nat.

Lemma bop_list_appS_not_commutative : bop_not_commutative (list S) brel_list_S appS.
Proof. unfold bop_not_commutative. 
       exists (1::nil,2::nil).
       unfold appS, app. compute.
       auto.
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

Lemma bop_list_appT_not_commutative : bop_not_commutative T brel_list_const appT.
Proof. unfold bop_not_commutative.
    exists (inr(1::nil),inr(2::nil)).
    unfold appT,appS, app. compute.
    auto.
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
Proof. intros l. 
       case_eq(brel_list_S (a :: l) l); intro K. 
       assert (A :=     brel_list_length_cong _ _ K ).
       simpl in A.
       assert (B := n_Sn (length l)).
   elim B. rewrite A. auto.
       auto.
Qed.

Lemma neq_list_app (l : list S): forall a: S, forall l0 : list S, brel_list_S (a::l0 ++ l) l = false.
Proof. intros a l0. 
   case_eq(brel_list_S (a :: l0 ++ l) l); intro K. 
   assert (A :=     brel_list_length_cong _ _ K ).
   rewrite app_comm_cons in A.
   rewrite app_length in A.
   rewrite <- Nat.add_0_l in A.
rewrite plus_comm in A.
assert (length l + length (a :: l0) = length l + 0).
rewrite A. rewrite plus_comm. auto.
apply plus_reg_l in H.
compute in H.
symmetry in H.
apply O_S in H.
elim H.
 auto.
Qed.

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


Fixpoint dic_order (l1 l2 : list S) : bool :=
match l1,l2 with
| nil,_ => true
| _,nil => false    
| x::xl, y :: yl => if eqS x y
                    then dic_order xl yl
                    else x <? y 
end.


Lemma brel_dic_order_reflexive : brel_reflexive (list S) dic_order.
Proof. intro l. induction l. auto. unfold dic_order. rewrite (refS a); auto.
Qed.

Lemma brel_dic_order_transitive : brel_transitive (list S) dic_order.
Proof. intros x y z H1 H2.
       
Admitted.

Lemma brel_dic_order_total (l1 l2 : list S) :  (dic_order l1 l2 = true) +  (dic_order l2 l1 = true).
Proof. case_eq (dic_order l1 l2); intro K; auto.
       right.
       induction l1. compute in K. discriminate K.
       induction l2. compute. auto.
Admitted.

Definition brel_antisymmetric (S : Type) (r1 : brel S) (r2 : brel S) := 
    ∀ s t : S, (r2 s t = true) → (r2 t s = true) → (r1 s t = true). 

Lemma brel_dic_order_antisymmetric :  brel_antisymmetric (list S) brel_list_S dic_order.
Proof. intros x y H1 H2.
Admitted.

Lemma brel_dic_order_congruence : brel_congruence (list S) brel_list_S dic_order.
Proof. intros x y m n H1 H2. 
       Admitted.

Definition dic_minS : binary_op (list S) := λ l1 l2, if dic_order l1 l2 then l1 else l2.
Definition left_shortest : binary_op (list S) := λ l1 l2, if length l1 <=? length l2 then l1 else l2.


Lemma bop_dic_minS_selective : bop_selective (list S) brel_list_S dic_minS.
Proof.  unfold bop_selective. intros s t.
        unfold dic_minS.
        case_eq(dic_order s t); intro K.
        left. apply brel_list_ref.
        right. apply brel_list_ref.
Qed.

Lemma bop_dic_minS_commutative : bop_commutative (list S) brel_list_S dic_minS.
Proof.  intros s t.
        unfold dic_minS.
        case_eq(dic_order s t); intro J1; case_eq(dic_order t s); intro J2. 
        apply brel_dic_order_antisymmetric; auto.
        apply brel_list_ref.
        apply brel_list_ref.
        destruct (brel_dic_order_total s t) as [L | R].
        rewrite L in J1. discriminate J1.
        rewrite R in J2. discriminate J2.         
Qed. 

Lemma bop_left_shortest_selective : bop_selective (list S) brel_list_S left_shortest.
Proof.  unfold bop_selective. intros s t.
        unfold left_shortest.
        case_eq(length s <=? length t); intro K.
        left. apply brel_list_ref.
        right. apply brel_list_ref.
Qed.


Lemma bop_dic_minS_associative : bop_associative (list S) brel_list_S dic_minS.
Proof. intros x y z. unfold dic_minS.
       case_eq(dic_order x y); intro K1; case_eq(dic_order y z); intro K2; auto.
       rewrite K1. 
       case_eq(dic_order x z); intro K3. 
       apply brel_list_ref.
       apply brel_list_sym.
       assert (J := brel_dic_order_transitive _ _ _ K1 K2). rewrite K3 in J. discriminate J. 
       case_eq(dic_order x z); intro K3.
       apply brel_list_ref.
       apply brel_list_ref.
       rewrite K1.        apply brel_list_ref.
       case_eq(dic_order x z); intro K3.
       assert (K4 : dic_order y x = true). destruct (brel_dic_order_total x y) as [L | R]. rewrite L in K1. discriminate K1. exact R. 
       assert (K5 : dic_order z y = true). destruct (brel_dic_order_total y z) as [L | R]. rewrite L in K2. discriminate K2. exact R. 
       assert (J := brel_dic_order_transitive _ _ _ K5 K4). 
       assert (N := brel_dic_order_antisymmetric _ _ J K3). exact N. 
       apply brel_list_ref.
Qed. 

Lemma bop_left_shortest_associative : bop_associative (list S) brel_list_S left_shortest.
Proof. intros x y z. unfold left_shortest.
       case_eq(length x <=? length y); intro K1; case_eq(length y <=? length z); intro K2; auto.
       rewrite K1. 
       case_eq(length x <=? length z); intro K3. 
       apply brel_list_ref.
       apply leb_complete in K1.
       apply leb_complete in K2.
       assert (A := le_trans _ _ _ K1 K2).
       apply leb_correct in A. rewrite A in K3. discriminate.
       case_eq(length x <=? length z); intro K3.
       apply brel_list_ref.
       apply brel_list_ref.
       rewrite K1.        apply brel_list_ref.
       case_eq(length x <=? length z); intro K3.
       apply leb_complete_conv in K1.
       apply leb_complete_conv in K2.
       assert (A := lt_trans _ _ _ K2 K1).
       apply leb_correct_conv in A. rewrite A in K3. discriminate.
       apply brel_list_ref.
Qed.
       

Lemma bop_dic_minS_congruence : bop_congruence (list S) brel_list_S dic_minS.
Proof. intros x y m n H1 H2.
       unfold dic_minS.
       case_eq(dic_order x y); intro K.
       assert (A := brel_dic_order_congruence _ _ _ _ H1 H2).
       rewrite A in K. rewrite K. exact H1.
       assert (A := brel_dic_order_congruence _ _ _ _ H1 H2).
       rewrite A in K. rewrite K. exact H2.
Qed.

Lemma bop_left_shortest_congruence : bop_congruence (list S) brel_list_S left_shortest.
Proof. intros x y m n H1 H2.
       unfold left_shortest.
       assert (A := brel_list_length_cong _ _ H1).
       assert (B := brel_list_length_cong _ _ H2).
       case_eq(length x <=? length y); intro K; rewrite A in K; rewrite B in K; rewrite K.
       exact H1. exact H2.
Qed.

Definition minS : binary_op (list S) :=
  λ l1 l2, if length l1 =? length l2
           then dic_minS l1 l2 
           else left_shortest l1 l2.

Definition minT := bop_add_id minS c.
  
Lemma bop_list_minS_congruence : bop_congruence (list S) brel_list_S minS.
Proof. intros x y m n H1 H2. unfold minS.
    assert (A := brel_list_length_cong _ _ H1).
    assert (B := brel_list_length_cong _ _ H2).
    rewrite A. rewrite B.
    case_eq(length m =? length n ); intro K.
    apply bop_dic_minS_congruence; auto.
    apply bop_left_shortest_congruence; auto.
Qed.

Lemma H1 (t u : list S): length t ≠ length u -> length t = length (left_shortest t u) ->  brel_list_S (left_shortest t u) t = true.
Proof. intros H1 H2. unfold left_shortest. unfold left_shortest in H2.
       case_eq(length t <=? length u); intro K. apply brel_list_ref.
       rewrite K in H2. rewrite H2 in H1. assert (A := eq_refl (length u)). apply H1 in A. elim A.
Qed.

Lemma H2 (s t u : list S): length s = length t -> brel_list_S (left_shortest t u) t = true -> brel_list_S (left_shortest s u) s = true.
Proof. intros H1 H2. unfold left_shortest. unfold left_shortest in H2.  
       case_eq (length t <=? length u); intro K. rewrite <- H1 in K. rewrite K. apply brel_list_ref.
       rewrite K in H2.  rewrite leb_correct in K. discriminate.
       assert (A := brel_list_length_cong _ _ H2).
       rewrite A in K. 
       assert (B := le_refl (length t)). apply leb_correct in B. rewrite B in K. discriminate K.
Qed. 

Lemma brel_left_shortest_nleq (t u : list S): brel_list_S t u = false -> brel_list_S (left_shortest t u) u = true -> length t <=? length u = false.
Proof. intros H1 H2. unfold left_shortest in H2.
   case_eq (length t <=? length u); intro K. rewrite K in H2.
   rewrite H1 in H2. discriminate. 
   auto.
Qed.

Lemma brel_left_shortest_leq (t u : list S): brel_list_S (left_shortest t u) t = true -> length t <=? length u = true.
Proof. intro H. unfold left_shortest in H.
   case_eq (length t <=? length u); intro K. auto.
   rewrite K in H.
   apply leb_iff_conv in K.
   assert (A := brel_list_length_cong u t H).
   rewrite A in K.
   assert (B := lt_irrefl (length t)).
   apply B in K. elim K.
Qed.

Lemma H3 (s t u : list S): length s = length t -> brel_list_S t u = false -> brel_list_S (left_shortest t u) u = true -> brel_list_S (left_shortest s u) u = true.
Proof. intros H1 H2 H3. 
       assert (A := brel_left_shortest_nleq t u H2 H3).
       rewrite <- H1 in A.
    unfold left_shortest. rewrite A. unfold left_shortest in H2.  
    apply brel_list_ref.
Qed.

Lemma H4 (s t u : list S): length t = length u -> brel_list_S (left_shortest s t) s = true -> brel_list_S (left_shortest s u) s = true.
Proof. intros H1 H2. 
    unfold left_shortest. unfold left_shortest in H2.
    case_eq (length s <=? length t); intro K.
    rewrite H1 in K. rewrite K.     apply brel_list_ref.
    rewrite K in H2. rewrite H1 in K. rewrite K.
    rewrite <- H1 in K.
    assert (A := brel_list_length_cong t s H2).
    rewrite A in K.
    apply leb_iff_conv in K.
    assert (B := lt_irrefl (length s)).
    apply B in K. elim K.
Qed.

Lemma H5 (s t u : list S): length t = length u -> brel_list_S s t = false -> brel_list_S (left_shortest s t) t = true -> brel_list_S (left_shortest s u) u = true.
Proof. intros H1 H2 H3. 
    unfold left_shortest. unfold left_shortest in H3.
    case_eq (length s <=? length t); intro K.
rewrite H1 in K. rewrite K. rewrite <- H1 in K. rewrite K in H3.
rewrite H3 in H2. discriminate.
rewrite H1 in K. rewrite K. apply brel_list_ref.
Qed.

Lemma bop_list_minS_associative : bop_associative (list S) brel_list_S minS.
Proof.  unfold bop_associative. intros s t u. unfold minS.
        case_eq(length s =? length t); intro K1; 
        case_eq(length t =? length u); intro K2; auto.
        assert (J1 : length (dic_minS s t) =? length u = true).
        assert (A := bop_dic_minS_selective s t). destruct A as [A | A].
        assert (B := brel_list_length_cong (dic_minS s t) s A). rewrite B. 
        apply beq_nat_true in K1. rewrite <- K1 in K2. exact K2. 
        assert (B := brel_list_length_cong (dic_minS s t) t A). rewrite B. 
        exact K2. rewrite J1.
        assert (J2 : length s =? length (dic_minS t u) = true).
        assert (A := bop_dic_minS_selective t u). destruct A as [A | A].
        assert (B := brel_list_length_cong (dic_minS t u) t A). rewrite B.
        exact K1. 
        assert (B := brel_list_length_cong (dic_minS t u) u A). rewrite B.
        apply beq_nat_true in K1. rewrite <- K1 in K2. exact K2.  
        rewrite J2.
        apply bop_dic_minS_associative.
        assert (J1 : length (dic_minS s t) =? length u = false). 
        assert (A := bop_dic_minS_selective s t). destruct A as [A | A].
        assert (B := brel_list_length_cong (dic_minS s t) s A). rewrite B. 
        apply beq_nat_true in K1. rewrite <- K1 in K2. exact K2.
        assert (B := brel_list_length_cong (dic_minS s t) t A). rewrite B.
        exact K2. rewrite J1.
        destruct (bop_left_shortest_selective t u) as [L | R].
        assert (J2: length s =? length (left_shortest t u) = true).
        assert (B := brel_list_length_cong (left_shortest t u) t  L). rewrite B. exact K1. 
        rewrite J2. apply beq_nat_true in K1. apply beq_nat_true in J2. apply beq_nat_false in K2. apply beq_nat_false in J1.
        rewrite K1 in J2. 
        assert (A := bop_dic_minS_congruence s (left_shortest t u) s t (brel_list_ref s) L).
        assert (B := bop_dic_minS_selective s t). destruct B as [B | B].
        assert (C := bop_left_shortest_congruence (dic_minS s t) u s u B (brel_list_ref u)).
        assert (D := H1 t u K2 J2).
        assert (E := H2 s t u K1 D).
        assert (F := brel_list_tran _ _ _ A B).
        assert (G := brel_list_tran _ _ _ C E).
        apply brel_list_sym in F.
        exact (brel_list_tran _ _ _ G F).
        assert (C := bop_left_shortest_congruence (dic_minS s t) u t u B (brel_list_ref u)).
        assert (D := H1 t u K2 J2).
        assert (F := brel_list_tran _ _ _ A B).
        assert (G := brel_list_tran _ _ _ C D).
        apply brel_list_sym in F.
        exact (brel_list_tran _ _ _ G F).
        assert (J2 : length s =? length (left_shortest t u) = false).
        assert (A := brel_list_length_cong (left_shortest t u) u R).
        rewrite <- A in K2. apply beq_nat_true in K1.
        rewrite <- K1 in K2. exact K2. rewrite J2.
        assert (B := bop_dic_minS_selective s t). destruct B as [B | B].
        assert (C := bop_left_shortest_congruence s (left_shortest t u) s u  (brel_list_ref s) R).
        assert (D := bop_left_shortest_congruence (dic_minS s t) u s u  B (brel_list_ref u)).
        apply brel_list_sym in C.
        exact (brel_list_tran _ _ _ D C).
        assert (C := bop_left_shortest_congruence s (left_shortest t u) s u  (brel_list_ref s) R).
        assert (D := bop_left_shortest_congruence (dic_minS s t) u t u  B (brel_list_ref u)).
        apply brel_list_sym in C. apply beq_nat_true in K1.
        case_eq(brel_list_S t u); intro K. 
        assert (A := brel_list_length_cong _ _ K).
        rewrite A in K2. apply beq_nat_false in K2.
        elim K2. auto.
        assert (E := H3 s t u K1 K R). apply brel_list_sym in E.
        assert (F := brel_list_tran _ _ _ R E).
        assert (G := brel_list_tran _ _ _ D F).
        exact (brel_list_tran _ _ _ G C).
        assert (J1 : length s =? length (dic_minS t u) = false). 
        assert (A := bop_dic_minS_selective t u). destruct A as [A | A].
        assert (B := brel_list_length_cong _ _ A).
        rewrite B. exact K1.
        assert (B := brel_list_length_cong _ _ A).
        rewrite B. apply beq_nat_true in K2. rewrite K2 in K1. exact K1.
        rewrite J1.        
        destruct (bop_left_shortest_selective s t) as [L | R].
        assert (J2 : length (left_shortest s t) =? length u = false).
        assert (B := brel_list_length_cong _ _ L).
        rewrite B. apply beq_nat_true in K2. rewrite K2 in K1. exact K1.
        rewrite J2.
        assert (A := bop_left_shortest_congruence (left_shortest s t) u s u L (brel_list_ref u)).
        apply beq_nat_true in K2.
        assert (B := H4 s t u K2 L).
        assert (C := brel_list_tran _ _ _ A B).
        assert (D := bop_dic_minS_selective t u). destruct D as [D | D].
        assert (E := brel_left_shortest_leq s t L).
        assert (F : brel_list_S (left_shortest s t) s = true).
        unfold left_shortest. rewrite E. apply brel_list_ref.
        assert (G := bop_left_shortest_congruence s (dic_minS t u) s t (brel_list_ref s) D).
        assert (H := brel_list_tran _ _ _ G F). apply brel_list_sym in H.
        exact (brel_list_tran _ _ _ C H).
        assert (E := brel_left_shortest_leq s t L). rewrite K2 in E.
        assert (F : brel_list_S (left_shortest s u) s = true).
        unfold left_shortest. rewrite E. apply brel_list_ref.
        assert (G := bop_left_shortest_congruence s (dic_minS t u) s u (brel_list_ref s) D).
        assert (H := brel_list_tran _ _ _ G F). apply brel_list_sym in H.
        exact (brel_list_tran _ _ _ C H).
        assert (A := brel_list_length_cong (left_shortest s t) t R).
        apply beq_nat_true in K2. rewrite K2 in A. 
        assert (length (left_shortest s t) =? length u = true).
        rewrite A. rewrite <- (beq_nat_refl (length u)). auto.
        rewrite H. rewrite <- K2 in A. 
        assert (B := bop_dic_minS_congruence (left_shortest s t) u t u R (brel_list_ref u)).
        assert (D := bop_dic_minS_selective t u). destruct D as [D | D].
        assert (C := brel_list_tran _ _ _ B D).
        assert (E := bop_left_shortest_congruence s (dic_minS t u) s t (brel_list_ref s) D).
        assert (F := brel_list_tran _ _ _ E R). apply brel_list_sym in F.
        exact (brel_list_tran _ _ _ C F).
        assert (E := bop_left_shortest_congruence s (dic_minS t u) s u (brel_list_ref s) D).
        assert (C := brel_list_tran _ _ _ B D).
        case_eq(brel_list_S s t); intro K. 
        assert (X := brel_list_length_cong _ _ K).
        rewrite X in K1. apply beq_nat_false in K1.
        elim K1. auto.
        assert (F := H5 s t u K2 K R).
        assert (G := brel_list_tran _ _ _ E F). apply brel_list_sym in G.
        exact (brel_list_tran _ _ _ C G).
        destruct (bop_left_shortest_selective s t) as [J1 | J1];
        destruct (bop_left_shortest_selective t u) as [J2 | J2]; 
        case_eq(length s =? length u); intro J3. 
        assert (A := brel_left_shortest_leq _ _ J1).
        assert (B := brel_left_shortest_leq _ _ J2).
        apply beq_nat_true in J3. rewrite J3 in A.
        apply beq_nat_false in K2.
        apply leb_complete in A. apply leb_complete in B.
        assert (length t = length u).
        apply le_antisym; auto.
        apply K2 in H. elim H.
        assert (A := brel_list_length_cong _ _ J1).
        assert (B := brel_list_length_cong _ _ J2).
        rewrite <- A in J3. rewrite J3. rewrite <- B in K1. rewrite K1.
        apply bop_left_shortest_associative.    
        assert (A := brel_list_length_cong _ _ J1).   
        assert (B := brel_list_length_cong _ _ J2).
        apply beq_nat_true_iff in A. 
        apply beq_nat_true_iff in J3. rewrite J3 in A. rewrite A.
        apply beq_nat_true_iff in J3. rewrite <- B in J3. rewrite J3. 
        apply bop_dic_minS_congruence. exact J1.
        apply brel_list_sym in J2. exact J2.
        assert (A := brel_list_length_cong _ _ J1).
        assert (B := brel_list_length_cong _ _ J2).
        rewrite <- A in J3. rewrite J3. rewrite A in J3. rewrite <- B in J3. rewrite J3.
        apply bop_left_shortest_associative. 
        assert (A := brel_list_length_cong _ _ J1).
        assert (B := brel_list_length_cong _ _ J2).
        rewrite <- A in K2. rewrite K2. rewrite <- B in K1. rewrite K1.
        apply bop_left_shortest_associative.  
        assert (A := brel_list_length_cong _ _ J1).
        assert (B := brel_list_length_cong _ _ J2).
        rewrite <- A in K2. rewrite K2. rewrite <- B in K1. rewrite K1.
        apply bop_left_shortest_associative.  
        apply beq_nat_false in K1.
        apply beq_nat_false in K2.
        case_eq(brel_list_S s t); intro A.
        assert (B := brel_list_length_cong _ _ A).
        elim K1. exact B.  
        case_eq(brel_list_S t u); intro B.   
        assert (C := brel_list_length_cong _ _ B).
        elim K2. exact C.
        assert (C := brel_left_shortest_nleq _ _ A J1). 
        assert (D := brel_left_shortest_nleq _ _ B J2).
        apply leb_complete_conv in C.
        apply leb_complete_conv in D.
        assert (E := lt_trans _ _ _ D C).
        apply beq_nat_true in J3.
        rewrite J3 in E.
        assert (not (length u < length u)). apply lt_irrefl.
        elim H. exact E.             
        assert (A := brel_list_length_cong _ _ J1).
        assert (B := brel_list_length_cong _ _ J2).
        rewrite <- A in K2. rewrite K2. rewrite <- B in J3. rewrite J3.
        apply bop_left_shortest_associative.                
Qed.
        
Lemma bop_list_minS_selective : bop_selective (list S) brel_list_S minS.
Proof.  unfold bop_selective. intros s t. unfold minS.
        case_eq(length s =? length t); intro K. apply bop_dic_minS_selective.
        apply bop_left_shortest_selective. 
Qed.


Lemma bop_list_minS_commutative : bop_commutative(list S) brel_list_S minS.
Proof.  unfold bop_commutative. intros s t. unfold minS.
        case_eq(length s =? length t); intro K.
        assert (J : length t =? length s = true). rewrite Nat.eqb_eq in K. rewrite Nat.eqb_eq. rewrite K. auto. 
        rewrite J. apply bop_dic_minS_commutative. 
        assert (J : length t =? length s = false). rewrite Nat.eqb_neq in K. rewrite Nat.eqb_neq. intro. rewrite H in K. elim K. auto. 
        unfold left_shortest.
        case_eq(length s <=? length t); intro N.
        assert (M : length t <=? length s = false).
        apply leb_correct_conv. 
        apply leb_complete in N.
        apply le_lt_eq_dec in N. destruct N. exact l.
        apply beq_nat_false in K. elim K. exact e.
        rewrite M. rewrite J. apply brel_list_ref. 
        assert (M : length t <=? length s = true). 
        apply leb_correct.
        apply leb_complete_conv in N.
        apply le_lt_or_eq_iff. left. exact N.
        rewrite M. rewrite J.
        apply brel_list_ref.
Qed.

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
        destruct A. unfold minT,bop_add_id in H.
        simpl in e.
        assert (K := dup_list_cong _ _ e).  rewrite K in H. left. exact H.
        simpl in H.
        simpl in e.
        assert (K := dup_list_cong _ _ e).  rewrite K in H. right. exact H.
Qed.

Definition bop_list_app : binary_op T := bop_fpr (inl c) P appT.
Definition bop_list_min : binary_op T := bop_fpr (inl c) P minT.

Lemma bop_list_min_congruence : bop_congruence T (brel_reduce uop_list brel_list_const) bop_list_min.
Proof. apply bop_full_reduce_congruence; auto.
  apply uop_predicate_reduce_congruence; auto.
  apply brel_list_const_ref; auto.
  unfold pred_congruence. apply P_congruence. 
  apply bop_list_minT_congruence; auto. 
Qed.

Lemma bop_list_app_congruence : bop_congruence T (brel_reduce uop_list brel_list_const) bop_list_app.
Proof. apply bop_full_reduce_congruence; auto.
  apply uop_predicate_reduce_congruence; auto.
  apply brel_list_const_ref; auto.
  unfold pred_congruence. apply P_congruence. 
  apply bop_list_appT_congruence; auto. 
Qed.

Lemma bop_list_min_commutative : bop_commutative T (brel_reduce uop_list brel_list_const) bop_list_min.
Proof. apply bop_full_reduce_commutative; auto.
  apply uop_predicate_reduce_congruence; auto.
  apply brel_list_const_ref; auto.
  unfold pred_congruence. apply P_congruence. 
  apply bop_list_minT_commutative; auto. 
Qed.

Lemma bop_list_app_not_commutative : bop_not_commutative T (brel_reduce uop_list brel_list_const) bop_list_app.
Proof. unfold bop_not_commutative. 
    exists (inr(1::nil),inr(2::nil)). 
    compute. auto.
Qed.    

Lemma bop_list_app_commutative_decidable : bop_commutative_decidable T (brel_reduce uop_list brel_list_const) bop_list_app.
Proof. unfold bop_commutative_decidable. right.
       apply bop_list_app_not_commutative.
Qed. 

Lemma bop_is_id_min_const : bop_is_id T brel_list_const minT (inl c).
Proof. intro s. destruct s; unfold brel_list_const,brel_add_constant; auto.
    unfold minT,minS,bop_add_id.
    rewrite (brel_list_ref l). auto.
Qed.
    
Lemma bop_is_ann_min_const : bop_is_ann T brel_list_const minT (inr nil).
Proof. intros s. destruct s; simpl. rewrite (brel_list_ref nil). auto.
       destruct l; auto. 
Qed.

Lemma uop_min_preserves_ann  :
 uop_preserves_ann T brel_list_const minT  uop_list.
Proof. unfold uop_preserves_ann. intros s H.
       assert (A := bop_is_ann_min_const).
       assert (B := bop_is_ann_unique T brel_list_const 
        brel_list_const_sym brel_list_const_tran _ _ minT H A).
    destruct s; simpl. auto.
    destruct l; simpl. apply brel_list_ref.
    unfold brel_list_const,brel_add_constant,brel_list_S,brel_list,basic.brel_list in B.
    discriminate B.
Qed.

Lemma uop_min_preserves_id  :
 uop_preserves_id T brel_list_const minT  uop_list.
Proof. unfold uop_preserves_id. intros s H.
    assert (A := bop_is_id_min_const).
    assert (B := bop_is_id_unique T brel_list_const
    brel_list_const_sym brel_list_const_tran _ _ minT H A).
    destruct s; simpl. auto.
    destruct l; simpl. apply brel_list_ref.
    unfold brel_list_const,brel_add_constant,brel_list_S,brel_list,basic.brel_list in B.
    discriminate B.
Qed.

Lemma bop_list_min_associative : bop_associative T (brel_reduce uop_list brel_list_const) bop_list_min.
Proof. apply bop_associative_fpr_decompositional_id; auto.
    apply brel_list_const_ref; auto.
    apply brel_list_const_sym; auto.
    apply brel_list_const_tran; auto.
    apply P_true; auto.
    apply P_congruence; auto.
    apply bop_list_minT_congruence; auto.
    apply bop_list_minT_associative; auto.
    apply P_min_decompose.
    apply bop_is_id_min_const; auto.
Qed.


Lemma bop_list_app_associative : bop_associative T (brel_reduce uop_list brel_list_const) bop_list_app.
Proof. apply bop_associative_fpr_compositional.
    apply brel_list_const_ref; auto.
    apply brel_list_const_sym; auto.
    apply brel_list_const_tran; auto.
    apply P_true; auto.
    apply P_congruence; auto.
    apply P_app_compose; auto.
    apply bop_list_appT_congruence; auto.
    apply bop_list_appT_associative; auto.
  Qed.  

Lemma bop_list_min_selective : bop_selective T (brel_reduce uop_list brel_list_const) bop_list_min.
Proof. apply bop_full_reduce_selective; auto.
    apply brel_list_const_tran; auto.
    apply uop_list_congruence; auto.
    apply uop_list_idempotent; auto.
    apply bop_list_minT_selective; auto.
Qed.

Lemma bop_is_id_min : bop_is_id T (brel_reduce uop_list brel_list_const) bop_list_min (inl c).
Proof. apply bop_full_reduce_is_id.
    apply brel_list_const_ref; auto.
    apply brel_list_const_tran; auto.
    apply uop_list_congruence; auto.
    apply uop_list_idempotent; auto.
    apply bop_list_minT_congruence; auto.
    apply uop_min_preserves_id;auto.
    apply bop_is_id_min_const;auto.
Qed.
    
Lemma bop_is_ann_min : bop_is_ann T (brel_reduce uop_list brel_list_const) bop_list_min (inr nil).
Proof. apply bop_full_reduce_is_ann.
    apply brel_list_const_ref; auto.
    apply brel_list_const_tran; auto.
    apply uop_list_congruence; auto.
    apply bop_list_minT_congruence; auto.
    apply uop_min_preserves_ann;auto.
    apply bop_is_ann_min_const;auto.
Qed.

Lemma bop_is_id_app : bop_is_id T (brel_reduce uop_list brel_list_const) bop_list_app (inr nil).
Proof. apply bop_full_reduce_is_id.
    apply brel_list_const_ref; auto.
    apply brel_list_const_tran; auto.
    apply uop_list_congruence; auto.
    apply uop_list_idempotent; auto.
    apply bop_list_appT_congruence; auto.
    apply uop_app_preserves_id;auto.
    apply bop_is_id_app_const;auto.
Qed.
    
Lemma bop_is_ann_app : bop_is_ann T (brel_reduce uop_list brel_list_const) bop_list_app (inl c).
Proof. apply bop_full_reduce_is_ann.
    apply brel_list_const_ref; auto.
    apply brel_list_const_tran; auto.
    apply uop_list_congruence; auto.
    apply bop_list_appT_congruence; auto.
    apply uop_app_preserves_ann;auto.
    apply bop_is_ann_app_const;auto.
Qed.

Definition min_proofs  : 
commutative_selective_semigroup_proofs T (brel_reduce uop_list brel_list_const) bop_list_min
:= {|
  cssg_associative   := bop_list_min_associative
; cssg_congruence    := bop_list_min_congruence
; cssg_commutative   := bop_list_min_commutative
; cssg_selective     := bop_list_min_selective                                        
|}.

Definition app_proofs: 
semigroup_proofs T (brel_reduce uop_list brel_list_const) bop_list_app
:= {|
sg_associative   := bop_list_app_associative
  ; sg_congruence    := bop_list_app_congruence
; sg_commutative_d    := bop_list_app_commutative_decidable                                                
|}.


Definition eqv_proofs_eq_T : eqv_proofs T (brel_reduce uop_list brel_list_const)
:= {| 
     eqv_reflexive   := brel_reduce_list_const_reflexive
   ; eqv_transitive  := brel_reduce_list_const_transitive
   ; eqv_symmetric   := brel_reduce_list_const_symmetric
   ; eqv_congruence  := brel_reduce_list_const_congruence
   ; eqv_witness     := (inl c)
|}. 

Record non_distributive_dioid_proofs (S: Type) (eq : brel S) (add mul : binary_op S) (zero : S) (one : S) :=
{  
  dioid_zero_is_add_id     : bop_is_id S eq add zero
; dioid_one_is_mul_id      : bop_is_id S eq mul one                                                      
; dioid_zero_is_mul_ann    : bop_is_ann S eq mul zero
; dioid_one_is_add_ann     : bop_is_ann S eq add one
}.

Definition min_app_non_distributive_dioid_proofs : 
non_distributive_dioid_proofs T (brel_reduce uop_list brel_list_const) bop_list_min bop_list_app (inl c) (inr nil)
:= {|  
  dioid_zero_is_add_id     := bop_is_id_min
; dioid_one_is_mul_id      := bop_is_id_app
; dioid_one_is_add_ann     := bop_is_ann_min
; dioid_zero_is_mul_ann    := bop_is_ann_app
|}.

Record non_distributive_selective_dioid (S : Type) := {
    dioid_eq         : brel S  
  ; dioid_add        : binary_op S
  ; dioid_mul        : binary_op S                                   
  ; dioid_zero       : S
  ; dioid_one        : S
  ; diode_eqv        : eqv_proofs S dioid_eq
  ; diode_add_pfs    : commutative_selective_semigroup_proofs S dioid_eq dioid_add 
  ; diode_mul_pfs    : semigroup_proofs S dioid_eq dioid_mul 
  ; dioid_pfs        : non_distributive_dioid_proofs S dioid_eq dioid_add dioid_mul dioid_zero dioid_one
}.

Definition min_app_non_distributive_dioid : non_distributive_selective_dioid T
:= {|
    dioid_eq         := brel_reduce uop_list brel_list_const
  ; dioid_add        := bop_list_min
  ; dioid_mul        := bop_list_app                                 
  ; dioid_zero       := inl c
  ; dioid_one        := inr nil
  ; diode_eqv        := eqv_proofs_eq_T
  ; diode_add_pfs    := min_proofs
  ; diode_mul_pfs    := app_proofs
  ; dioid_pfs        := min_app_non_distributive_dioid_proofs
|}.

End ElementaryPath.
