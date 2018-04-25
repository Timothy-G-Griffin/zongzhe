Require Export Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.   
Require Import CAS.basic. 
Require Import CAS.properties. 
Require Import CAS.structures.
Require Import CAS.product.
Require Import CAS.facts.
Require Import CAS.brel_reduce.
Require Import CAS.bop_full_reduce.

(* 

 *)


Definition uop_predicate_reduce : ∀ {S : Type}, S -> (S -> bool) -> unary_op S 
  := λ  {S} s1 P s2,  if P s2 then s1 else s2.

Definition bop_fpr {S : Type} (s : S ) (P : S -> bool) (bS : binary_op S) := 
  bop_full_reduce (uop_predicate_reduce s P) bS.


Section PredicateReduce. 

Variable S : Type.
Variable P : S -> bool.

Variable eq : brel S. 
Variable refS : brel_reflexive S eq.
Variable symS : brel_symmetric S eq.
Variable tranS : brel_transitive S eq.


Lemma uop_predicate_reduce_congruence (s : S) :
  pred_congruence S eq P -> uop_congruence S eq (uop_predicate_reduce s P). 
Proof. intros congP s1 s2; compute; intro H; compute; auto.
       case_eq(P s1); intro H1; case_eq(P s2); intro H2; auto.
       apply congP in H. rewrite H1 in H. rewrite H2 in H. discriminate H.
       apply congP in H. rewrite H1 in H. rewrite H2 in H. discriminate H.        
Qed.

Lemma uop_predicate_reduce_idempotent : ∀ (s : S), uop_idempotent S eq (uop_predicate_reduce s P). 
Proof. intros s x; compute; auto.
       case_eq(P x); intro H; auto.
       case_eq(P s); intro H1; auto.
       rewrite H. apply refS. 
Qed.


Lemma bop_fpr_congruence (s : S) (bS : binary_op S) :
  pred_congruence S eq P ->
  bop_congruence S eq bS ->  
        bop_congruence S (brel_reduce (uop_predicate_reduce s P) eq) (bop_fpr s P bS).       
Proof. intros congP congb.
       apply bop_full_reduce_congruence; auto.
       apply uop_predicate_reduce_congruence; auto.
Qed.


Lemma pred_bop_decompose_contrapositive (bS : binary_op S) : 
  pred_bop_decompose S P bS -> ∀ (a b : S), (P a = false) -> (P b = false) -> P (bS a b) = false.
Proof. intros D a b H1 H2.   
       case_eq(P (bS a b)); intro H3; auto. 
       destruct (D _ _ H3) as [H4 | H4].
       rewrite H4 in H1. discriminate.
       rewrite H4 in H2. discriminate.
Qed.

Lemma pred_bop_compose_contrapositive (bS : binary_op S) : 
  pred_bop_compose S P bS -> ∀ (a b : S), P (bS a b) = false -> (P a = false) /\ (P b = false).
Proof. intros D a b H. split.
       case_eq(P a); intro K.
       assert (A : (P a = true) + (P b = true)).
       left. auto.
       assert (B := D a b A). rewrite H in B. discriminate.
       auto.
       case_eq(P b); 
       intro K. 
       assert (A : (P a = true) + (P b = true)).
       right. auto.
       assert (B := D a b A). rewrite H in B. discriminate.
       auto.
Qed.

Lemma pred_bop_preserve_order_congrapositive (bS : binary_op S) : 
pred_preserve_order S P eq bS -> ∀ a b : S, eq (bS a b) a = true → P b = false → P a = false.
Proof. intros H a b M N.
     case_eq (P a); intro K.
     assert (A := H a b M K). rewrite N in A. discriminate. auto.
Qed.

(*

  Decompositional 

*) 

Lemma bop_pseudo_associative_fpr_decompositional_id :
  ∀ (c : S) (bS : binary_op S),
    pred_true S P c ->
    pred_congruence S eq P ->
    bop_congruence S eq bS ->     
    bop_associative S eq bS -> 
    pred_bop_decompose S P bS ->
    bop_is_id S eq bS c -> 
       bop_pseudo_associative S eq (uop_predicate_reduce c P) bS. 
Proof. intros c bS Pc P_cong b_cong assoc H isId l1 l2 l3; compute; auto.
       destruct (isId c) as [Jc _].
       destruct (isId l1) as [L1 R1].
       destruct (isId l2) as [L2 R2].
       destruct (isId l3) as [L3 R3].
       assert (Pcc := P_cong _ _ Jc). rewrite Pc in Pcc.
       assert (PL1 := P_cong _ _ L1).
       assert (PR1 := P_cong _ _ R1).
       assert (PL2 := P_cong _ _ L2).
       assert (PR2 := P_cong _ _ R2).
       assert (PL3 := P_cong _ _ L3).
       assert (PR3 := P_cong _ _ R3).
       case_eq(P l1); intro H1; case_eq(P l2); intro H2; case_eq(P l3); intro H3;
         repeat (try rewrite Pcc;
                 try rewrite Pc;
                 try rewrite H1;
                 try rewrite H2;
                 try rewrite H3;                  
                 try auto). 
       rewrite H3 in PL3. rewrite PL3. 
       destruct (isId (bS c l3)) as [L4 R4].
       assert (PL4 := P_cong _ _ L4). rewrite PL3 in PL4. rewrite PL4. apply symS. exact L4.
       rewrite H2 in PL2. rewrite PL2. 
       destruct (isId (bS c l2)) as [L4 R4].       
       assert (PR4 := P_cong _ _ R4). rewrite PL2 in PR4. rewrite PR4. 
       rewrite H2 in PR2.  rewrite PR2. 
       destruct (isId (bS l2 c)) as [L5 R5].
       assert (PL5 := P_cong _ _ L5). rewrite PR2 in PL5. rewrite PL5. 
       apply assoc.
       rewrite H2 in PL2. rewrite PL2. 
       assert (H4 : P (bS l2 l3) = false). apply pred_bop_decompose_contrapositive; auto. 
       rewrite H4.   
       assert (H5 : eq (bS (bS c l2) l3) (bS l2 l3) = true).
          destruct (isId l2) as [H6 _].
          assert (H7 := b_cong _ _ _ _ H6 (refS l3)).
          exact H7. 
       assert (H6 := P_cong _ _ H5).  rewrite H4 in H6. rewrite H6. 
       assert (H7 : eq (bS c (bS l2 l3)) (bS l2 l3) = true).
          destruct (isId (bS l2 l3)) as [H7 _].
          exact H7. 
       assert (H8 := P_cong _ _ H7).  rewrite H4 in H8. rewrite H8. 
       apply assoc.
       rewrite H1 in PR1. rewrite PR1. 
       assert (H5 : eq (bS (bS l1 c) c) l1 = true).
          destruct (isId l1) as [_ H4].
          destruct (isId (bS l1 c)) as [_ H5].
          assert (H6 := tranS _ _ _ H5 H4).
          exact H6.
       assert (H6 := P_cong _ _ H5). rewrite H1 in H6. rewrite H6. 
       apply isId.
       rewrite H1 in PR1. rewrite PR1. 
       rewrite H3 in PL3. rewrite PL3. 
       assert (H4 : P (bS l1 l3) = false). apply pred_bop_decompose_contrapositive; auto. 
       assert (H5 : eq (bS (bS l1 c) l3) (bS l1 l3) = true).
          destruct (isId l1) as [_ H5].
          assert (H6 := b_cong _ _ _ _ H5 (refS l3)).
          exact H6. 
      assert (H6 : eq (bS l1 (bS c l3)) (bS l1 l3) = true).
          destruct (isId l3) as [H6 _].
          assert (H7 := b_cong _ _ _ _ (refS l1) H6).
          exact H7. 
       assert (H7 := P_cong _ _ H5). rewrite H4 in H7. 
       assert (H8 := P_cong _ _ H6). rewrite H4 in H8.
       rewrite H7, H8. 
       apply assoc.
       assert (H4 : P (bS l1 l2) = false). apply pred_bop_decompose_contrapositive; auto. 
       rewrite H4. 
       assert (H5 : eq (bS (bS l1 l2) c) (bS l1 l2) = true).
          destruct (isId (bS l1 l2)) as [_ H5].
          exact H5. 
       assert (H6 := P_cong _ _ H5). rewrite H4 in H6.
       rewrite H6. 
       rewrite H2 in PR2. rewrite PR2. 
       assert (H7 : eq (bS l1 (bS l2 c)) (bS l1 l2) = true).
          destruct (isId l2) as [_ H7].
          assert (H8 := b_cong _ _ _ _ (refS l1) H7).
          exact H8. 
       assert (H8 := P_cong _ _ H7). rewrite H4 in H8.
       rewrite H8. 
       apply assoc.
       assert (H4 : P (bS l1 l2) = false). apply pred_bop_decompose_contrapositive; auto. 
       assert (H5 : P (bS l2 l3) = false). apply pred_bop_decompose_contrapositive; auto. 
       assert (H6 : P (bS (bS l1 l2) l3) = false). apply pred_bop_decompose_contrapositive; auto. 
       assert (H7 : P (bS l1 (bS l2 l3)) = false). apply pred_bop_decompose_contrapositive; auto. 
       repeat (
               try rewrite H4;
               try rewrite H5;
               try rewrite H6;
               try rewrite H7                             
             ). 
       apply assoc.        
Qed.


Lemma bop_associative_fpr_decompositional_id : 
  ∀ (c : S) (bS : binary_op S),
    pred_true S P c -> 
    pred_congruence S eq P -> 
    bop_congruence S eq bS ->     
    bop_associative S eq bS ->
    pred_bop_decompose S P bS ->
    bop_is_id S eq bS c -> 
        bop_associative S (brel_reduce (uop_predicate_reduce c P) eq) (bop_fpr c P bS). 
Proof. intros c bS Pc P_cong cong accos H isId. unfold bop_fpr. 
       apply bop_full_reduce_pseudo_associative_implies_associative; auto.
       apply uop_predicate_reduce_idempotent; auto.
       apply uop_predicate_reduce_congruence; auto.
       apply bop_pseudo_associative_fpr_decompositional_id; auto. 
Qed. 



Lemma bop_pseudo_associative_fpr_decompositional_ann :
  ∀ (s : S) (bS : binary_op S),
    pred_true S P s -> 
    pred_congruence S eq P ->
    bop_associative S eq bS ->    
    pred_bop_decompose S P bS ->
    bop_is_ann S eq bS s ->     
    bop_pseudo_associative S eq (uop_predicate_reduce s P) bS.
Proof. intros s bS P_true congP assoc D s_ann a b c.
       destruct (s_ann s) as [Lss Rss].
       destruct (s_ann a) as [Lsa Rsa].
       destruct (s_ann b) as [Lsb Rsb].
       destruct (s_ann c) as [Lsc Rsc].                     
       assert (Pss := congP _ _ Lss). rewrite P_true in Pss.
       assert (PLsa := congP _ _ Lsa). rewrite P_true in PLsa.
       assert (PLsb := congP _ _ Lsb). rewrite P_true in PLsb.
       assert (PLsc := congP _ _ Lsc). rewrite P_true in PLsc.
       assert (PRsa := congP _ _ Rsa). rewrite P_true in PRsa.
       assert (PRsb := congP _ _ Rsb). rewrite P_true in PRsb.
       assert (PRsc := congP _ _ Rsc). rewrite P_true in PRsc.       
       compute. 
       case_eq(P a); intro Pa; case_eq(P b); intro Pb; case_eq(P c); intro Pc;
         repeat (try rewrite Pss;
                 try rewrite PLsa;
                 try rewrite PLsb;
                 try rewrite PLsc;
                 try rewrite PRsa;
                 try rewrite PRsb;
                 try rewrite PRsc;                 
                 try rewrite P_true;
                 try rewrite Pa;
                 try rewrite Pb;
                 try rewrite Pc;                                                   
                 auto).
       assert (H1 : P (bS b c) = false). apply pred_bop_decompose_contrapositive; auto.
       rewrite H1.
       destruct (s_ann (bS b c)) as [H2 H3].
       assert (H4 := congP _ _ H2). rewrite P_true in H4. rewrite H4. apply refS.

       assert (H1 : P (bS a b) = false). apply pred_bop_decompose_contrapositive; auto.
       rewrite H1.
       destruct (s_ann (bS a b)) as [H2 H3].
       assert (H4 := congP _ _ H3). rewrite P_true in H4. rewrite H4. apply refS.

       assert (H1 : P (bS a b) = false). apply pred_bop_decompose_contrapositive; auto.
       assert (H2 : P (bS b c) = false). apply pred_bop_decompose_contrapositive; auto.
       rewrite H1. rewrite H2.
       assert (H3 : P (bS (bS a b) c) = false). apply pred_bop_decompose_contrapositive; auto.
       assert (H4 : P (bS a (bS b c)) = false). apply pred_bop_decompose_contrapositive; auto.              
       rewrite H3. rewrite H4.
       apply assoc. 
Qed. 


Lemma bop_associative_fpr_decompositional_ann : 
  ∀ (c : S) (bS : binary_op S),
    pred_true S P c -> 
    pred_congruence S eq P -> 
    bop_congruence S eq bS ->     
    bop_associative S eq bS ->
    pred_bop_decompose S P bS ->
    bop_is_ann S eq bS c -> 
        bop_associative S (brel_reduce (uop_predicate_reduce c P) eq) (bop_fpr c P bS). 
Proof. intros c bS Pc P_cong cong accos H isAnn. unfold bop_fpr. 
       apply bop_full_reduce_pseudo_associative_implies_associative; auto.
       apply uop_predicate_reduce_idempotent; auto.
       apply uop_predicate_reduce_congruence; auto.
       apply bop_pseudo_associative_fpr_decompositional_ann; auto. 
Qed. 


(*

  Compositional 

*) 

Lemma bop_left_uop_invariant_predicate_reduce :
  ∀ (s : S) (bS : binary_op S),
    pred_true S P s -> 
    pred_bop_compose S P bS ->
         bop_left_uop_invariant S eq (bop_reduce (uop_predicate_reduce s P) bS) (uop_predicate_reduce s P).
Proof. intros s bS B H s1 s2; compute; auto; case_eq(P s1); intro H1; auto. 
       assert (K := H s1 s2 (inl H1)). rewrite K; auto. 
       case_eq(P (bS s s2)); intro H2; auto.
       assert (J := H s s2 (inl B)). rewrite J in H2. discriminate H2. 
Qed. 

Lemma bop_right_uop_invariant_predicate_reduce :
  ∀ (s : S) (bS : binary_op S),
    pred_true S P s -> 
    pred_bop_compose S P bS ->    
       bop_right_uop_invariant S eq (bop_reduce (uop_predicate_reduce s P) bS) (uop_predicate_reduce s P).
Proof. intros s bS B H s1 s2; compute; auto; case_eq(P s2); intro H1; auto. 
       assert (K := H s1 s2 (inr H1)). rewrite K; auto. 
       case_eq(P (bS s1 s)); intro H2; auto.
       assert (J := H s1 s (inr B)). rewrite J in H2. discriminate H2.        
Qed.


Lemma bop_associative_fpr_compositional :
  ∀ (s : S) (bS : binary_op S),
    pred_true S P s    -> 
    pred_congruence S eq P ->     
    pred_bop_compose S P bS ->
    bop_congruence S eq bS ->         
    bop_associative S eq bS ->
        bop_associative S (brel_reduce (uop_predicate_reduce s P) eq) (bop_fpr s P bS).      
Proof. intros s bS Ps P_cong H cong assoc.
       apply bop_full_reduce_left_right_invariant_implies_associative; auto.
       apply uop_predicate_reduce_idempotent; auto.
       apply uop_predicate_reduce_congruence; auto.
       apply bop_left_uop_invariant_predicate_reduce; auto. 
       apply bop_right_uop_invariant_predicate_reduce; auto.
Qed.





(*  
    some sufficient conditions 
*) 


Lemma bop_fpr_selective (s : S) (bS : binary_op S) : 
(P s = true) ->
(∀ (a b : S), eq a b = true -> P a = P b) ->
(∀ (a b : S), P a = false -> P b = false -> P (bS a b) = false) -> 
bop_is_ann S eq bS s ->
bop_selective S eq bS ->  
bop_selective S (brel_reduce (uop_predicate_reduce s P) eq) (bop_fpr s P bS).
Proof. intros X Y B is_ann H. compute. intros a b. compute in H.
      case_eq(P a); intro K;case_eq(P b); intro L;
      assert (M := is_ann s); destruct M as [M _].
      assert (Z := Y (bS s s) s M). rewrite X in Z. rewrite Z. rewrite X. auto.
      assert (Z := is_ann b); destruct Z as [Z _].
      assert (A := Y (bS s b) s Z). rewrite X in A. rewrite A. rewrite X. auto.
      assert (Z := is_ann a); destruct Z as [_ Z].
      assert (A := Y (bS a s) s Z). rewrite X in A. rewrite A. rewrite X. auto.
      assert (Z := B a b K L). rewrite Z. rewrite Z. auto.
Qed.

Lemma bop_fpr_selective_v2 (s : S) (bS : binary_op S) : 
(P s = true) ->
(∀ (a b : S), eq a b = true -> P a = P b) ->
(∀ (a b : S), P a = false -> P b = false -> P (bS a b) = false) -> 
bop_is_id S eq bS s ->
bop_selective S eq bS ->  
bop_selective S (brel_reduce (uop_predicate_reduce s P) eq) (bop_fpr s P bS).
Proof. intros X Y B is_id H. compute. intros a b. compute in H.
      case_eq(P a); intro K;case_eq(P b); intro L;
      assert (M := is_id s); destruct M as [M _].
      assert (Z := Y (bS s s) s M). rewrite X in Z. rewrite Z. rewrite X. auto.
      assert (Z := is_id b); destruct Z as [Z _].
      assert (A := Y (bS s b) b Z). rewrite L in A. rewrite A,A. auto.
      assert (Z := is_id a); destruct Z as [_ Z].
      assert (A := Y (bS a s) a Z). rewrite K in A. rewrite A,A. auto.
      assert (Z := B a b K L). rewrite Z. rewrite Z. auto.
Qed.



 (* what about distributivity ? *) 

Lemma bop_fpr_id_true_true (s : S) (bS : binary_op S) :
  P(s) = true -> 
  (∀ (a b : S), eq a b = true -> P a = P b) ->
  bop_is_id S eq bS s ->       
  ∀ a b : S,  (P a = true) -> (P b = true) -> eq (bop_fpr s P bS a b) s = true.
Proof. intros P_true congP s_id a b Pa Pb. compute. rewrite Pa, Pb.
       destruct (s_id s) as [J _]. apply congP in J. rewrite P_true in J. rewrite J. 
       apply refS.
Qed.

Lemma bop_fpr_id_true_false (s : S) (bS : binary_op S) :
  (∀ (a b : S), eq a b = true -> P a = P b) ->
  bop_is_id S eq bS s ->       
  ∀ a b : S,  (P a = true) -> (P b = false) -> eq (bop_fpr s P bS a b) b = true.
Proof. intros congP s_id a b Pa Pb. compute. rewrite Pa, Pb.
       destruct (s_id b) as [J _]. apply congP in J. rewrite Pb in J. rewrite J. 
       apply s_id. 
Qed.

Lemma bop_fpr_id_false_true (s : S) (bS : binary_op S) :
  (∀ (a b : S), eq a b = true -> P a = P b) ->
  bop_is_id S eq bS s ->       
  ∀ a b : S,  (P a = false) -> (P b = true) -> eq (bop_fpr s P bS a b) a = true.
Proof. intros congP s_id a b Pa Pb. compute. rewrite Pa, Pb.
       destruct (s_id a) as [_ J]. apply congP in J. rewrite Pa in J. rewrite J. 
       apply s_id. 
Qed.

Lemma bop_fpr_false_false (s : S) (bS : binary_op S) :
  (∀ (a b : S), P a = false -> P b = false -> P (bS a b) = false) ->
       ∀ a b : S,  (P a = false) -> (P b = false) -> eq (bop_fpr s P bS a b) (bS a b) = true.
Proof. intros false_inv a b Pa Pb. compute. rewrite Pa, Pb.
       rewrite (false_inv a b Pa Pb). apply refS. 
Qed.

Lemma bop_fpr_ann_true (s : S) (bS : binary_op S) :
  P(s) = true -> 
  (∀ (a b : S), eq a b = true -> P a = P b) ->
  bop_is_ann S eq bS s ->       
  ∀ a b : S,  ((P a = true) + (P b = true)) -> eq (bop_fpr s P bS a b) s = true.
Proof. intros P_true congP s_ann a b [Pa | Pb]; compute.
       rewrite Pa.
       case_eq(P b); intro Pb. 
       destruct (s_ann s) as [J _]. apply congP in J. rewrite P_true in J. rewrite J. 
       apply refS.
       destruct (s_ann b) as [J _]. apply congP in J. rewrite P_true in J. rewrite J.
       apply refS.       
       rewrite Pb.
       case_eq(P a); intro Pa. 
       destruct (s_ann s) as [J _]. apply congP in J. rewrite P_true in J. rewrite J. 
       apply refS.
       destruct (s_ann a) as [_ J]. apply congP in J. rewrite P_true in J. rewrite J.
       apply refS.       
Qed.


Lemma bop_fpr_left_distributive :
  ∀ (s : S) (add mul : binary_op S),
     pred_true S P s -> 
     pred_congruence S eq P ->
     pred_bop_decompose S P add ->
     pred_bop_decompose S P mul ->          
     bop_congruence S eq add ->     
     bop_congruence S eq mul -> 
     bop_is_id S eq add s ->     
     bop_is_ann S eq mul s ->
     bop_left_distributive S eq add mul ->
       bop_left_distributive S (brel_reduce (uop_predicate_reduce s P) eq) (bop_fpr s P add) (bop_fpr s P mul).
Proof. intros s add mul P_true congP dadd dmul cong_add cong_mul s_id s_ann ldist a b c.
       assert (add_false : ∀ (a b : S), P a = false -> P b = false -> P (add a b) = false).
          apply pred_bop_decompose_contrapositive; auto. 
       assert (mul_false : ∀ (a b : S), P a = false -> P b = false -> P (mul a b) = false).
          apply pred_bop_decompose_contrapositive; auto.           
       compute.
       case_eq (P a); intro L; case_eq (P b); intro M; case_eq (P c); intro N;
       assert (addSS := s_id s); destruct addSS as [addSSL addSSR];
       assert (PaddSS := congP (add s s) s addSSL);rewrite P_true in PaddSS. rewrite PaddSS. rewrite P_true.
       assert (mulSS := s_ann s). destruct mulSS as [mulSSL mulSSR].
       assert (PmulSS := congP (mul s s) s mulSSL). rewrite P_true in PmulSS. rewrite PmulSS. rewrite P_true.
       rewrite PaddSS. rewrite P_true. auto.
       assert (addSC := s_id c). destruct addSC as [addSCL addSCR].
       assert (PaddSC := congP (add s c) c addSCL). rewrite N in PaddSC. rewrite PaddSC. rewrite PaddSC.
       assert (mulSS := s_ann s). destruct mulSS as [mulSSL mulSSR].
       assert (PmulSS := congP (mul s s) s mulSSL). rewrite P_true in PmulSS. rewrite PmulSS.
       assert (mulSC := s_ann c). destruct mulSC as [mulSCL mulSCR].
       assert (PmulSC := congP (mul s c) s mulSCL). rewrite P_true in PmulSC. rewrite PmulSC.
       assert (mulSASC := s_ann (add s c)). destruct mulSASC as [mulSASCL mulSASCR].
       assert (PmulSASC := congP (mul s (add s c)) s mulSASCL). rewrite P_true in PmulSASC. rewrite PmulSASC.
       rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
       assert (addBS := s_id b). destruct addBS as [addBSL addBSR].
       assert (PaddBS := congP (add b s) b addBSR). rewrite M in PaddBS. rewrite PaddBS. rewrite PaddBS.
       assert (mulSS := s_ann s). destruct mulSS as [mulSSL mulSSR].
       assert (PmulSS := congP (mul s s) s mulSSL). rewrite P_true in PmulSS. rewrite PmulSS. rewrite P_true.
       assert (mulSB := s_ann b). destruct mulSB as [mulSBL mulSBR].
       assert (PmulSB := congP (mul s b) s mulSBL). rewrite P_true in PmulSB. rewrite PmulSB.
       assert (mulSABS := s_ann (add b s)). destruct mulSABS as [mulSABSL mulSABSR].
       assert (PmulSABS := congP (mul s (add b s)) s mulSABSL). rewrite P_true in PmulSABS. rewrite PmulSABS.
       rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
       assert (PaddBC := add_false b c M N). rewrite PaddBC. rewrite PaddBC.
       assert (mulSABC := s_ann (add b c)). destruct mulSABC as [mulSABCL mulSABCR].
       assert (PmulSABC := congP (mul s (add b c)) s mulSABCL). rewrite P_true in PmulSABC. rewrite PmulSABC.
       assert (mulSB := s_ann b). destruct mulSB as [mulSBL mulSBR].
       assert (PmulSB := congP (mul s b) s mulSBL). rewrite P_true in PmulSB. rewrite PmulSB. rewrite P_true.
       assert (mulSC := s_ann c). destruct mulSC as [mulSCL mulSCR].
       assert (PmulSC := congP (mul s c) s mulSCL). rewrite P_true in PmulSC. rewrite PmulSC. rewrite P_true.
       rewrite PaddSS. rewrite P_true. auto.
       rewrite PaddSS. rewrite P_true.
       assert (mulAS := s_ann a). destruct mulAS as [mulASL mulASR].
       assert (PmulAS := congP (mul a s) s mulASR). rewrite P_true in PmulAS. rewrite PmulAS. rewrite P_true.
       rewrite PaddSS. rewrite P_true. auto.
       assert (addSC := s_id c). destruct addSC as [addSCL addSCR].
       assert (PaddSC := congP (add s c) c addSCL). rewrite N in PaddSC. rewrite PaddSC. rewrite PaddSC.
       assert (mulAS := s_ann a). destruct mulAS as [mulASL mulASR].
       assert (PmulAS := congP (mul a s) s mulASR). rewrite P_true in PmulAS. rewrite PmulAS. rewrite P_true.
       assert (mulAC := mul_false a c L N). rewrite mulAC. rewrite mulAC.
       assert (addSAC := s_id (mul a c)). destruct addSAC as [addSACL addSACR].
       assert (PaddSAC := congP (add s (mul a c)) (mul a c) addSACL). rewrite mulAC in PaddSAC. rewrite PaddSAC. (* rewrite PaddSAC *) 
       assert (PmulASC := mul_false a (add s c) L PaddSC). rewrite PmulASC. rewrite PmulASC.
       assert (mulASC := cong_mul a (add s c) a c (refS a) addSCL). rewrite P_true. rewrite PaddSAC. rewrite P_true. rewrite PaddSAC. rewrite P_true. 
       assert (K := tranS _ _ _ mulASC (symS _ _ addSACL)). exact K. 
       assert (addBS := s_id b). destruct addBS as [addBSL addBSR].
       assert (PaddBS := congP (add b s) b addBSR). rewrite M in PaddBS. rewrite PaddBS. rewrite PaddBS.
       assert (PmulAB := mul_false a b L M). rewrite PmulAB. rewrite PmulAB.
       assert (mulAS := s_ann a). destruct mulAS as [mulASL mulASR].
       assert (PmulAS := congP (mul a s) s mulASR). rewrite P_true in PmulAS. rewrite PmulAS. rewrite P_true.
       assert (addSAB := s_id (mul a b)). destruct addSAB as [addSABL addSABR].
       assert (PaddSAB := congP (add (mul a b) s) (mul a b) addSABR). rewrite PmulAB in PaddSAB. rewrite PaddSAB. 
       assert (PmulSABC := mul_false a (add b s) L PaddBS). rewrite PmulSABC. rewrite PmulSABC.
       assert (mulASB := cong_mul a (add b s) a b (refS a) addBSR). rewrite P_true. rewrite PaddSAB. rewrite P_true. rewrite PaddSAB. rewrite P_true. 
       assert (K := tranS _ _ _ mulASB (symS _ _ addSABR)). exact K.
       assert (addBC := add_false b c M N). rewrite addBC. rewrite addBC.
       assert (mulAB := mul_false a b L M). rewrite mulAB. rewrite mulAB.
       assert (mulAC := mul_false a c L N). rewrite mulAC. rewrite mulAC.
       assert (mulAABC := mul_false a (add b c) L addBC). rewrite mulAABC. rewrite mulAABC.
       assert (addMABMAC := add_false (mul a b) (mul a c) mulAB mulAC). rewrite addMABMAC. rewrite addMABMAC.
       assert (K := ldist a b c). exact K.
Qed.

Lemma bop_fpr_left_distributive_v2 :
  ∀ (s : S) (add mul : binary_op S),
     pred_true S P s -> 
     pred_congruence S eq P ->
     pred_bop_decompose S P add ->
     pred_preserve_order S P eq add ->
     pred_bop_compose S P mul ->        
     bop_congruence S eq add ->     
     bop_congruence S eq mul -> 
     bop_is_id S eq add s ->     
     bop_is_ann S eq mul s ->
     bop_left_distributive S eq add mul ->
       bop_left_distributive S (brel_reduce (uop_predicate_reduce s P) eq) (bop_fpr s P add) (bop_fpr s P mul).
Proof. intros s add mul P_true congP dadd padd cmul cong_add cong_mul s_id s_ann ldist a b c.
  assert (add_false : ∀ (a b : S), P a = false -> P b = false -> P (add a b) = false).
     apply pred_bop_decompose_contrapositive; auto.
     assert (add_preseve : ∀ a b : S, eq (add a b) a = true → P b = false → P a = false).
     apply pred_bop_preserve_order_congrapositive; auto.
     assert (mul_false : ∀ (a b : S), P (mul a b) = false -> (P a = false) /\ (P b = false)).
     apply pred_bop_compose_contrapositive; auto.
     compute.
     case_eq (P a); intro L; case_eq (P b); intro M; case_eq (P c); intro N;
     assert (addSS := s_id s); destruct addSS as [addSSL addSSR];
     assert (PaddSS := congP (add s s) s addSSL);rewrite P_true in PaddSS. rewrite PaddSS. rewrite P_true.
     assert (mulSS := s_ann s). destruct mulSS as [mulSSL mulSSR].
     assert (PmulSS := congP (mul s s) s mulSSL). rewrite P_true in PmulSS. rewrite PmulSS. rewrite P_true.
     rewrite PaddSS. rewrite P_true. auto.
     assert (addSC := s_id c). destruct addSC as [addSCL addSCR].
     assert (PaddSC := congP (add s c) c addSCL). rewrite N in PaddSC. rewrite PaddSC. rewrite PaddSC.
     assert (mulSS := s_ann s). destruct mulSS as [mulSSL mulSSR].
     assert (PmulSS := congP (mul s s) s mulSSL). rewrite P_true in PmulSS. rewrite PmulSS.
     assert (mulSC := s_ann c). destruct mulSC as [mulSCL mulSCR].
     assert (PmulSC := congP (mul s c) s mulSCL). rewrite P_true in PmulSC. rewrite PmulSC.
     assert (mulSASC := s_ann (add s c)). destruct mulSASC as [mulSASCL mulSASCR].
     assert (PmulSASC := congP (mul s (add s c)) s mulSASCL). rewrite P_true in PmulSASC. rewrite PmulSASC.
     rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
     assert (addBS := s_id b). destruct addBS as [addBSL addBSR].
     assert (PaddBS := congP (add b s) b addBSR). rewrite M in PaddBS. rewrite PaddBS. rewrite PaddBS.
     assert (mulSS := s_ann s). destruct mulSS as [mulSSL mulSSR].
     assert (PmulSS := congP (mul s s) s mulSSL). rewrite P_true in PmulSS. rewrite PmulSS. rewrite P_true.
     assert (mulSB := s_ann b). destruct mulSB as [mulSBL mulSBR].
     assert (PmulSB := congP (mul s b) s mulSBL). rewrite P_true in PmulSB. rewrite PmulSB.
     assert (mulSABS := s_ann (add b s)). destruct mulSABS as [mulSABSL mulSABSR].
     assert (PmulSABS := congP (mul s (add b s)) s mulSABSL). rewrite P_true in PmulSABS. rewrite PmulSABS.
     rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
     assert (PaddBC := add_false b c M N). rewrite PaddBC. rewrite PaddBC.
     assert (mulSABC := s_ann (add b c)). destruct mulSABC as [mulSABCL mulSABCR].
     assert (PmulSABC := congP (mul s (add b c)) s mulSABCL). rewrite P_true in PmulSABC. rewrite PmulSABC.
     assert (mulSB := s_ann b). destruct mulSB as [mulSBL mulSBR].
     assert (PmulSB := congP (mul s b) s mulSBL). rewrite P_true in PmulSB. rewrite PmulSB. rewrite P_true.
     assert (mulSC := s_ann c). destruct mulSC as [mulSCL mulSCR].
     assert (PmulSC := congP (mul s c) s mulSCL). rewrite P_true in PmulSC. rewrite PmulSC. rewrite P_true.
     rewrite PaddSS. rewrite P_true. auto.
     rewrite PaddSS. rewrite P_true.
     assert (mulAS := s_ann a). destruct mulAS as [mulASL mulASR].
     assert (PmulAS := congP (mul a s) s mulASR). rewrite P_true in PmulAS. rewrite PmulAS. rewrite P_true.
     rewrite PaddSS. rewrite P_true. auto.
     assert (addSC := s_id c). destruct addSC as [addSCL addSCR].
     assert (PaddSC := congP (add s c) c addSCL). rewrite N in PaddSC. rewrite PaddSC. rewrite PaddSC.
     assert (mulAS := s_ann a). destruct mulAS as [mulASL mulASR].
     assert (PmulAS := congP (mul a s) s mulASR). rewrite P_true in PmulAS. rewrite PmulAS. rewrite P_true.
     case_eq (P (mul a c)); intros K;
     assert (PA := congP (add s s) s addSSL); rewrite PaddSS in PA; rewrite <- PA;
     apply symS in addSCL;
     assert (mulASC := cong_mul a c a (add s c) (refS a) addSCL);
     assert (PASC := congP (mul a c) (mul a (add s c)) mulASC); rewrite K in PASC; rewrite <- PASC.
     rewrite <- PA. rewrite PaddSS. rewrite <- PA. auto.
     rewrite <- PASC. rewrite K.
     assert (addSAC := s_id (mul a c)). destruct addSAC as [addSACL addSACR].
     assert (PaddSAC := congP (add s (mul a c)) (mul a c) addSACL). rewrite K in PaddSAC. rewrite PaddSAC. rewrite PaddSAC.
     assert (J := tranS _ _ _ addSACL mulASC). apply symS in J. exact J.
     (* assert (mulAC := mul_false a c L N). rewrite mulAC. rewrite mulAC.
     assert (addSAC := s_id (mul a c)). destruct addSAC as [addSACL addSACR].
     assert (PaddSAC := congP (add s (mul a c)) (mul a c) addSACL). rewrite mulAC in PaddSAC. rewrite PaddSAC. (* rewrite PaddSAC *) 
     assert (PmulASC := mul_false a (add s c) L PaddSC). rewrite PmulASC. rewrite PmulASC.
     assert (mulASC := cong_mul a (add s c) a c (refS a) addSCL). rewrite P_true. rewrite PaddSAC. rewrite P_true. rewrite PaddSAC. rewrite P_true. 
     assert (K := tranS _ _ _ mulASC (symS _ _ addSACL)). exact K.  *)
     assert (addBS := s_id b). destruct addBS as [addBSL addBSR].
     assert (PaddBS := congP (add b s) b addBSR). rewrite M in PaddBS. rewrite PaddBS. rewrite PaddBS.
     case_eq (P (mul a b)); intros K.






     
     assert (PmulAB := mul_false a b L M). rewrite PmulAB. rewrite PmulAB.
     assert (mulAS := s_ann a). destruct mulAS as [mulASL mulASR].
     assert (PmulAS := congP (mul a s) s mulASR). rewrite P_true in PmulAS. rewrite PmulAS. rewrite P_true.
     assert (addSAB := s_id (mul a b)). destruct addSAB as [addSABL addSABR].
     assert (PaddSAB := congP (add (mul a b) s) (mul a b) addSABR). rewrite PmulAB in PaddSAB. rewrite PaddSAB. 
     assert (PmulSABC := mul_false a (add b s) L PaddBS). rewrite PmulSABC. rewrite PmulSABC.
     assert (mulASB := cong_mul a (add b s) a b (refS a) addBSR). rewrite P_true. rewrite PaddSAB. rewrite P_true. rewrite PaddSAB. rewrite P_true. 
     assert (K := tranS _ _ _ mulASB (symS _ _ addSABR)). exact K.
     assert (addBC := add_false b c M N). rewrite addBC. rewrite addBC.
     assert (mulAB := mul_false a b L M). rewrite mulAB. rewrite mulAB.
     assert (mulAC := mul_false a c L N). rewrite mulAC. rewrite mulAC.
     assert (mulAABC := mul_false a (add b c) L addBC). rewrite mulAABC. rewrite mulAABC.
     assert (addMABMAC := add_false (mul a b) (mul a c) mulAB mulAC). rewrite addMABMAC. rewrite addMABMAC.
     assert (K := ldist a b c). exact K.

Lemma bop_fpr_right_distributive :
  ∀ (s : S) (add mul : binary_op S),
     pred_true S P s -> 
     pred_congruence S eq P ->
     pred_bop_decompose S P add ->
     pred_bop_decompose S P mul ->          
    bop_congruence S eq add ->     
    bop_congruence S eq mul -> 
    bop_is_id S eq add s ->     
    bop_is_ann S eq mul s ->
    bop_right_distributive S eq add mul ->
         bop_right_distributive S (brel_reduce (uop_predicate_reduce s P) eq) (bop_fpr s P add) (bop_fpr s P mul).
Proof. intros s add mul P_true congP dadd dmul cong_add cong_mul s_id s_ann rdist a b c.
       assert (add_false : ∀ (a b : S), P a = false -> P b = false -> P (add a b) = false).
          apply pred_bop_decompose_contrapositive; auto. 
       assert (mul_false : ∀ (a b : S), P a = false -> P b = false -> P (mul a b) = false).
       apply pred_bop_decompose_contrapositive; auto.
       compute in P_true.
       compute;case_eq (P a); intro L; case_eq (P b); intro M; case_eq (P c); intro N;
       assert (addSS := s_id s); destruct addSS as [addSSL addSSR];
       assert (PaddSS := congP (add s s) s addSSL);rewrite P_true in PaddSS. rewrite PaddSS. rewrite P_true.
       assert (mulSS := s_ann s). destruct mulSS as [mulSSL mulSSR].
       assert (PmulSS := congP (mul s s) s mulSSL). rewrite P_true in PmulSS. rewrite PmulSS. rewrite P_true.
       rewrite PaddSS. rewrite P_true. auto.
       assert (addSC := s_id c). destruct addSC as [addSCL addSCR].
       assert (PaddSC := congP (add s c) c addSCL). rewrite N in PaddSC. rewrite PaddSC. rewrite PaddSC.
       assert (mulSS := s_ann s). destruct mulSS as [mulSSL mulSSR].
       assert (PmulSS := congP (mul s s) s mulSSL). rewrite P_true in PmulSS. rewrite PmulSS.
       assert (mulSC := s_ann c). destruct mulSC as [mulSCL mulSCR].
       assert (PmulSC := congP (mul c s) s mulSCR). rewrite P_true in PmulSC. rewrite PmulSC.
       assert (mulSASC := s_ann (add s c)). destruct mulSASC as [mulSASCL mulSASCR].
       assert (PmulSASC := congP (mul (add s c) s) s mulSASCR). rewrite P_true in PmulSASC. rewrite PmulSASC.
       rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
       assert (addBS := s_id b). destruct addBS as [addBSL addBSR].
       assert (PaddBS := congP (add b s) b addBSR). rewrite M in PaddBS. rewrite PaddBS. rewrite PaddBS.
       assert (mulSS := s_ann s). destruct mulSS as [mulSSL mulSSR].
       assert (PmulSS := congP (mul s s) s mulSSL). rewrite P_true in PmulSS. rewrite PmulSS. rewrite P_true.
       assert (mulSB := s_ann b). destruct mulSB as [mulSBL mulSBR].
       assert (PmulSB := congP (mul b s) s mulSBR). rewrite P_true in PmulSB. rewrite PmulSB.
       assert (mulSABS := s_ann (add b s)). destruct mulSABS as [mulSABSL mulSABSR].
       assert (PmulSABS := congP (mul (add b s) s) s mulSABSR). rewrite P_true in PmulSABS. rewrite PmulSABS.
       rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
       assert (PaddBC := add_false b c M N). rewrite PaddBC. rewrite PaddBC.
       assert (mulSABC := s_ann (add b c)). destruct mulSABC as [mulSABCL mulSABCR].
       assert (PmulSABC := congP (mul (add b c) s) s mulSABCR). rewrite P_true in PmulSABC. rewrite PmulSABC.
       assert (mulSB := s_ann b). destruct mulSB as [mulSBL mulSBR].
       assert (PmulSB := congP (mul b s) s mulSBR). rewrite P_true in PmulSB. rewrite PmulSB. rewrite P_true.
       assert (mulSC := s_ann c). destruct mulSC as [mulSCL mulSCR].
       assert (PmulSC := congP (mul c s) s mulSCR). rewrite P_true in PmulSC. rewrite PmulSC. rewrite P_true.
       rewrite PaddSS. rewrite P_true. auto.
       rewrite PaddSS. rewrite P_true.
       assert (mulAS := s_ann a). destruct mulAS as [mulASL mulASR].
       assert (PmulAS := congP (mul s a) s mulASL). rewrite P_true in PmulAS. rewrite PmulAS. rewrite P_true.
       rewrite PaddSS. rewrite P_true. auto.
       assert (addSC := s_id c). destruct addSC as [addSCL addSCR].
       assert (PaddSC := congP (add s c) c addSCL). rewrite N in PaddSC. rewrite PaddSC. rewrite PaddSC.
       assert (mulAS := s_ann a). destruct mulAS as [mulASL mulASR].
       assert (PmulAS := congP (mul s a) s mulASL). rewrite P_true in PmulAS. rewrite PmulAS. rewrite P_true.
       assert (mulAC := mul_false c a N L). rewrite mulAC. rewrite mulAC.
       assert (addSAC := s_id (mul c a)). destruct addSAC as [addSACL addSACR].
       assert (PaddSAC := congP (add s (mul c a)) (mul c a) addSACL). rewrite mulAC in PaddSAC. rewrite PaddSAC. rewrite PaddSAC.
       assert (PmulASC := mul_false (add s c) a PaddSC L ). rewrite PmulASC. rewrite PmulASC.
       assert (mulASC := cong_mul (add s c) a c a addSCL  (refS a)).
       assert (K := tranS _ _ _ mulASC (symS _ _ addSACL)). exact K.
       assert (addBS := s_id b). destruct addBS as [addBSL addBSR].
       assert (PaddBS := congP (add b s) b addBSR). rewrite M in PaddBS. rewrite PaddBS. rewrite PaddBS.
       assert (PmulAB := mul_false b a M L). rewrite PmulAB. rewrite PmulAB.
       assert (mulAS := s_ann a). destruct mulAS as [mulASL mulASR].
       assert (PmulAS := congP (mul s a) s mulASL). rewrite P_true in PmulAS. rewrite PmulAS. rewrite P_true.
       assert (addSAB := s_id (mul b a)). destruct addSAB as [addSABL addSABR].
       assert (PaddSAB := congP (add (mul b a) s) (mul b a) addSABR). rewrite PmulAB in PaddSAB. rewrite PaddSAB. rewrite PaddSAB.
       assert (PmulSABC := mul_false (add b s) a PaddBS L). rewrite PmulSABC. rewrite PmulSABC.
       assert (mulASB := cong_mul  (add b s) a b a addBSR  (refS a)).
       assert (K := tranS _ _ _ mulASB (symS _ _ addSABR)). exact K.
       assert (addBC := add_false b c M N). rewrite addBC. rewrite addBC.
       assert (mulAB := mul_false b a M L). rewrite mulAB. rewrite mulAB.
       assert (mulAC := mul_false c a N L). rewrite mulAC. rewrite mulAC.
       assert (mulAABC := mul_false (add b c) a addBC L). rewrite mulAABC. rewrite mulAABC.
       assert (addMABMAC := add_false (mul b a) (mul c a) mulAB mulAC). rewrite addMABMAC. rewrite addMABMAC.
       assert (K := rdist a b c). exact K.
Qed.

  
End PredicateReduce.






                                                                                                                           