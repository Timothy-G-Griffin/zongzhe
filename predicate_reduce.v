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



(* non-commutativity *)

(* First, show that witnesses (w1, w2) must have P(w1) = P(w2) = false *) 

Definition bop_not_commutative_witness(S : Type) (r : brel S) (b : binary_op S) (z : S * S)
  := match z with (s, t) => r (b s t) (b t s) = false end.

Lemma bop_fpr_not_commutative_and_id_implies_witnesses_P_false {S : Type} (s w1 w2 : S ) (P : S -> bool) (eq: brel S) (bS : binary_op S) :
  brel_reflexive S eq ->
  brel_symmetric S eq ->
  brel_transitive S eq -> 
  pred_true S P s -> pred_congruence S eq P -> bop_is_id S eq bS s -> 
  bop_not_commutative_witness S eq (bop_fpr s P bS) (w1, w2) -> 
  ((P w1 = false) * (P w2 = false)). 
Proof. intros refS symS tranS Ps Pc id W. compute in W. 
       case_eq(P w1); intro H1; case_eq(P w2); intro H2; rewrite H1, H2 in W.
       destruct (id s) as [L _]. apply Pc in L. rewrite Ps in L.  rewrite L in W. rewrite (refS s) in W. discriminate W.
       destruct (id w2) as [L R]. apply Pc in L. apply Pc in R. rewrite H2 in L, R.  rewrite L, R in W.
       destruct (id w2) as [L2 R2]. apply symS in R2.
       assert (H3 := tranS _ _ _ L2 R2). rewrite H3 in W. discriminate W.
       destruct (id w1) as [L R]. apply Pc in L. apply Pc in R. rewrite H1 in L, R.  rewrite L, R in W.
       destruct (id w1) as [L2 R2]. apply symS in L2.
       assert (H3 := tranS _ _ _ R2 L2). rewrite H3 in W. discriminate W.
       auto.
Qed.

Lemma bop_fpr_not_commutative_and_ann_implies_witnesses_P_false {S : Type} (s w1 w2 : S ) (P : S -> bool) (eq: brel S) (bS : binary_op S) :
  brel_reflexive S eq ->
  pred_true S P s -> pred_congruence S eq P -> bop_is_ann S eq bS s -> 
  bop_not_commutative_witness S eq (bop_fpr s P bS) (w1, w2) -> 
  ((P w1 = false) * (P w2 = false)). 
Proof. intros refS Ps Pc ann W. compute in W. 
       case_eq(P w1); intro H1; case_eq(P w2); intro H2; rewrite H1, H2 in W.
       destruct (ann s) as [L _]. apply Pc in L. rewrite Ps in L.  rewrite L in W. rewrite (refS s) in W. discriminate W.
       destruct (ann w2) as [L R]. apply Pc in L. apply Pc in R. rewrite Ps in L, R.  rewrite L, R in W.
       rewrite (refS s) in W. discriminate W.
       destruct (ann w1) as [L R]. apply Pc in L. apply Pc in R. rewrite Ps in L, R.  rewrite L, R in W.
       rewrite (refS s) in W. discriminate W.
       auto. 
Qed.

Lemma bop_fpr_not_commutative_implies_witnesses_P_false {S : Type} (s w1 w2 : S ) (P : S -> bool) (eq: brel S) (bS : binary_op S) :
  brel_reflexive S eq ->
  brel_symmetric S eq ->
  brel_transitive S eq -> 
  pred_true S P s -> pred_congruence S eq P -> ((bop_is_id S eq bS s) + (bop_is_ann S eq bS s)) -> 
  bop_not_commutative_witness S eq (bop_fpr s P bS) (w1, w2) -> 
  ((P w1 = false) * (P w2 = false)). 
Proof. intros refS symS tranS pS Pc [id | ann] W.
       apply (bop_fpr_not_commutative_and_id_implies_witnesses_P_false s w1 w2 P eq bS); auto.
       apply (bop_fpr_not_commutative_and_ann_implies_witnesses_P_false s w1 w2 P eq bS); auto.
Qed.        


(* Now, the othe direction ... *) 

Lemma bop_fpr_decompose_not_commutative {S : Type} (s w1 w2 : S ) (P : S -> bool) (eq: brel S) (bS : binary_op S) :
  pred_true S P s -> pred_congruence S eq P ->
  pred_bop_decompose S P bS ->
  bop_not_commutative_witness S eq (bop_fpr s P bS) (w1, w2) ->   
  ((P w1 = false) * (P w2 = false)) ->
  bop_not_commutative S eq (bop_fpr s P bS). 
Proof. intros Ps Pc D W [H1 H2]; exists (w1, w2); compute.
       rewrite H1, H2. 
       case_eq(P (bS w1 w2)); intro H3; case_eq(P (bS w2 w1)); intro H4; auto.
          destruct (D _ _ H3) as [F | F]. rewrite F in H1. discriminate H1. rewrite F in H2. discriminate H2. 
          destruct (D _ _ H3) as [F | F]. rewrite F in H1. discriminate H1. rewrite F in H2. discriminate H2.
          destruct (D _ _ H4) as [F | F]. rewrite F in H2. discriminate H2. rewrite F in H1. discriminate H1.
          compute in W. rewrite H1, H2 in W. rewrite H3, H4 in W. exact W. 
Qed. 

(* a bit more general *)

Definition pred_bop_weak_decompose (S : Type) (P : pred S) (bS : binary_op S) 
  := ∀ (a b : S), P (bS a b) = true -> P (bS b a) = true -> (P a = true) + (P b = true).

Lemma bop_fpr_not_commutative {S : Type} (s w1 w2 : S ) (P : S -> bool) (eq: brel S) (bS : binary_op S) :
  brel_symmetric S eq -> 
  pred_true S P s -> pred_congruence S eq P ->
  pred_bop_weak_decompose S P bS ->
  bop_self_divisor S eq bS s -> 
  bop_not_commutative_witness S eq (bop_fpr s P bS) (w1, w2) ->   
  ((P w1 = false) * (P w2 = false)) ->
  bop_not_commutative S eq (bop_fpr s P bS). 
Proof. intros symS Ps Pc wD sd W [H1 H2]; exists (w1, w2); compute.
       rewrite H1, H2. compute in Ps. 
       case_eq(P (bS w1 w2)); intro H3; case_eq(P (bS w2 w1)); intro H4; auto.
          destruct (wD _ _ H3 H4) as [F | F]. rewrite F in H1. discriminate H1. rewrite F in H2. discriminate H2.
          case_eq(eq s (bS w2 w1)); intro J.
             apply symS in J.
             destruct (sd _ _ J) as [F | F].
             apply Pc in F. rewrite H2 in F. rewrite Ps in F. discriminate F.
             apply Pc in F. rewrite H1 in F. rewrite Ps in F. discriminate F.              
             reflexivity. 
          compute in W. rewrite H1, H2 in W. rewrite H3, H4 in W. exact W.
          compute in W. rewrite H1, H2 in W. rewrite H3, H4 in W. exact W.              
Qed. 

(* End non-commutative *) 


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
       

Lemma pred_bop_preserve_order_congrapositive_v2 (bS : binary_op S) : 
bop_selective S eq bS ->
bop_commutative S eq bS ->
pred_preserve_order S P eq bS -> ∀ a b : S, P b = true → P a = false -> eq (bS a b) a = true.
Proof. intros sel com H a b M N.
     assert (J:= sel a b). destruct J. auto.
     assert (cab := com a b). apply symS in cab.
     assert (cba := tranS _ _ _ cab e).
     assert (A := H _ _ cba M). rewrite A in N. discriminate. 
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


Lemma bop_left_uop_invariant_predicate_reduce_v2 :
  ∀ (s : S) (bS : binary_op S),
    pred_true S P s ->
    pred_congruence S eq P -> 
    bop_selective S eq bS ->
    bop_is_id S eq bS s ->        
    pred_preserve_order S P eq bS ->
         bop_left_uop_invariant S eq (bop_reduce (uop_predicate_reduce s P) bS) (uop_predicate_reduce s P).
Proof. intros s bS P_true P_cong selS is_id pres s1 s2; compute; auto.
       destruct (is_id s1) as [J1 J2].
       destruct (is_id s2) as [M1 K2].              
       case_eq(P s1); intro H1; auto. compute in pres.
       assert(K1 := P_cong _ _ M1). rewrite K1. 
       case_eq(P s2); intro H2; auto.
       destruct (selS s1 s2) as [H3 | H3]; apply P_cong in H3.
       rewrite H3. rewrite H1. apply refS. 
       rewrite H3. rewrite H2. apply refS.
       destruct (selS s1 s2) as [H3 | H3].
       assert (K := pres s1 s2 H3 H1). rewrite K in H2. discriminate H2.
       assert (K3 := P_cong _ _ H3). rewrite K3. rewrite H2.
       apply symS in H3.
       assert (K4 := tranS _ _ _ M1 H3). 
       exact K4. 
Qed. 

Lemma bop_right_uop_invariant_predicate_reduce_v2 :
  ∀ (s : S) (bS : binary_op S),
    pred_true S P s ->
    pred_congruence S eq P -> 
    bop_selective S eq bS ->
    bop_commutative S eq bS ->
    bop_is_id S eq bS s ->        
    pred_preserve_order S P eq bS ->
    bop_right_uop_invariant S eq (bop_reduce (uop_predicate_reduce s P) bS) (uop_predicate_reduce s P).
Proof. intros s bS P_true P_cong selS comS is_id pres s1 s2; compute; auto.
       destruct (is_id s1) as [J1 J2].
       destruct (is_id s2) as [M1 K2].              
       case_eq(P s2); intro H1; auto. compute in pres.
       assert(K1 := P_cong _ _ J2). rewrite K1. 
       case_eq(P s1); intro H2; auto.
       destruct (selS s1 s2) as [H3 | H3]; apply P_cong in H3.
       rewrite H3. rewrite H2. apply refS. 
       rewrite H3. rewrite H1. apply refS.
       destruct (selS s1 s2) as [H3 | H3].
       assert (K3 := P_cong _ _ H3). rewrite K3. rewrite H2.
       apply symS in H3.
       assert (K4 := tranS _ _ _ J2 H3). 
       exact K4. 
       assert (A := comS s2 s1).
       assert (B := tranS _ _ _  A H3).
       assert (C := pres s2 s1 B H1). rewrite C in H2. discriminate H2. 
Qed. 



Lemma conj1 :
  ∀ (s : S) (bS : binary_op S),
    pred_true S P s -> 
    pred_congruence S eq P ->
    bop_is_id S eq bS s -> 
  bop_left_uop_invariant S eq (bop_reduce (uop_predicate_reduce s P) bS) (uop_predicate_reduce s P)
  ->     pred_preserve_order S P eq bS.
Proof. intros s bS P_true P_cong is_id H s1 s2 H1 H2.
       assert (K := H s1 s2). compute in K. rewrite H2 in K.
       apply P_cong in H1. rewrite H1 in K. rewrite H2 in K.
       destruct (is_id s2) as [L R].
       assert (J := P_cong _ _ L). rewrite J in K. 
       case_eq(P s2); intro H3; auto.
       rewrite H3 in K.
       apply symS in K.
       assert (H4 := tranS _ _ _ K L).
       apply P_cong in H4.  rewrite P_true in H4.
       rewrite H3 in H4.
       discriminate H4.
Qed.        

(* Lemma conj2 :
  ∀ (s : S) (bS : binary_op S),
    pred_true S P s ->
    pred_congruence S eq P -> 
    bop_selective S eq bS ->
    bop_is_id S eq bS s ->
    
    pred_preserve_order S P eq bS <-> 
    bop_left_uop_invariant S eq (bop_reduce (uop_predicate_reduce s P) bS) (uop_predicate_reduce s P).
Proof. intros s bs P_true P_cong selS idS.
       split; intros H s1 s2.
     compute. case_eq (P s1); intro K. compute in H. admit.
     case_eq (P (bs s1 s2)); intro J; apply refS.
     intros H1 H2. assert (A := H s1 s2). compute in A. rewrite H2 in A.

Admitted.

Lemma conj3 :
  ∀ (s : S) (bS : binary_op S),
    pred_true S P s ->
    pred_congruence S eq P -> 
    bop_selective S eq bS ->
    bop_commutative S eq bS ->    
    bop_is_id S eq bS s ->
    
    pred_preserve_order S P eq bS <-> 
    bop_right_uop_invariant S eq (bop_reduce (uop_predicate_reduce s P) bS) (uop_predicate_reduce s P).
Admitted. *)

(*p

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

Definition bop_preserve_pred (S : Type) (P : pred S) (bS : binary_op S)
  := ∀ (a b : S), P a = true -> P b = true -> P (bS a b) = true.

Lemma selective_implies_preserve_pred (bS : binary_op S) : 
bop_selective S eq bS ->
pred_congruence S eq P ->
bop_preserve_pred S P bS.
Proof. intros sel congP a b.
     assert(A := sel a b). destruct A; intros Pa Pb.
     assert(B := congP _ _ e). rewrite Pa in B. auto.
     assert(B := congP _ _ e). rewrite Pb in B. auto.
Qed.


(*
  delete decompose of mul
  add preserve_order properties of add
  add selectivity of add
  add commutativity of add
*)
Lemma bop_fpr_left_distributive_v2 :
  ∀ (s : S) (add mul : binary_op S),
     pred_true S P s -> 
     pred_congruence S eq P ->
     pred_bop_decompose S P add ->
     pred_preserve_order S P eq add ->
     bop_congruence S eq add ->     
     bop_congruence S eq mul -> 
     bop_selective S eq add ->
     bop_commutative S eq add ->
     bop_is_id S eq add s ->     
     bop_is_ann S eq mul s ->
     bop_left_distributive S eq add mul ->
       bop_left_distributive S (brel_reduce (uop_predicate_reduce s P) eq) (bop_fpr s P add) (bop_fpr s P mul).
Proof. intros s add mul P_true congP dadd padd cong_add cong_mul sel_add com_add s_id s_ann ldist a b c.
  assert (add_false : ∀ (a b : S), P a = false -> P b = false -> P (add a b) = false).
     apply pred_bop_decompose_contrapositive; auto.
     assert (app : bop_preserve_pred S P add).
     apply selective_implies_preserve_pred; auto. 
     assert (add_SelP : ∀ a b : S, P b = true → P a = false -> eq (add a b) a = true).
     apply pred_bop_preserve_order_congrapositive_v2;auto.
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
     rewrite P_true;
     apply symS in addSCL;
     assert (mulASC := cong_mul a c a (add s c) (refS a) addSCL);
     assert (PASC := congP (mul a c) (mul a (add s c)) mulASC); rewrite K in PASC; rewrite <- PASC.
     rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
     rewrite <- PASC. rewrite K.
     assert (addSAC := s_id (mul a c)). destruct addSAC as [addSACL addSACR].
     assert (PaddSAC := congP (add s (mul a c)) (mul a c) addSACL). rewrite K in PaddSAC. rewrite PaddSAC. rewrite PaddSAC.
     assert (J := tranS _ _ _ addSACL mulASC). apply symS in J. rewrite P_true. rewrite P_true. rewrite PaddSAC. exact J.
     assert (addBS := s_id b). destruct addBS as [addBSL addBSR].
     assert (PaddBS := congP (add b s) b addBSR). rewrite M in PaddBS. rewrite PaddBS. rewrite PaddBS.
     case_eq (P (mul a b)); intros K;
     apply symS in addBSR;
     assert (mulABS := cong_mul a b a (add b s) (refS a) addBSR);
     assert (PABS := congP (mul a b) (mul a (add b s)) mulABS); rewrite K in PABS; rewrite <- PABS;
     assert (mulAS := s_ann a); destruct mulAS as [mulASL mulASR];
     assert (PAS := congP (mul a s) s mulASR); rewrite P_true in PAS; rewrite PAS. 
     rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
     rewrite <- PABS. rewrite K. rewrite P_true.
     assert (addABS := s_id (mul a b)). destruct addABS as [addABSL addABSR].
     assert (PaddABS := congP (add (mul a b) s) (mul a b) addABSR). rewrite K in PaddABS. rewrite PaddABS. rewrite P_true. rewrite P_true. rewrite PaddABS.
     rewrite P_true.
     assert (J := tranS _ _ _ addABSR mulABS). apply symS in J. exact J.
     assert (addBC := add_false b c M N). rewrite addBC. rewrite addBC.
     assert (addABAC := ldist a b c).
     case_eq (P (mul a b)); intro J; case_eq (P (mul a c)); intro K.
     assert (PABAC := app _ _ J K).
     assert (PABC := congP _ _ addABAC). rewrite PABAC in PABC. rewrite PABC.
     rewrite P_true. rewrite P_true. rewrite P_true. rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
     rewrite P_true. rewrite P_true. rewrite K. rewrite P_true. rewrite P_true.
     assert (addACS := s_id (mul a c)). destruct addACS as [addACSL addACSR].
     assert (PSAC := congP _ _ addACSL). rewrite K in PSAC. rewrite PSAC. rewrite PSAC.
     assert (addACAB := add_SelP _ _ J K).
     assert (addPABAC := com_add (mul a b) (mul a c)).
     assert (mulABC := tranS _ _ _ addABAC addPABAC).
     assert (mulPABC := tranS _ _ _ mulABC addACAB).
     assert (PABC := congP _ _ mulPABC). rewrite K in PABC.
     rewrite PABC. rewrite PABC. apply symS in addACSL.
     exact (tranS _ _ _ mulPABC addACSL).
     rewrite J. rewrite P_true. rewrite P_true. rewrite P_true. rewrite P_true.
     assert (addABS := s_id (mul a b)). destruct addABS as [addABSL addABSR].
     assert (PSAB := congP _ _ addABSR). rewrite J in PSAB. rewrite PSAB. rewrite PSAB.
     assert (addPABAC := add_SelP _ _ K J).
     assert (mulABC := tranS _ _ _ addABAC addPABAC).
     assert (PABC := congP _ _ mulABC). rewrite J in PABC. rewrite PABC. rewrite PABC.
     apply symS in addABSR. exact (tranS _ _ _ mulABC addABSR).
     assert (PABAC := add_false _ _ J K).
     assert (PABC := congP _ _ addABAC). rewrite PABAC in PABC. rewrite PABC. rewrite PABC.
     rewrite J. rewrite K. rewrite PABAC. rewrite PABAC. exact addABAC.
Qed.

Lemma bop_fpr_right_distributive_v2 :
  ∀ (s : S) (add mul : binary_op S),
     pred_true S P s -> 
     pred_congruence S eq P ->
     pred_bop_decompose S P add ->
     pred_preserve_order S P eq add ->
     bop_congruence S eq add ->     
     bop_congruence S eq mul -> 
     bop_selective S eq add ->
     bop_commutative S eq add ->
     bop_is_id S eq add s ->     
     bop_is_ann S eq mul s ->
    bop_right_distributive S eq add mul ->
         bop_right_distributive S (brel_reduce (uop_predicate_reduce s P) eq) (bop_fpr s P add) (bop_fpr s P mul).
Proof. intros s add mul P_true congP dadd padd cong_add cong_mul sel_add com_add s_id s_ann rdist a b c.
  assert (add_false : ∀ (a b : S), P a = false -> P b = false -> P (add a b) = false).
     apply pred_bop_decompose_contrapositive; auto.
     assert (app : bop_preserve_pred S P add).
     apply selective_implies_preserve_pred; auto. 
     assert (add_SelP : ∀ a b : S, P b = true → P a = false -> eq (add a b) a = true).
     apply pred_bop_preserve_order_congrapositive_v2;auto.
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
     case_eq (P (mul c a)); intros K;
     rewrite P_true;
     apply symS in addSCL;
     assert (mulASC := cong_mul c a (add s c) a  addSCL (refS a));
     assert (PASC := congP (mul c a) (mul (add s c) a) mulASC); rewrite K in PASC; rewrite <- PASC.
     rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
     rewrite <- PASC. rewrite K.
     assert (addSAC := s_id (mul c a)). destruct addSAC as [addSACL addSACR].
     assert (PaddSAC := congP (add s (mul c a)) (mul c a) addSACL). rewrite K in PaddSAC. rewrite PaddSAC. rewrite PaddSAC.
     assert (J := tranS _ _ _ addSACL mulASC). apply symS in J. rewrite P_true. rewrite P_true. rewrite PaddSAC. exact J.
     assert (addBS := s_id b). destruct addBS as [addBSL addBSR].
     assert (PaddBS := congP (add b s) b addBSR). rewrite M in PaddBS. rewrite PaddBS. rewrite PaddBS.
     case_eq (P (mul b a)); intros K;
     apply symS in addBSR;
     assert (mulABS := cong_mul b a (add b s) a addBSR (refS a));
     assert (PABS := congP (mul b a) (mul (add b s) a) mulABS); rewrite K in PABS; rewrite <- PABS;
     assert (mulAS := s_ann a); destruct mulAS as [mulASL mulASR];
     assert (PAS := congP (mul s a) s mulASL); rewrite P_true in PAS; rewrite PAS. 
     rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
     rewrite <- PABS. rewrite K. rewrite P_true.
     assert (addABS := s_id (mul b a)). destruct addABS as [addABSL addABSR].
     assert (PaddABS := congP (add (mul b a) s) (mul b a) addABSR). rewrite K in PaddABS. rewrite PaddABS. rewrite P_true. rewrite P_true. rewrite PaddABS.
     rewrite P_true.
     assert (J := tranS _ _ _ addABSR mulABS). apply symS in J. exact J.
     assert (addBC := add_false b c M N). rewrite addBC. rewrite addBC.
     assert (addABAC := rdist a b c).
     case_eq (P (mul b a)); intro J; case_eq (P (mul c a)); intro K.
     assert (PABAC := app _ _ J  K).
     assert (PABC := congP _ _ addABAC). rewrite PABAC in PABC. rewrite PABC.
     rewrite P_true. rewrite P_true. rewrite P_true. rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
     rewrite P_true. rewrite P_true. rewrite K. rewrite P_true. rewrite P_true.
     assert (addACS := s_id (mul c a)). destruct addACS as [addACSL addACSR].
     assert (PSAC := congP _ _ addACSL). rewrite K in PSAC. rewrite PSAC. rewrite PSAC.
     assert (addACAB := add_SelP _ _ J K).
     assert (addPABAC := com_add (mul b a) (mul c a)).
     assert (mulABC := tranS _ _ _ addABAC addPABAC).
     assert (mulPABC := tranS _ _ _ mulABC addACAB).
     assert (PABC := congP _ _ mulPABC). rewrite K in PABC.
     rewrite PABC. rewrite PABC. apply symS in addACSL.
     exact (tranS _ _ _ mulPABC addACSL).
     rewrite J. rewrite P_true. rewrite P_true. rewrite P_true. rewrite P_true.
     assert (addABS := s_id (mul b a)). destruct addABS as [addABSL addABSR].
     assert (PSAB := congP _ _ addABSR). rewrite J in PSAB. rewrite PSAB. rewrite PSAB.
     assert (addPABAC := add_SelP _ _ K J).
     assert (mulABC := tranS _ _ _ addABAC addPABAC).
     assert (PABC := congP _ _ mulABC). rewrite J in PABC. rewrite PABC. rewrite PABC.
     apply symS in addABSR. exact (tranS _ _ _ mulABC addABSR).
     assert (PABAC := add_false _ _ J K).
     assert (PABC := congP _ _ addABAC). rewrite PABAC in PABC. rewrite PABC. rewrite PABC.
     rewrite J. rewrite K. rewrite PABAC. rewrite PABAC. exact addABAC.
Qed.

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



(* look at not left distributivity *)

Definition bop_not_left_distributive_witness (S : Type) (r : brel S) (add : binary_op S) (mul : binary_op S) (a : S * S * S)
  := match a with (s,t,u) => r (mul s (add t u)) (add (mul s t) (mul s u)) = false end.


Lemma bop_fpr_not_left_distributive_implies_witnesses_P_false :
  ∀ (s w1 w2 w3 : S) (add mul : binary_op S),
     pred_true S P s -> 
     pred_congruence S eq P ->
     bop_congruence S eq add ->     
     bop_congruence S eq mul -> 
     bop_is_id S eq add s ->     
     bop_is_ann S eq mul s ->
     bop_not_left_distributive_witness S (brel_reduce (uop_predicate_reduce s P) eq) (bop_fpr s P add) (bop_fpr s P mul) ((w1, w2), w3) ->
     (P w1 = false) * (P w2 = false) * (P w3 = false). 
Proof. intros s w1 w2 w3 add mul P_true congP cong_add cong_mul s_id s_ann nLD.
       compute in nLD. compute in P_true.
       assert (PLmul : ∀ (x : S),  P(mul s x) = true). intro x. destruct (s_ann x) as [L _]. apply congP in L. rewrite P_true in L. exact L.
       assert (PRmul : ∀ (x : S),  P(mul x s) = true). intro x. destruct (s_ann x) as [_ R]. apply congP in R. rewrite P_true in R. exact R.        
       assert (PLadd : ∀ (x : S),  P(add s x) = P x). intro x. destruct (s_id x) as [L _]. apply congP in L. exact L.
       assert (PRadd : ∀ (x : S),  P(add x s) = P x). intro x. destruct (s_id x) as [_ R]. apply congP in R. exact R.        
       case_eq(P w1); intro H1; case_eq(P w2); intro H2; case_eq(P w3); intro H3;
         repeat (
             try rewrite H1 in nLD;
             try rewrite H2 in nLD;
             try rewrite H3 in nLD;
             try rewrite P_true in nLD;
             try rewrite PLmul in nLD;
             try rewrite PRmul in nLD;             
             try rewrite PLadd in nLD;
             try rewrite PRadd in nLD; auto                                                  
           ).
       rewrite (refS s) in nLD.  discriminate nLD. 
       rewrite (refS s) in nLD.  discriminate nLD. 
       rewrite (refS s) in nLD.  discriminate nLD. 
       rewrite (refS s) in nLD.  discriminate nLD.
       rewrite (refS s) in nLD.  discriminate nLD.

       assert (K : P (mul w1 (add s w3)) = P (mul w1 w3)).
         destruct (s_id w3) as [L _]. assert (J := cong_mul _ _ _ _ (refS w1) L). apply congP in J. exact J. 
       case_eq(P (mul w1 w3)); intro H4;
         repeat (
             try rewrite H1 in nLD;
             try rewrite H2 in nLD;
             try rewrite H3 in nLD;
             try rewrite H4 in nLD;
             try rewrite K in nLD;                          
             try rewrite P_true in nLD;
             try rewrite PLmul in nLD;
             try rewrite PRmul in nLD;             
             try rewrite PLadd in nLD;
             try rewrite PRadd in nLD; auto                                                  
           ).
       rewrite (refS s) in nLD.  discriminate nLD.       
       destruct (s_id (mul w1 w3)) as [L1 _].
       destruct (s_id w3) as [L2 _].
       assert (J := cong_mul _ _ _ _ (refS w1) L2).
       apply symS in L1.
       assert (T := tranS _ _ _ J L1).
       rewrite T in nLD. discriminate nLD.

       assert (K : P (mul w1 (add w2 s)) = P (mul w1 w2)).
         destruct (s_id w2) as [_ R]. assert (J := cong_mul _ _ _ _ (refS w1) R). apply congP in J. exact J.        
       case_eq(P (mul w1 w2)); intro H4;
         repeat (
             try rewrite H1 in nLD;
             try rewrite H2 in nLD;
             try rewrite H3 in nLD;
             try rewrite H4 in nLD;
             try rewrite K in nLD;                          
             try rewrite P_true in nLD;
             try rewrite PLmul in nLD;
             try rewrite PRmul in nLD;             
             try rewrite PLadd in nLD;
             try rewrite PRadd in nLD; auto                                                  
           ).
       rewrite (refS s) in nLD.  discriminate nLD.
       destruct (s_id (mul w1 w2)) as [_ R1].
       destruct (s_id w2) as [_ R2].
       assert (J := cong_mul _ _ _ _ (refS w1) R2).
       apply symS in R1.
       assert (T := tranS _ _ _ J R1).
       rewrite T in nLD. discriminate nLD.
Qed.


Lemma bop_fpr_not_left_distributive :
  ∀ (s w1 w2 w3 : S) (add mul : binary_op S),
     pred_true S P s -> 
     pred_congruence S eq P ->
     bop_congruence S eq add ->     
     bop_congruence S eq mul -> 
     bop_is_id S eq add s ->     
     bop_is_ann S eq mul s ->
     pred_bop_decompose S P add ->
     pred_bop_decompose S P mul -> 
     (P w1 = false) * (P w2 = false) * (P w3 = false) ->      
     bop_not_left_distributive_witness S eq add mul ((w1, w2), w3) ->
       bop_not_left_distributive_witness S (brel_reduce (uop_predicate_reduce s P) eq) (bop_fpr s P add) (bop_fpr s P mul) ((w1, w2), w3).
Proof. intros s w1 w2 w3 add mul P_true congP cong_add cong_mul s_id s_ann addD mulD [[H1 H2] H3] nLD. 
       assert (PLmul : ∀ (x : S),  P(mul s x) = true). intro x. destruct (s_ann x) as [L _]. apply congP in L. rewrite P_true in L. exact L.
       assert (PRmul : ∀ (x : S),  P(mul x s) = true). intro x. destruct (s_ann x) as [_ R]. apply congP in R. rewrite P_true in R. exact R.        
       assert (PLadd : ∀ (x : S),  P(add s x) = P x). intro x. destruct (s_id x) as [L _]. apply congP in L. exact L.
       assert (PRadd : ∀ (x : S),  P(add x s) = P x). intro x. destruct (s_id x) as [_ R]. apply congP in R. exact R.        
       compute.       
       case_eq(P (add w2 w3)); intro H4; case_eq(P (mul w1 w2)); intro H5; case_eq(P (mul w1 w3)); intro H6;
         repeat
           ( try rewrite P_true; 
             try rewrite H1;
             try rewrite H2;
             try rewrite H3;
             try rewrite H4;
             try rewrite H5;
             try rewrite H6;             
             try rewrite PLmul;
             try rewrite PRmul;
             try rewrite PLadd;
             try rewrite PRadd;                           
             auto
           ).  
       destruct (addD _ _ H4) as [F | F]. rewrite F in H2. discriminate H2. rewrite F in H3. discriminate H3. 
       (* 2 *)
       case_eq(eq s (add s (mul w1 w3))); intro H7.
          apply congP in H7. rewrite P_true in H7.
          assert (H8 := PLadd (mul w1 w3)). rewrite H6 in H8. rewrite H8 in H7. discriminate H7. 
          reflexivity.
       (* 3 *)          
       case_eq(eq s (add (mul w1 w2) s)); intro H7.
          apply congP in H7. rewrite P_true in H7.
          assert (H8 := PRadd (mul w1 w2)). rewrite H5 in H8. rewrite H8 in H7. discriminate H7. 
          reflexivity.
       case_eq(P (add (mul w1 w2) (mul w1 w3))); intro H7.
          rewrite P_true.
          destruct (addD _ _ H4) as [F | F]. rewrite F in H2. discriminate H2. rewrite F in H3. discriminate H3.       
          rewrite H7.
          case_eq(eq s (add (mul w1 w2) (mul w1 w3))); intro H8.
             apply congP in H8. rewrite P_true in H8. rewrite H7 in H8. discriminate H8.
             reflexivity.
       (* 5 *)              
       case_eq(P (mul w1 (add w2 w3))); intro H7.
          rewrite P_true.
          destruct (mulD _ _ H5) as [F | F]. rewrite F in H1. discriminate H1. rewrite F in H2. discriminate H2. 
          rewrite H7.
           case_eq(eq (mul w1 (add w2 w3)) s); intro H8. 
              apply congP in H8. rewrite P_true in H8. rewrite H7 in H8. discriminate H8.
              reflexivity.               
       (* 6 *)
       case_eq(P (mul w1 (add w2 w3))); intro H7.
           rewrite P_true.  
           assert (K : P(add s (mul w1 w3)) = P(mul w1 w3)). destruct (s_id (mul w1 w3)) as [L _]. apply congP in L. exact L. 
           rewrite H6 in K.
           case_eq(eq s (add s (mul w1 w3))); intro H8.
              apply congP in H8. rewrite P_true in H8. rewrite K in H8. discriminate H8.
              reflexivity.
          rewrite H7.
          destruct (mulD _ _ H5) as [F | F]. rewrite F in H1. discriminate H1. rewrite F in H2. discriminate H2.               
      (* 7 *)
      case_eq(P (mul w1 (add w2 w3))); intro H7.
         rewrite P_true.
         case_eq (eq s (add (mul w1 w2) s) ); intro H8.
            apply congP in H8. rewrite P_true in H8.
            destruct (s_id (mul w1 w2)) as [_ R].
            apply congP in R. rewrite H5 in R. rewrite R in H8. discriminate H8.
            reflexivity. 
         rewrite H7. 
         destruct (mulD _ _ H6) as [F | F]. rewrite F in H1. discriminate H1. rewrite F in H3. discriminate H3.               
       (* 8 *)
       case_eq(P (add w2 w3)); intro H7; case_eq(P (add (mul w1 w2) (mul w1 w3))); intro H8; case_eq(P (mul w1 (add w2 w3))); intro H9; 
         repeat
           ( try rewrite P_true; 
             try rewrite H1;
             try rewrite H2;
             try rewrite H3;
             try rewrite H4;
             try rewrite H5;
             try rewrite H6;
             try rewrite H7;
             try rewrite H8;
             try rewrite H9;                                       
             try rewrite PLmul;
             try rewrite PRmul;
             try rewrite PLadd;
             try rewrite PRadd; auto
           ).
       rewrite H7 in H4.  discriminate H4. 
       case_eq(eq (mul w1 (add w2 w3)) s); intro H10.
          apply congP in H10. rewrite P_true in H10. rewrite H9 in H10. discriminate H10. 
          reflexivity. 
       case_eq(eq s (add (mul w1 w2) (mul w1 w3))); intro H10.
          apply congP in H10. rewrite P_true in H10. rewrite H8 in H10. discriminate H10. 
          reflexivity. 
       destruct (mulD _ _ H9) as [F | F]. rewrite F in H1. discriminate H1. rewrite F in H4. discriminate H4.                      
       case_eq(eq (mul w1 (add w2 w3)) s); intro H10.
          apply congP in H10. rewrite P_true in H10. rewrite H9 in H10. discriminate H10. 
          reflexivity.        
       case_eq(eq s (add (mul w1 w2) (mul w1 w3))); intro H10.
          apply congP in H10. rewrite P_true in H10. rewrite H8 in H10. discriminate H10. 
          reflexivity. 
Qed. 


End PredicateReduce.






                                                                                                                           