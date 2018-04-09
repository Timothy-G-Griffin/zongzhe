Require Export Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.   
Require Import CAS.basic. 
Require Import CAS.properties. 
Require Import CAS.structures.
Require Import CAS.product.
Require Import CAS.facts.
Require Import CAS.brel_reduce.
Require Import CAS.bop_full_reduce.

(* I think with this we can define 
   our annihilator combinator. 

P(a, b) = (is_ann S bS a) or (is_ann T bT b) 

bop_product (a, b) (c, d) = (bS a c, bT b d) 

C1: P(a, b) => P(bop_product (a, b) (c, d))
C2: P(c, d) => P(bop_product (a, b) (c, d))

*) 

Section PredicateReduce. 

Definition uop_predicate_reduce : ∀ {S : Type}, S -> (S -> bool) -> unary_op S 
  := λ  {S} s1 P s2,  if P s2 then s1 else s2.

Definition bop_fpr {S : Type} (s : S ) (P : S -> bool) (bS : binary_op S) := 
  (bop_full_reduce (uop_predicate_reduce s P) bS).


Variable S : Type.
Variable P : S -> bool.

Variable eq : brel S. 
Variable refS : brel_reflexive S eq.
Variable symS : brel_symmetric S eq.
Variable tranS : brel_transitive S eq.

Lemma uop_predicate_reduce_idempoent : ∀ (s : S), uop_idempotent S eq (uop_predicate_reduce s P). 
Proof. intros s x; compute; auto.
       case_eq(P x); intro H; auto.
       case_eq(P s); intro H1; auto.
       rewrite H. apply refS. 
Qed.

(* WE NEVER USE THESE! 
(* TOO STRONG !!! *) 
Lemma bop_left_uop_invariant_predicate_reduce :
  ∀ (s : S) (bS : binary_op S), (P s = true) ->  (∀ (a b : S), P a = true -> P (bS a b) = true) ->  
         bop_left_uop_invariant S eq (bop_reduce (uop_predicate_reduce s P) bS) (uop_predicate_reduce s P).
Proof. intros s bS B H s1 s2; compute; auto; case_eq(P s1); intro H1; auto. 
       assert (K := H s1 s2 H1). rewrite K; auto. 
       case_eq(P (bS s s2)); intro H2; auto.
       assert (J := H s s2 B). rewrite J in H2. discriminate H2. 
Qed. 

(* TOO STRONG !!! *) 
Lemma bop_right_uop_invariant_predicate_reduce :
  ∀ (s : S) (bS : binary_op S),  (P s = true) ->  (∀ (a b : S), P b = true -> P (bS a b) = true) ->  
       bop_right_uop_invariant S eq (bop_reduce (uop_predicate_reduce s P) bS) (uop_predicate_reduce s P).
Proof. intros s bS B H s1 s2; compute; auto; case_eq(P s2); intro H1; auto. 
       assert (K := H s1 s2 H1). rewrite K; auto. 
       case_eq(P (bS s1 s)); intro H2; auto.
       assert (J := H s1 s B). rewrite J in H2. discriminate H2.        
Qed.
 *)


Lemma uop_predicate_reduce_congruence :
  ∀ (s : S), (∀ (a b : S), eq a b = true -> P a = P b) -> uop_congruence S eq (uop_predicate_reduce s P). 
Proof. intros s congP s1 s2; compute; intro H; compute; auto.
       case_eq(P s1); intro H1; case_eq(P s2); intro H2; auto.
       apply congP in H. rewrite H1 in H. rewrite H2 in H. discriminate H.
       apply congP in H. rewrite H1 in H. rewrite H2 in H. discriminate H.        
Qed.


Lemma bop_commutative_predicate_reduce :
  ∀ (s : S) (bS : binary_op S),  bop_commutative S eq bS ->    
       (∀ (a b : S), eq a b = true -> P a  = P b) ->  
       bop_commutative S eq (bop_reduce (uop_predicate_reduce s P) bS).
Proof. intros s bS commS H s1 s2; compute; auto.
       assert (K := commS s1 s2). 
       case_eq(P (bS s1 s2)); intro H1; case_eq(P (bS s2 s1)); intro H2; auto.
       apply H in K. rewrite H1 in K. rewrite H2 in K. discriminate K. 
       apply H in K. rewrite H1 in K. rewrite H2 in K. discriminate K.        
Qed.

Lemma bop_not_commutative_predicate_reduce :
  ∀ (s : S) (bS : binary_op S)
      (ncomm : bop_not_commutative S eq bS),
      (P(fst (projT1 ncomm)) = false) ->
      (P(snd (projT1 ncomm)) = false) ->  
      (∀ (a b : S), P a = false -> P b = false -> P (bS a b) = false) ->  
      bop_not_commutative S eq (bop_reduce (uop_predicate_reduce s P) bS).
Proof. intros s bS [[a b] Q] p1 p2 H; compute; auto. exists (a, b).
       simpl in p1. simpl in p2.
       assert (K1 := H _ _ p1 p2).
       assert (K2 := H _ _ p2 p1).
       rewrite K1. rewrite K2. 
       exact Q. 
Qed.

(*
Lemma bop_idempotent_predicate_reduce :
  ∀ (s : S)  (bS : binary_op S),
    bop_idempotent S eq bS ->    
       (∀ (a : S), P a = true -> eq s a = true) ->  
       bop_idempotent S eq (bop_reduce (uop_predicate_reduce s P) bS).
Proof. intros s bS idemS H s1. compute. 
       case_eq(P (bS s1 s1)); intro H1; auto.
          
Qed.
 *)

(* this should use a general lemma about bop_full_reduce! *) 
Lemma bop_fpr_congruence (s : S) (bS : binary_op S) :
  (∀ (a b : S), eq a b = true -> P a = P b) -> bop_congruence S eq bS ->  
        bop_congruence S eq (bop_fpr s P bS).       
Proof. intros congP congb a b c d H1 H2.
       assert (P1 := congP _ _ H1).
       assert (P2 := congP _ _ H2).
       assert (C3 := congb _ _ _ _ H1 H2).
       assert (P3 := congP _ _ C3).
       assert (C4 := congb _ _ _ _ (refS s) H2).
       assert (P4 := congP _ _ C4).
       assert (C5 := congb _ _ _ _ H1 (refS s)).
       assert (P5 := congP _ _ C5).       
       compute. 
       case_eq(P a); intro Pa; case_eq(P b); intro Pb; rewrite Pa in P1; rewrite Pb in P2; try rewrite <- P1; try rewrite <- P2.
          apply refS.
          rewrite P4. case_eq(P (bS s d)); intro J. apply refS. exact C4.
          rewrite P5. case_eq(P (bS c s)); intro J. apply refS. exact C5.
          rewrite P3. case_eq(P (bS c d)); intro J. apply refS. exact C3.                     
Qed.


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

(*
Lemma bop_associative_fpr_id :
  ∀ (s : S) (add : binary_op S),
     P(s) = true -> 
    (∀ (a b : S), eq a b = true -> P a = P b) ->
    (∀ (a b : S), P a = false -> P b = false -> P (add a b) = false) ->        
    bop_congruence S eq add ->     
    bop_is_id S eq add s ->     
    bop_associative S eq add ->
         bop_associative S eq (bop_fpr s P add).
Proof. intros s add P_true congP add_false cong_add s_id assoc a b c.
       destruct (s_id s) as [Lss Rss].
       destruct (s_id a) as [Lsa Rsa].
       destruct (s_id b) as [Lsb Rsb].
       destruct (s_id c) as [Lsc Rsc].                     
       assert (Pss := congP _ _ Lss). rewrite P_true in Pss.
       assert (PLsa := congP _ _ Lsa).
       assert (PLsb := congP _ _ Lsb).
       assert (PLsc := congP _ _ Lsc).
       assert (PRsa := congP _ _ Rsa).
       assert (PRsb := congP _ _ Rsb).
       assert (PRsc := congP _ _ Rsc).        
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
       assert (K1 : P (add s (add s c) ) = false).
          assert (E1 := cong_add _ _ _ _ (refS s) Lsc).
          assert (P1 := congP _ _ E1). rewrite PLsc in P1. rewrite Pc in P1. exact P1. 
       rewrite K1.
       apply cong_add. apply refS. apply symS. exact Lsc. 

       assert (K1 : P (add (add s b) s) = false).
          assert (E1 := cong_add _ _ _ _ Lsb (refS s)).
          assert (P1 := congP _ _ E1). rewrite PRsb in P1. rewrite Pb in P1. exact P1. 
       rewrite K1.
       assert (K3 : P (add s (add b s)) = false).
          assert (E1 := cong_add _ _ _ _ (refS s) Rsb ).
          assert (P1 := congP _ _ E1). rewrite PLsb in P1. rewrite Pb in P1. exact P1. 
       rewrite K3. 
       assert (K4 := assoc s b s). exact K4. 

       assert (J1 := add_false _ _ Pb Pc). rewrite J1. rewrite J1.        
       assert (K1 : P (add (add s b) c) = false).
          assert (E1 := cong_add _ _ _ _ Lsb (refS c)).
          assert (P1 := congP _ _ E1). rewrite J1 in P1. exact P1. 
       rewrite K1. 
       assert (K2 : P (add s (add b c)) = false).
          destruct (s_id (add b c)) as [E1 _]. 
          assert (P1 := congP _ _ E1). rewrite J1 in P1. exact P1. 
       rewrite K2.
       assert (K3 := assoc s b c). exact K3.        

       assert (K1 : P (add (add a s) s) = false).
          destruct (s_id (add a s)) as [_ E1]. 
          assert (P1 := congP _ _ E1). rewrite PRsa in P1. rewrite Pa in P1. exact P1. 
       rewrite K1.        
       destruct (s_id (add a s)) as [_ E2].        
       exact E2.
       
       assert (J1 := add_false _ _ Pa Pc). 
       assert (K1 : P (add (add a s) c) = false).
          assert (E1 := cong_add _ _ _ _ Rsa (refS c)).
          assert (P1 := congP _ _ E1). rewrite J1 in P1. exact P1. 
       rewrite K1.        
       assert (K2 : P (add a (add s c)) = false).
          assert (E1 := cong_add _ _ _ _ (refS a) Lsc). 
          assert (P1 := congP _ _ E1). rewrite J1 in P1. exact P1. 
       rewrite K2.
       assert (K3 := assoc a s c). exact K3.               

       assert (J1 := add_false _ _ Pa Pb).        
       assert (K1 : P (add a (add b s)) = false).
          assert (E1 := cong_add _ _ _ _ (refS a) Rsb). 
          assert (P1 := congP _ _ E1). rewrite J1 in P1. exact P1. 
       rewrite K1. rewrite J1. rewrite J1.                             
       assert (K2 : P (add (add a b) s) = false).
          destruct (s_id (add a b)) as [_ E1]. 
          assert (P1 := congP _ _ E1). rewrite J1 in P1. exact P1.        
       rewrite K2.        
       assert (K3 := assoc a b s). exact K3.                      


       assert (J1 := add_false _ _ Pa Pb). rewrite J1. rewrite J1. 
       assert (J2 := add_false _ _ Pb Pc). rewrite J2. rewrite J2. 
       assert (J3 := add_false _ _ J1 Pc). rewrite J3.
       assert (J4 := add_false _ _ Pa J2). rewrite J4.
       apply assoc. 
Qed. 

*) 

Lemma bop_associative_fpr_id_v2 :
  ∀ (s : S) (add : binary_op S),
     P(s) = true -> 
    (∀ (a b : S), eq a b = true -> P a = P b) ->
    (∀ (a b : S), P a = false -> P b = false -> P (add a b) = false) ->        
    bop_congruence S eq add ->     
    bop_is_id S eq add s ->     
    bop_associative S eq add ->
         bop_associative S (brel_reduce (uop_predicate_reduce s P) eq) (bop_fpr s P add).
Proof. intros s add P_true congP add_false cong_add s_id assoc a b c.
       destruct (s_id s) as [Lss Rss].
       destruct (s_id a) as [Lsa Rsa].
       destruct (s_id b) as [Lsb Rsb].
       destruct (s_id c) as [Lsc Rsc].                     
       assert (Pss := congP _ _ Lss). rewrite P_true in Pss.
       assert (PLsa := congP _ _ Lsa).
       assert (PLsb := congP _ _ Lsb).
       assert (PLsc := congP _ _ Lsc).
       assert (PRsa := congP _ _ Rsa).
       assert (PRsb := congP _ _ Rsb).
       assert (PRsc := congP _ _ Rsc).        
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
       assert (K1 : P (add s (add s c) ) = false).
          assert (E1 := cong_add _ _ _ _ (refS s) Lsc).
          assert (P1 := congP _ _ E1). rewrite PLsc in P1. rewrite Pc in P1. exact P1. 
       rewrite K1. rewrite K1. 
          apply cong_add. apply refS. apply symS. exact Lsc. 

       assert (K1 : P (add (add s b) s) = false).
          assert (E1 := cong_add _ _ _ _ Lsb (refS s)).
          assert (P1 := congP _ _ E1). rewrite PRsb in P1. rewrite Pb in P1. exact P1. 
       rewrite K1.
       assert (K3 : P (add s (add b s)) = false).
          assert (E1 := cong_add _ _ _ _ (refS s) Rsb ).
          assert (P1 := congP _ _ E1). rewrite PLsb in P1. rewrite Pb in P1. exact P1. 
       rewrite K3. 
       assert (K4 := assoc s b s). rewrite K1. rewrite K3. exact K4. 

       assert (J1 := add_false _ _ Pb Pc). rewrite J1. rewrite J1.        
       assert (K1 : P (add (add s b) c) = false).
          assert (E1 := cong_add _ _ _ _ Lsb (refS c)).
          assert (P1 := congP _ _ E1). rewrite J1 in P1. exact P1. 
       rewrite K1. 
       assert (K2 : P (add s (add b c)) = false).
          destruct (s_id (add b c)) as [E1 _]. 
          assert (P1 := congP _ _ E1). rewrite J1 in P1. exact P1. 
       rewrite K2.
       assert (K3 := assoc s b c). rewrite K1. rewrite K2. exact K3.        

       assert (K1 : P (add (add a s) s) = false).
          destruct (s_id (add a s)) as [_ E1]. 
          assert (P1 := congP _ _ E1). rewrite PRsa in P1. rewrite Pa in P1. exact P1. 
       rewrite K1.        
       destruct (s_id (add a s)) as [_ E2].        
       rewrite K1. exact E2.
       
       assert (J1 := add_false _ _ Pa Pc). 
       assert (K1 : P (add (add a s) c) = false).
          assert (E1 := cong_add _ _ _ _ Rsa (refS c)).
          assert (P1 := congP _ _ E1). rewrite J1 in P1. exact P1. 
       rewrite K1.        
       assert (K2 : P (add a (add s c)) = false).
          assert (E1 := cong_add _ _ _ _ (refS a) Lsc). 
          assert (P1 := congP _ _ E1). rewrite J1 in P1. exact P1. 
       rewrite K2.
       assert (K3 := assoc a s c). rewrite K1. rewrite K2. exact K3.               

       assert (J1 := add_false _ _ Pa Pb).        
       assert (K1 : P (add a (add b s)) = false).
          assert (E1 := cong_add _ _ _ _ (refS a) Rsb). 
          assert (P1 := congP _ _ E1). rewrite J1 in P1. exact P1. 
       rewrite K1. rewrite J1. rewrite J1.                             
       assert (K2 : P (add (add a b) s) = false).
          destruct (s_id (add a b)) as [_ E1]. 
          assert (P1 := congP _ _ E1). rewrite J1 in P1. exact P1.        
       rewrite K2.        
       assert (K3 := assoc a b s). rewrite K2. rewrite K1. exact K3.                      


       assert (J1 := add_false _ _ Pa Pb). rewrite J1. rewrite J1. 
       assert (J2 := add_false _ _ Pb Pc). rewrite J2. rewrite J2. 
       assert (J3 := add_false _ _ J1 Pc). rewrite J3.
       assert (J4 := add_false _ _ Pa J2). rewrite J4.
       rewrite J3. rewrite J4. 
       apply assoc. 
Qed. 


(*
Lemma bop_associative_fpr_ann :
  ∀ (s : S) (mul : binary_op S),
     P(s) = true -> 
    (∀ (a b : S), eq a b = true -> P a = P b) ->
    (∀ (a b : S), P a = false -> P b = false -> P (mul a b) = false) ->        
    bop_congruence S eq mul ->     
    bop_is_ann S eq mul s ->     
    bop_associative S eq mul ->
         bop_associative S eq (bop_fpr s P mul).
Proof. intros s mul P_true congP mul_false cong_mul s_ann assoc a b c.
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

       assert (J1 := mul_false _ _ Pb Pc). rewrite J1. rewrite J1.        
       assert (K1 : P (mul s (mul b c)) = true).
          destruct (s_ann (mul b c)) as [E1 _].
          assert (P1 := congP _ _ E1). rewrite P_true in P1. exact P1. 
       rewrite K1. 
       apply refS. 

       assert (J1 := mul_false _ _ Pa Pb). rewrite J1. rewrite J1. 
       assert (K1 : P (mul (mul a b) s) = true).
          destruct (s_ann (mul a b)) as [_ E1].
          assert (P1 := congP _ _ E1). rewrite P_true in P1. exact P1. 
       rewrite K1. apply refS. 

       assert (J1 := mul_false _ _ Pa Pb). rewrite J1. rewrite J1. 
       assert (J2 := mul_false _ _ Pb Pc). rewrite J2. rewrite J2. 
       assert (J3 := mul_false _ _ J1 Pc). rewrite J3.
       assert (J4 := mul_false _ _ Pa J2). rewrite J4.
       apply assoc. 
Qed. 
*) 

Lemma bop_associative_fpr_ann_v2 :
  ∀ (s : S) (mul : binary_op S),
     P(s) = true -> 
    (∀ (a b : S), eq a b = true -> P a = P b) ->
    (∀ (a b : S), P a = false -> P b = false -> P (mul a b) = false) ->        
    bop_congruence S eq mul ->     
    bop_is_ann S eq mul s ->     
    bop_associative S eq mul ->
         bop_associative S (brel_reduce (uop_predicate_reduce s P) eq) (bop_fpr s P mul).
Proof. intros s mul P_true congP mul_false cong_mul s_ann assoc a b c.
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

       assert (J1 := mul_false _ _ Pb Pc). rewrite J1. rewrite J1.        
       assert (K1 : P (mul s (mul b c)) = true).
          destruct (s_ann (mul b c)) as [E1 _].
          assert (P1 := congP _ _ E1). rewrite P_true in P1. exact P1. 
       rewrite K1. 
       rewrite P_true. apply refS. 

       assert (J1 := mul_false _ _ Pa Pb). rewrite J1. rewrite J1. 
       assert (K1 : P (mul (mul a b) s) = true).
          destruct (s_ann (mul a b)) as [_ E1].
          assert (P1 := congP _ _ E1). rewrite P_true in P1. exact P1. 
       rewrite K1. rewrite P_true. apply refS. 

       assert (J1 := mul_false _ _ Pa Pb). rewrite J1. rewrite J1. 
       assert (J2 := mul_false _ _ Pb Pc). rewrite J2. rewrite J2. 
       assert (J3 := mul_false _ _ J1 Pc). rewrite J3.
       assert (J4 := mul_false _ _ Pa J2). rewrite J4.
       rewrite J3. rewrite J4. apply assoc. 
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

(*
Lemma bop_left_distributive_fpr :
  ∀ (s : S) (add mul : binary_op S),
     P(s) = true -> 
    (∀ (a b : S), eq a b = true -> P a = P b) ->
    (∀ (a b : S), P a = false -> P b = false -> P (add a b) = false) ->        
    (∀ (a b : S), P a = false -> P b = false -> P (mul a b) = false) ->
    bop_congruence S eq add ->     
    bop_congruence S eq mul -> 
    bop_is_id S eq add s ->     
    bop_is_ann S eq mul s ->
    bop_left_distributive S eq add mul ->
         bop_left_distributive S eq (bop_fpr s P add) (bop_fpr s P mul).
Proof. intros s add mul P_true congP add_false mul_false cong_add cong_mul s_id s_ann ldist a b c.
       assert (fpr_cong_mul := bop_fpr_congruence s mul congP cong_mul).
       assert (fpr_cong_add := bop_fpr_congruence s add congP cong_add).        
       case_eq (P a); intro Pa.
          assert(K1 := bop_fpr_ann_true s mul P_true congP s_ann a c (inl Pa)).
          assert(P1 := congP _ _ K1). rewrite P_true in P1. 
          assert(K2 := bop_fpr_ann_true s mul P_true congP s_ann a b (inl Pa)).
          assert(P2 := congP _ _ K2). rewrite P_true in P2.           
          assert(K3 := bop_fpr_id_true_true s add P_true congP s_id _ _ P2 P1).
          assert(K6 := bop_fpr_ann_true s mul P_true congP s_ann a ((bop_fpr s P add b c)) (inl Pa)).
          apply symS in K3.
          assert (K7 := tranS _ _ _ K6 K3).
          exact K7.
          case_eq (P b); intro Pb.
             assert(K1 := bop_fpr_ann_true s mul P_true congP s_ann a b (inr Pb)).
             case_eq (P c); intro Pc.
                assert(K2 := bop_fpr_ann_true s mul P_true congP s_ann a c (inr Pc)).
                assert (K3 := fpr_cong_add _ _ _ _ K1 K2).
                assert (K4 := bop_fpr_id_true_true s add P_true congP s_id _ _ Pb Pc).             
                assert (P4 := congP _ _ K4). rewrite P_true in P4.
                assert (K5 := bop_fpr_ann_true s mul P_true congP s_ann a _ (inr P4)).
                assert (K6 := bop_fpr_id_true_true s add P_true congP s_id _ _ P_true P_true).
                assert (K7 := tranS _ _ _ K3 K6). apply symS in K7.
                assert (K8 := tranS _ _ _ K5 K7).
                exact K8.
                assert (K2 : eq (bop_fpr s P mul a (bop_fpr s P add b c)) (mul a c) = true).
                   assert (K3 := bop_fpr_id_true_false s add congP s_id _ _ Pb Pc).
                   assert (K4 := fpr_cong_mul _ _ _ _ (refS a) K3).
                   assert (K5 := bop_fpr_false_false s mul mul_false _ _ Pa Pc).
                   assert (K6 := tranS _ _ _ K4 K5).
                   exact K6.
                assert (K3 : eq (mul a c) (bop_fpr s P add (bop_fpr s P mul a b) (bop_fpr s P mul a c)) = true).
                   assert (K4 := bop_fpr_ann_true s mul P_true congP s_ann a b (inr Pb)).
                   assert (K5 := bop_fpr_false_false s mul mul_false _ _ Pa Pc).
                   assert (P4 := congP _ _ K4). rewrite P_true in P4.
                   assert (P5 := mul_false _ _ Pa Pc). 
                   assert (P6 := congP _ _ K5). rewrite P5 in P6.
                   assert (K6 := bop_fpr_id_true_false s add congP s_id _ _ P4 P6).
                   assert (K7 := tranS _ _ _ K6 K5).
                   apply symS.
                   exact K7.
                assert (K4 := tranS _ _ _ K2 K3). 
                exact K4.
                case_eq (P c); intro Pc.
                assert (K2 : eq (bop_fpr s P mul a (bop_fpr s P add b c)) (mul a b) = true).
                   assert (K3 := bop_fpr_id_false_true s add congP s_id _ _ Pb Pc).
                   assert (P3 := congP _ _ K3). rewrite Pb in P3.
                   assert (K4 := bop_fpr_false_false s mul mul_false _ _ Pa P3).
                   assert (K5 := cong_mul _ _ _ _ (refS a) K3).
                   assert (K6 := tranS _ _ _ K4 K5).
                   exact K6.
                assert (K3 : eq (mul a b)  (bop_fpr s P add (bop_fpr s P mul a b) (bop_fpr s P mul a c)) = true).
                   assert (K4 := bop_fpr_false_false s mul mul_false _ _ Pa Pb).
                   assert (K5 := bop_fpr_ann_true s mul P_true congP s_ann a c (inr Pc)).
                   assert (Pab := mul_false _ _ Pa Pb).
                   assert (K6 := fpr_cong_add _ _ _ _ K4 K5).
                   assert (K7 := bop_fpr_id_false_true s add congP s_id _ _ Pab P_true).
                   assert (K8 := tranS _ _ _ K6 K7).
                   apply symS.
                   exact K8.
                assert (K4 := tranS _ _ _ K2 K3).
                exact K4. 
                assert (K2 : eq (bop_fpr s P mul a (bop_fpr s P add b c)) (mul a (add b c)) = true).
                   assert (K3 := bop_fpr_false_false s add add_false _ _ Pb Pc).
                   assert (Pbc := add_false _ _ Pb Pc).
                   assert (P3 := congP _ _ K3). rewrite Pbc in P3.
                   assert (K4 := bop_fpr_false_false s mul mul_false _ _ Pa P3).
                   assert (K5 := cong_mul _ _ _ _ (refS a) K3).
                   assert (K6 := tranS _ _ _ K4 K5).
                   exact K6.
                assert (K3 : eq (add (mul a b) (mul a c)) (bop_fpr s P add (bop_fpr s P mul a b) (bop_fpr s P mul a c)) = true).
                   assert (K4 := bop_fpr_false_false s mul mul_false _ _ Pa Pb).
                   assert (K5 := bop_fpr_false_false s mul mul_false _ _ Pa Pc).
                   assert (Pac := mul_false _ _ Pa Pc).
                   assert (Pab := mul_false _ _ Pa Pb).
                   assert (K6 := fpr_cong_add _ _ _ _ K4 K5).
                   assert (K7 := bop_fpr_false_false s add add_false _ _ Pab Pac).
                   assert (K8 := tranS _ _ _ K6 K7).
                   apply symS.
                   exact K8.
                assert (K4 := ldist a b c). 
                assert (K5 := tranS _ _ _ K2 K4).
                assert (K6 := tranS _ _ _ K5 K3).
                exact K6.
Qed.
 *)

Lemma bop_left_distributive_fpr_v2 :
  ∀ (s : S) (add mul : binary_op S),
     P(s) = true -> 
    (∀ (a b : S), eq a b = true -> P a = P b) ->
    (∀ (a b : S), P a = false -> P b = false -> P (add a b) = false) ->        
    (∀ (a b : S), P a = false -> P b = false -> P (mul a b) = false) ->
    bop_congruence S eq add ->     
    bop_congruence S eq mul -> 
    bop_is_id S eq add s ->     
    bop_is_ann S eq mul s ->
    bop_left_distributive S eq add mul ->
    bop_left_distributive S (brel_reduce (uop_predicate_reduce s P) eq) (bop_fpr s P add) (bop_fpr s P mul).
Proof. intros s add mul P_true congP add_false mul_false cong_add cong_mul s_id s_ann ldist a b c.
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
       assert (PaddSAC := congP (add s (mul a c)) (mul a c) addSACL). rewrite mulAC in PaddSAC. rewrite PaddSAC. rewrite PaddSAC.
       assert (PmulASC := mul_false a (add s c) L PaddSC). rewrite PmulASC. rewrite PmulASC.
       assert (mulASC := cong_mul a (add s c) a c (refS a) addSCL).
       assert (K := tranS _ _ _ mulASC (symS _ _ addSACL)). exact K.
       assert (addBS := s_id b). destruct addBS as [addBSL addBSR].
       assert (PaddBS := congP (add b s) b addBSR). rewrite M in PaddBS. rewrite PaddBS. rewrite PaddBS.
       assert (PmulAB := mul_false a b L M). rewrite PmulAB. rewrite PmulAB.
       assert (mulAS := s_ann a). destruct mulAS as [mulASL mulASR].
       assert (PmulAS := congP (mul a s) s mulASR). rewrite P_true in PmulAS. rewrite PmulAS. rewrite P_true.
       assert (addSAB := s_id (mul a b)). destruct addSAB as [addSABL addSABR].
       assert (PaddSAB := congP (add (mul a b) s) (mul a b) addSABR). rewrite PmulAB in PaddSAB. rewrite PaddSAB. rewrite PaddSAB.
       assert (PmulSABC := mul_false a (add b s) L PaddBS). rewrite PmulSABC. rewrite PmulSABC.
       assert (mulASB := cong_mul a (add b s) a b (refS a) addBSR).
       assert (K := tranS _ _ _ mulASB (symS _ _ addSABR)). exact K.
       assert (addBC := add_false b c M N). rewrite addBC. rewrite addBC.
       assert (mulAB := mul_false a b L M). rewrite mulAB. rewrite mulAB.
       assert (mulAC := mul_false a c L N). rewrite mulAC. rewrite mulAC.
       assert (mulAABC := mul_false a (add b c) L addBC). rewrite mulAABC. rewrite mulAABC.
       assert (addMABMAC := add_false (mul a b) (mul a c) mulAB mulAC). rewrite addMABMAC. rewrite addMABMAC.
       assert (K := ldist a b c). exact K.
Qed.

(*
Lemma bop_right_distributive_fpr :
  ∀ (s : S) (add mul : binary_op S),
     P(s) = true -> 
    (∀ (a b : S), eq a b = true -> P a = P b) ->
    (∀ (a b : S), P a = false -> P b = false -> P (add a b) = false) ->        
    (∀ (a b : S), P a = false -> P b = false -> P (mul a b) = false) ->
    bop_congruence S eq add ->     
    bop_congruence S eq mul -> 
    bop_is_id S eq add s ->     
    bop_is_ann S eq mul s ->
    bop_right_distributive S eq add mul ->
         bop_right_distributive S eq (bop_fpr s P add) (bop_fpr s P mul).
Proof. intros s add mul P_true congP add_false mul_false cong_add cong_mul s_id s_ann ldist a b c.
       assert (fpr_cong_mul := bop_fpr_congruence s mul congP cong_mul).
       assert (fpr_cong_add := bop_fpr_congruence s add congP cong_add).        
       case_eq (P a); intro Pa.
          assert(K1 := bop_fpr_ann_true s mul P_true congP s_ann c a (inr Pa)).
          assert(P1 := congP _ _ K1). rewrite P_true in P1. 
          assert(K2 := bop_fpr_ann_true s mul P_true congP s_ann b a (inr Pa)).
          assert(P2 := congP _ _ K2). rewrite P_true in P2.           
          assert(K3 := bop_fpr_id_true_true s add P_true congP s_id _ _ P2 P1).
          assert(K6 := bop_fpr_ann_true s mul P_true congP s_ann (bop_fpr s P add b c) a (inr Pa)).
          apply symS in K3.
          assert (K7 := tranS _ _ _ K6 K3).
          exact K7.
          case_eq (P b); intro Pb.
             assert(K1 := bop_fpr_ann_true s mul P_true congP s_ann b a (inl Pb)).
             case_eq (P c); intro Pc.
                assert(K2 := bop_fpr_ann_true s mul P_true congP s_ann c a (inl Pc)).
                assert (K3 := fpr_cong_add _ _ _ _ K1 K2).
                assert (K4 := bop_fpr_id_true_true s add P_true congP s_id _ _ Pb Pc).             
                assert (P4 := congP _ _ K4). rewrite P_true in P4.
                assert (K5 := bop_fpr_ann_true s mul P_true congP s_ann _ a (inl P4)).
                assert (K6 := bop_fpr_id_true_true s add P_true congP s_id _ _ P_true P_true).
                assert (K7 := tranS _ _ _ K3 K6). apply symS in K7.
                assert (K8 := tranS _ _ _ K5 K7).
                exact K8.
                assert (K2 : eq (bop_fpr s P mul (bop_fpr s P add b c) a) (mul c a) = true).
                   assert (K3 := bop_fpr_id_true_false s add congP s_id _ _ Pb Pc).
                   assert (K4 := fpr_cong_mul _ _ _ _ K3 (refS a)).
                   assert (K5 := bop_fpr_false_false s mul mul_false _ _ Pc Pa).
                   assert (K6 := tranS _ _ _ K4 K5).
                   exact K6.
                assert (K3 : eq (mul c a) (bop_fpr s P add (bop_fpr s P mul b a) (bop_fpr s P mul c a)) = true).
                   assert (K4 := bop_fpr_ann_true s mul P_true congP s_ann b a (inl Pb)).
                   assert (K5 := bop_fpr_false_false s mul mul_false _ _ Pc Pa).
                   assert (P4 := congP _ _ K4). rewrite P_true in P4.
                   assert (P5 := mul_false _ _ Pc Pa). 
                   assert (P6 := congP _ _ K5). rewrite P5 in P6.
                   assert (K6 := bop_fpr_id_true_false s add congP s_id _ _ P4 P6).
                   assert (K7 := tranS _ _ _ K6 K5).
                   apply symS.
                   exact K7.
                assert (K4 := tranS _ _ _ K2 K3). 
                exact K4.
                case_eq (P c); intro Pc.
                assert (K2 : eq (bop_fpr s P mul (bop_fpr s P add b c) a) (mul b a) = true).
                   assert (K3 := bop_fpr_id_false_true s add congP s_id _ _ Pb Pc).
                   assert (P3 := congP _ _ K3). rewrite Pb in P3.
                   assert (K4 := bop_fpr_false_false s mul mul_false _ _ P3 Pa).
                   assert (K5 := cong_mul _ _ _ _ K3 (refS a)).
                   assert (K6 := tranS _ _ _ K4 K5).
                   exact K6.
                assert (K3 : eq (mul b a)  (bop_fpr s P add (bop_fpr s P mul b a) (bop_fpr s P mul c a)) = true).
                   assert (K4 := bop_fpr_false_false s mul mul_false _ _ Pb Pa).
                   assert (K5 := bop_fpr_ann_true s mul P_true congP s_ann c a (inl Pc)).
                   assert (Pab := mul_false _ _ Pb Pa).
                   assert (K6 := fpr_cong_add _ _ _ _ K4 K5).
                   assert (K7 := bop_fpr_id_false_true s add congP s_id _ _ Pab P_true).
                   assert (K8 := tranS _ _ _ K6 K7).
                   apply symS.
                   exact K8.
                assert (K4 := tranS _ _ _ K2 K3).
                exact K4. 
                assert (K2 : eq (bop_fpr s P mul (bop_fpr s P add b c) a) (mul (add b c) a) = true).
                   assert (K3 := bop_fpr_false_false s add add_false _ _ Pb Pc).
                   assert (Pbc := add_false _ _ Pb Pc).
                   assert (P3 := congP _ _ K3). rewrite Pbc in P3.
                   assert (K4 := bop_fpr_false_false s mul mul_false _ _ P3 Pa).
                   assert (K5 := cong_mul _ _ _ _ K3 (refS a)).
                   assert (K6 := tranS _ _ _ K4 K5).
                   exact K6.
                assert (K3 : eq (add (mul b a) (mul c a)) (bop_fpr s P add (bop_fpr s P mul b a) (bop_fpr s P mul c a)) = true).
                   assert (K4 := bop_fpr_false_false s mul mul_false _ _ Pb Pa).
                   assert (K5 := bop_fpr_false_false s mul mul_false _ _ Pc Pa).
                   assert (Pac := mul_false _ _ Pc Pa).
                   assert (Pab := mul_false _ _ Pb Pa).
                   assert (K6 := fpr_cong_add _ _ _ _ K4 K5).
                   assert (K7 := bop_fpr_false_false s add add_false _ _ Pab Pac).
                   assert (K8 := tranS _ _ _ K6 K7).
                   apply symS.
                   exact K8.
                assert (K4 := ldist a b c). 
                assert (K5 := tranS _ _ _ K2 K4).
                assert (K6 := tranS _ _ _ K5 K3).
                exact K6.
Qed.
 *)

Lemma bop_right_distributive_fpr_v2 :
  ∀ (s : S) (add mul : binary_op S),
     P(s) = true -> 
    (∀ (a b : S), eq a b = true -> P a = P b) ->
    (∀ (a b : S), P a = false -> P b = false -> P (add a b) = false) ->        
    (∀ (a b : S), P a = false -> P b = false -> P (mul a b) = false) ->
    bop_congruence S eq add ->     
    bop_congruence S eq mul -> 
    bop_is_id S eq add s ->     
    bop_is_ann S eq mul s ->
    bop_right_distributive S eq add mul ->
         bop_right_distributive S (brel_reduce (uop_predicate_reduce s P) eq) (bop_fpr s P add) (bop_fpr s P mul).
Proof. intros s add mul P_true congP add_false mul_false cong_add cong_mul s_id s_ann rdist a b c.
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






                                                                                                                           