Require Export Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.   
Require Import CAS.basic. 
Require Import CAS.properties. 
Require Import CAS.structures.
Require Import CAS.product.
Require Import CAS.facts.
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




End PredicateReduce.







Section ReduceAnnihilators.

  Variable S : Type.
  Variable T : Type.     
  Variable eqS : brel S.
  Variable eqT : brel T.
  Variable refS : brel_reflexive S eqS.
  Variable symS : brel_symmetric S eqS.
  Variable tranS : brel_transitive S eqS.    
  Variable refT : brel_reflexive T eqT.
  Variable symT : brel_symmetric T eqT.
  Variable tranT : brel_transitive T eqT.      
  Variable aS : S.
  Variable aT : T.
  Variable mulS : binary_op S.
  Variable mulT : binary_op T.
  Variable cong_mulS : bop_congruence S eqS mulS.
  Variable cong_mulT : bop_congruence T eqT mulT.
  Variable ass_mulS : bop_associative S eqS mulS.
  Variable ass_mulT : bop_associative T eqT mulT.
  Variable is_annS : bop_is_ann S eqS mulS aS.
  Variable is_annT : bop_is_ann T eqT mulT aT.
  Variable no_annS_div : ∀ a b : S,  eqS (mulS a b) aS = true -> (eqS a aS = true) + (eqS b aS = true).  
  Variable no_annT_div : ∀ a b : T,  eqT (mulT a b) aT = true -> (eqT a aT = true) + (eqT b aT = true).  

  Definition P : (S *T) -> bool := λ p, match p with (s, t) => orb (eqS s aS) (eqT t aT) end. 

  Definition uop_rap : unary_op (S * T) := uop_predicate_reduce (aS, aT) P.

  Definition bop_rap : binary_op (S * T) := bop_fpr (aS, aT) P (bop_product mulS mulT).

  Lemma P_congruence : ∀ (p1 p2 : S * T), brel_product eqS eqT p1 p2 = true -> P p1 = P p2.
  Proof. intros [s1 t1] [s2 t2]; compute; intro H.
         case_eq(eqS s1 aS); intro J1; case_eq(eqS s2 aS); intro J2; auto.
         assert (J3 : eqS s1 s2 = false).
(*  HERE WE ARE         
           apply (brel_transitive_f1 S eqS symS tranS s2 aS s1 J2 (symS _ _ J1)). 
*)       admit. 
         rewrite J3 in H. discriminate H. 
         case_eq(eqS s1 s2); intro J3.
         rewrite J3 in H. admit. 
         rewrite J3 in H. discriminate H. 
Admitted.           

Lemma P_true : P(aS, aT) = true. Proof. compute; auto. rewrite refS; auto. Qed.

  Lemma P_false_preservation : ∀ (p1 p2 : S * T), P p1 = false -> P p2 = false -> P (bop_product mulS mulT p1 p2) = false.
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

Lemma bop_rap_congruence : bop_congruence (S * T) (brel_product eqS eqT) bop_rap.
Proof. unfold bop_rap. unfold bop_fpr. 
       apply bop_full_reduce_congruence; auto.
       apply uop_predicate_reduce_congruence; auto.
       apply brel_product_reflexive; auto.
       apply P_congruence; auto.
       apply bop_product_congruence; auto. 
Qed.        

(* move this .... *) 
Lemma  bop_product_is_ann : bop_is_ann (S * T) (brel_product eqS eqT) (bop_product mulS mulT) (aS, aT).
Proof. intros [s t]; compute. destruct (is_annS s) as [LS RS]. destruct (is_annT t) as [LT RT].
       rewrite LS, RS. rewrite LT, RT; auto. 
Qed.

Lemma  bop_rap_is_ann : bop_is_ann (S * T) (brel_product eqS eqT) bop_rap (aS, aT).
Proof.  intros [s t]; compute. rewrite refS.
        case_eq(eqS s aS); intro J1. 
        destruct (is_annS aS) as [LS RS]. destruct (is_annT aT) as [LT RT].
        rewrite LS.  rewrite refS. rewrite refT; auto.
        case_eq(eqT t aT); intro J2.
        destruct (is_annS aS) as [LS RS]. destruct (is_annT aT) as [LT RT].
        rewrite LS.  rewrite refS. rewrite refT; auto.
        destruct (is_annS s) as [LS RS]. destruct (is_annT t) as [LT RT].
       rewrite LS, RS. rewrite refS. rewrite refT; auto.
Qed.  

Lemma bop_rap_associative :  bop_associative (S * T) (brel_product eqS eqT) bop_rap.
Proof. apply bop_associative_fpr_ann; auto.
       apply brel_product_reflexive; auto. 
       apply P_true; auto. 
       apply P_congruence; auto. 
       apply P_false_preservation; auto.
       apply bop_product_congruence; auto.
       apply bop_product_is_ann; auto.
       apply bop_product_associative; auto.
Qed.




Lemma bop_rap_commutative :  bop_commutative S eqS mulS -> bop_commutative T eqT mulT -> bop_commutative (S * T) (brel_product eqS eqT) bop_rap.
Proof. intros C1 C2 [s1 t1] [s2 t2]. unfold bop_rap. unfold bop_fpr.
       apply bop_full_reduce_commutative; auto. 
       apply uop_predicate_reduce_congruence; auto.
       apply brel_product_reflexive; auto.
       apply P_congruence; auto.
       apply bop_product_commutative; auto.
Qed.        
  
End ReduceAnnihilators.

(*
Definition rap_product (S T : Type) : commutative_semigroup_with_ann S ->  commutative_semigroup_with_ann T ->  commutative_semigroup_with_ann (S * T) := 
  λ sg1 sg2,
{|
   ceqa   := brel_product (ceqa S sg1) (ceqa T sg2)
;  cbopa  := bop_rap S T (ceqa S sg1) (ceqa T sg2) (canna S sg1) (canna T sg2) (cbopa S sg1) (cbopa T sg2)
;  canna  := (canna S sg1, canna T sg2) 
;  ceqva  := eqv_proofs_product S T  (ceqa S sg1) (ceqa T sg2) (ceqva S sg1) (ceqva T sg2) 
;  csgpa  := {|
                csgwa_associative   := bop_rap_associative
              ; csgwa_congruence    := bop_rap_congruence
              ; csgwa_commutative   := bop_rap_commutative
              ; csgwa_is_ann        := bop_rap_is_ann
            |}

|}.
  
*) 