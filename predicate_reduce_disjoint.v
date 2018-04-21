Require Export Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.   
Require Import CAS.basic. 
Require Import CAS.properties. 
Require Import CAS.structures.


Definition uop_predicate_reduce_disjoint : ∀ {S : Type}, cas_constant -> (S -> bool) -> unary_op (cas_constant + S)
:= λ  {S} c p x,
   match x with     
   | inl a => x
   | inr a => if p a then inl c else x
   end.

Definition bop_fprd_add_id {S : Type} (c : cas_constant) (P : S -> bool) (bS : binary_op S) := 
  (bop_full_reduce (uop_predicate_reduce_disjoint c P) (bop_add_id bS c)).

Definition bop_fprd_add_ann {S : Type} (c : cas_constant) (P : S -> bool) (bS : binary_op S) := 
  (bop_full_reduce (uop_predicate_reduce_disjoint c P) (bop_add_ann bS c)).


Lemma uop_predicate_reduce_disjoint_idempotent :
  ∀ (S : Type)(c : cas_constant) (P : S -> bool) (eq : brel S),
       brel_reflexive S eq -> 
       uop_idempotent (cas_constant + S) (brel_add_constant eq c) (uop_predicate_reduce_disjoint c P). 
Proof. intros S c P eq refS [l | r]; compute; auto.
       case_eq(P r); intro H; auto.
       rewrite H. apply refS. 
Qed.

Lemma bop_pseudo_associative_predicate_disjoint (S : Type)(c : cas_constant) (P : S -> bool) (eq : brel S) (bS : binary_op S):
bop_pseudo_associative (cas_constant + S) (brel_add_constant eq c) (uop_predicate_reduce_disjoint c P) (bop_add_id bS c).
Proof. compute. intros s t u. destruct s.
Admitted.

Lemma bop_left_uop_invariant_fprd_add_ann :
  ∀ (S : Type)(c : cas_constant) (P : S -> bool) (eq : brel S) (bS : binary_op S),
       brel_reflexive S eq -> 
       (∀ (a b : S), P a = true -> P (bS a b) = true) ->  
       bop_left_uop_invariant (cas_constant + S) (brel_add_constant eq c) (bop_reduce (uop_predicate_reduce_disjoint c P) (bop_add_ann bS c)) (uop_predicate_reduce_disjoint c P).
Proof. intros S c P eq bS refS H [r1 | l1] [r2 | l2]; compute; auto; case_eq(P l1); intro H1; auto. 
       assert (K := H l1 l2 H1). rewrite K; auto. 
       case_eq(P (bS l1 l2)); intro H2; auto. 
Qed. 

Lemma bop_right_uop_invariant_fprd_add_ann :
  ∀ (S : Type)(c : cas_constant) (P : S -> bool) (eq : brel S) (bS : binary_op S),
       brel_reflexive S eq -> 
       (∀ (a b : S), P b = true -> P (bS a b) = true) ->  
       bop_right_uop_invariant (cas_constant + S) (brel_add_constant eq c) (bop_reduce (uop_predicate_reduce_disjoint c P) (bop_add_ann bS c)) (uop_predicate_reduce_disjoint c P).
Proof. intros S c P eq bS refS H [r1 | l1] [r2 | l2]; compute; auto; case_eq(P l2); intro H1; auto. 
       assert (K := H l1 l2 H1). rewrite K; auto. 
       case_eq(P (bS l1 l2)); intro H2; auto. 
Qed.


Lemma bop_left_uop_invariant_fprd_add_id :
  ∀ (S : Type)(c : cas_constant) (P : S -> bool) (eq : brel S) (bS : binary_op S),
       brel_reflexive S eq -> 
       (∀ (a b : S), P (bS a b) = true -> ((P a = true) + (P b = true))) ->
       (∀ (a b : S), P a = true -> P b = true -> P (bS a b) = true) ->  
       bop_left_uop_invariant (cas_constant + S) (brel_add_constant eq c) (bop_reduce (uop_predicate_reduce_disjoint c P) (bop_add_id bS c)) (uop_predicate_reduce_disjoint c P).
Proof. intros S c P eq bS refS H K [r1 | l1] [r2 | l2]; compute; auto.
       case_eq(P l2); intro H2; auto. 
       case_eq(P l1); intro H1; auto. rewrite H1. apply refS. 
       case_eq(P l1); intro H1; auto.
       case_eq(P l2); intro H2; auto. 
       case_eq(P (bS l1 l2)); intro H3; auto.
          rewrite (K l1 l2 H1 H2) in H3. discriminate H3. 
       case_eq(P (bS l1 l2)); intro H3; auto.
          admit. (* HELP !! This does not work*) 
          admit. (* HELP !! This does not work*) 
       case_eq(P (bS l1 l2)); intro H3; auto.       
Admitted. 
(*
Lemma bop_right_uop_invariant_fprd_add_ann :
  ∀ (S : Type)(c : cas_constant) (P : S -> bool) (eq : brel S) (bS : binary_op S),
       brel_reflexive S eq -> 
       (∀ (a b : S), P b = true -> P (bS a b) = true) ->  
       bop_right_uop_invariant (cas_constant + S) (brel_add_constant eq c) (bop_reduce (uop_predicate_reduce_disjoint c P) (bop_add_ann bS c)) (uop_predicate_reduce_disjoint c P).
Proof. intros S c P eq bS refS H [r1 | l1] [r2 | l2]; compute; auto; case_eq(P l2); intro H1; auto. 
       assert (K := H l1 l2 H1). rewrite K; auto. 
       case_eq(P (bS l1 l2)); intro H2; auto. 
Qed.
 *)


Lemma uop_predicate_reduce_disjoint_congruence :
  ∀ (S : Type)(c : cas_constant) (P : S -> bool) (eq : brel S),
       brel_reflexive S eq ->
       (∀ (a b : S), eq a b = true -> P a = P b) -> 
       uop_congruence (cas_constant + S) (brel_add_constant eq c) (uop_predicate_reduce_disjoint c P). 
Proof. intros S c P eq refS congP [l1 | r1] [l2 | r2]; compute; intro H; compute; auto.
       discriminate H. discriminate H. 
       case_eq(P r1); intro H1; case_eq(P r2); intro H2; auto.
       apply congP in H. rewrite H1 in H. rewrite H2 in H. discriminate H.
       apply congP in H. rewrite H1 in H. rewrite H2 in H. discriminate H.        
Qed.

      

Section Results.

Variable S : Type.
Variable c : cas_constant.
Variable P : S -> bool.

Variable eq : brel S. 
Variable refS : brel_reflexive S eq.

Variable ref_add_c : brel_reflexive (cas_constant + S) (brel_add_constant eq c).
Variable sym_add_c : brel_symmetric (cas_constant + S) (brel_add_constant eq c). 
Variable tran_add_c : brel_transitive (cas_constant + S) (brel_add_constant eq c).

Variable congP : ∀ (a b : S), eq a b = true -> P a = P b.

Variable add : binary_op S.
Variable mul : binary_op S.
Variable cong_add : bop_congruence S eq add.
Variable cong_mul : bop_congruence S eq mul. 

Notation "a == b"  := (eq a b = true)                     (at level 15).
Notation "a ~~ b"  := (brel_add_constant eq c a b = true) (at level 15).
Notation "a [+] b"  := (bop_fprd_add_id c P add a b)      (at level 15).
Notation "a [*] b"  := (bop_fprd_add_ann c P mul a b)     (at level 15).


Lemma bop_fprd_add_id_congruence : bop_congruence (cas_constant + S) (brel_add_constant eq c) (bop_fprd_add_id c P add).
Proof. intros [c1 | x1] [c2 | x2] [c3 | x3] [c4 | x4] E1 E2.
       compute. reflexivity.  
       compute in E2. discriminate E2.
       compute in E1. discriminate E1.
       compute in E1. discriminate E1.
       compute in E2. discriminate E2.       
Admitted. 

Lemma bop_fprd_add_ann_congruence : bop_congruence (cas_constant + S) (brel_add_constant eq c) (bop_fprd_add_ann c P mul).
Admitted.

Lemma bop_fprd_add_id_true_true : 
  ∀ a b : S,  (P a = true) -> (P b = true) -> (inr a) [+] (inr b) ~~ (inl c).
Proof. intros a b Pa Pb. compute. rewrite Pa, Pb.  reflexivity. Qed.

Lemma bop_fprd_add_id_false_true :
  ∀ a b : S,  (P a = false) -> (P b = true) -> (inr a) [+] (inr b) ~~ inr a.
Proof. intros a b Pa Pb. compute. rewrite Pa, Pb.  rewrite Pa. apply refS. Qed. 

Lemma bop_fprd_add_id_true_false :
  ∀ a b : S,  (P a = true) -> (P b = false) -> (inr a) [+] (inr b) ~~ inr b.
Proof. intros a b Pa Pb. compute. rewrite Pa, Pb.  rewrite Pb. apply refS. Qed. 

Lemma bop_fprd_add_id_false_false :
 (∀ (a b : S), P a = false -> P b = false -> P (add a b) = false) ->
  ∀ a b : S,  (P a = false) -> (P b = false) -> (inr a) [+] (inr b) ~~ inr (add a b).
Proof. intros add_false a b Pa Pb. compute. rewrite Pa, Pb.  rewrite (add_false _ _ Pa Pb) . apply refS. Qed. 

Lemma bop_fprd_add_id_id_true (c' : cas_constant) :
  ∀ b : S,  (P b = true) -> (inl c') [+] (inr b) ~~ inl c.
Proof. intros b Pb. compute. rewrite Pb. reflexivity. Qed. 

Lemma bop_fprd_add_id_id_false (c' : cas_constant) :
  ∀ b : S,  (P b = false) -> (inl c') [+] (inr b) ~~ inr b.
Proof. intros b Pb. compute. rewrite Pb. rewrite Pb. apply refS. Qed.


Lemma bop_fprd_add_id_true_id (c' : cas_constant) :
  ∀ a : S,  (P a = true) -> (inr a) [+] (inl c') ~~ inl c.
Proof. intros a Pa. compute. rewrite Pa. reflexivity. Qed. 

Lemma bop_fprd_add_id_false_id (c' : cas_constant) :
  ∀ a : S,  (P a = false) -> (inr a) [+] (inl c') ~~ inr a.
Proof. intros a Pa. compute. rewrite Pa. rewrite Pa. apply refS. Qed. 

Lemma bop_fprd_add_id_id_id (c' c'': cas_constant) : (inl c') [+] (inl c'') ~~ inl c.
Proof. compute. reflexivity. Qed.

Lemma bop_fprd_add_id_id_inr (c' : cas_constant) :
  ∀ b : S,  (inl c') [+] (inr b) ~~ (if P(b) then inl c else inr b). 
Proof. intros b. case_eq(P b); intro Pb; compute; rewrite Pb ;auto. rewrite Pb. apply refS. Qed. 

Lemma bop_fprd_add_id_inr_id (c' : cas_constant) :
  ∀ b : S,  (inr b) [+] (inl c') ~~ (if P(b) then inl c else inr b). 
Proof. intros b. case_eq(P b); intro Pb; compute; rewrite Pb ;auto. rewrite Pb. apply refS. Qed. 

(* fprd_ann_ann *) 
Lemma bop_fprd_add_ann_true_left :
  ∀ (a : S) (y : cas_constant + S), (P a = true) -> (inr a) [*] y ~~ inl c.
Proof. intros a y Pa. compute. 
       rewrite Pa. reflexivity.
Qed.

Lemma bop_fprd_add_ann_true_right :
  ∀ (x : cas_constant + S) (b : S),  (P b = true) -> x [*] (inr b) ~~ inl c.
Proof. intros [c' | a] b Pb; compute. 
       reflexivity.
       case_eq(P a) ; intro Pa.
          reflexivity.
          rewrite Pb. reflexivity.          
Qed.

Lemma bop_fprd_add_ann_false :
 (∀ (a b : S), P a = false -> P b = false -> P (mul a b) = false) ->
  ∀ a b : S,  (P a = false) -> (P b = false) -> (inr a) [*] (inr b) ~~ inr (mul a b).
Proof. intros mul_false a b Pa Pb. compute. rewrite Pa, Pb.  rewrite (mul_false _ _ Pa Pb) . apply refS. Qed.


Lemma bop_fprd_add_ann_left (c' : cas_constant) :
  ∀ y : cas_constant + S,  (inl c') [*] y ~~ inl c.
Proof. intro y. compute. reflexivity. Qed. 

Lemma bop_fprd_add_ann_right (c' : cas_constant) :
  ∀ x : cas_constant + S,  x [*] (inl c') ~~ inl c.
Proof. intros [c'' | a ]; compute.
       reflexivity.
       case_eq(P a); intro Pa; reflexivity. 
Qed. 

Lemma bop_fprd_add_ann_both (c' c'' : cas_constant) : (inl c') [*] (inl c'') = inl c.
Proof. compute. reflexivity. Qed. 

Lemma bop_left_distributive_full_predicate_reduce_disjoint :
    (∀ (a b : S), P a = false -> P b = false -> P (add a b) = false) ->        
    (∀ (a b : S), P a = false -> P b = false -> P (mul a b) = false) ->
     bop_left_distributive S eq add mul ->    
     bop_left_distributive (cas_constant + S) (brel_add_constant eq c) (bop_fprd_add_id c P add) (bop_fprd_add_ann c P mul).
Proof. intros add_false mul_false ldist [c1 | x] [c2 | y] [c3 | z].
       compute. reflexivity.
       
       apply (bop_fprd_add_ann_left c1).
       
       apply (bop_fprd_add_ann_left c1).
       
       apply (bop_fprd_add_ann_left c1).
       
       assert (E1 := bop_fprd_add_id_id_id c2 c3). 
       assert (E2 := bop_fprd_add_ann_congruence _ _ _ _ (ref_add_c (inr x)) E1).
       assert (E3 := bop_fprd_add_ann_right c (inr x)).
       assert (E4 := tran_add_c _ _ _ E2 E3).        
       assert (E5 := bop_fprd_add_ann_right c2 (inr x)).
       assert (E6 := bop_fprd_add_ann_right c3 (inr x)).               
       assert (E7 := bop_fprd_add_id_congruence _ _ _ _ E5 E6).
       assert (E8 := bop_fprd_add_id_id_id c c).
       assert (E9 := tran_add_c _ _ _ E7 E8). apply sym_add_c in E9.
       assert (E10 := tran_add_c _ _ _ E4 E9).
       exact E10.


       case_eq(P x); intro Px; case_eq(P z); intro Pz; compute; repeat (try rewrite Px; try rewrite Pz; auto).
          assert (Pxz := mul_false _ _ Px Pz). rewrite Pxz. rewrite Pxz. rewrite Pxz. apply refS. 

       case_eq(P x); intro Px; case_eq(P y); intro Py; compute; repeat (try rewrite Px; try rewrite Py; auto).
          assert (Pxy := mul_false _ _ Px Py). rewrite Pxy. rewrite Pxy. rewrite Pxy. apply refS.

       case_eq(P x); intro Px; case_eq(P y); intro Py; case_eq (P z); intro Pz; compute;
           repeat (try rewrite Px; try rewrite Py; try rewrite Pz; auto).  
           assert (Pxz := mul_false _ _ Px Pz). rewrite Pxz. rewrite Pxz. rewrite Pxz. apply refS. 
           assert (Pxy := mul_false _ _ Px Py). rewrite Pxy. rewrite Pxy. rewrite Pxy. apply refS.
           assert (Pyz_add := add_false _ _ Py Pz). rewrite Pyz_add. rewrite Pyz_add.
           assert (Pxyz := mul_false _ _ Px Pyz_add). rewrite Pxyz.
           assert (Pxy := mul_false _ _ Px Py). rewrite Pxy. rewrite Pxy.
           assert (Pxz := mul_false _ _ Px Pz). rewrite Pxz. rewrite Pxz.
           assert (Pxyxz := add_false _ _ Pxy Pxz). rewrite Pxyxz. 
           apply ldist. 
Qed. 

Lemma bop_associative_fprd_add_id :
    (∀ (a b : S), P a = false -> P b = false -> P (add a b) = false) ->        
     bop_associative S eq add ->    
     bop_associative (cas_constant + S) (brel_add_constant eq c) (bop_fprd_add_id c P add). 
Proof. intros add_false assoc [c1 | x] [c2 | y] [c3 | z]. 
       compute. reflexivity.
       case_eq(P z); intro Pz; compute; repeat (try rewrite Pz; auto). 
       case_eq(P y); intro Py; compute; repeat (try rewrite Py; auto).        
       case_eq(P y); intro Py; case_eq(P z); intro Pz; compute; repeat (try rewrite Py; try rewrite Pz; auto; try apply refS).
          assert(Pyz := add_false _ _ Py Pz). rewrite Pyz. rewrite Pyz. rewrite Pyz. apply refS. 
       case_eq(P x); intro Px; compute; repeat (try rewrite Px; auto). 
       case_eq(P x); intro Px; case_eq(P z); intro Pz; compute; repeat (try rewrite Px; try rewrite Pz; auto; try apply refS).
          assert(Pxz := add_false _ _ Px Pz). rewrite Pxz. apply refS. 
       case_eq(P x); intro Px; case_eq(P y); intro Py; compute; repeat (try rewrite Px; try rewrite Py; auto; try apply refS).
          assert(Pxy := add_false _ _ Px Py). rewrite Pxy. rewrite Pxy. rewrite Pxy. apply refS.           
       case_eq(P x); intro Px; case_eq(P y); intro Py; case_eq(P z); intro Pz; compute;
            repeat (try rewrite Px; try rewrite Py; try rewrite Pz; auto; try apply refS).
            assert(Pyz := add_false _ _ Py Pz). rewrite Pyz. rewrite Pyz. rewrite Pyz. apply refS. 
            assert(Pxz := add_false _ _ Px Pz). rewrite Pxz. apply refS. 
            assert(Pxy := add_false _ _ Px Py). rewrite Pxy. rewrite Pxy. rewrite Pxy. apply refS.           
            assert(Pxy := add_false _ _ Px Py). rewrite Pxy. rewrite Pxy.
            assert(Pyz := add_false _ _ Py Pz). rewrite Pyz. rewrite Pyz.
            assert(Pxyz := add_false _ _ Pxy Pz). rewrite Pxyz.
            assert(Px_yz := add_false _ _ Px Pyz). rewrite Px_yz.
            apply assoc. 
Qed. 


Lemma bop_associative_fprd_add_ann :
    (∀ (a b : S), P a = false -> P b = false -> P (mul a b) = false) ->        
     bop_associative S eq mul ->    
     bop_associative (cas_constant + S) (brel_add_constant eq c) (bop_fprd_add_ann c P mul). 
Proof. intros mul_false assoc [c1 | x] [c2 | y] [c3 | z]. 
       compute. reflexivity.
       case_eq(P z); intro Pz; compute; repeat (try rewrite Pz; auto). 
       case_eq(P y); intro Py; compute; repeat (try rewrite Py; auto).        
       case_eq(P y); intro Py; case_eq(P z); intro Pz; compute; repeat (try rewrite Py; try rewrite Pz; auto; try apply refS).
       case_eq(P x); intro Px; compute; repeat (try rewrite Px; auto). 
       case_eq(P x); intro Px; case_eq(P z); intro Pz; compute; repeat (try rewrite Px; try rewrite Pz; auto; try apply refS).
       case_eq(P x); intro Px; case_eq(P y); intro Py; compute; repeat (try rewrite Px; try rewrite Py; auto; try apply refS).
          assert(Pxy := mul_false _ _ Px Py). rewrite Pxy. rewrite Pxy. auto. 
       case_eq(P x); intro Px; case_eq(P y); intro Py; case_eq(P z); intro Pz; compute;
            repeat (try rewrite Px; try rewrite Py; try rewrite Pz; auto; try apply refS).
            assert(Pxy := mul_false _ _ Px Py). rewrite Pxy. rewrite Pxy. auto. 
            assert(Pxy := mul_false _ _ Px Py). rewrite Pxy. rewrite Pxy. 
            assert(Pxy_z := mul_false _ _ Pxy Pz). rewrite Pxy_z. 
            assert(Pyz := mul_false _ _ Py Pz). rewrite Pyz. rewrite Pyz. 
            assert(Px_yz := mul_false _ _ Px Pyz). rewrite Px_yz. 
            apply assoc. 
Qed. 


End Results. 