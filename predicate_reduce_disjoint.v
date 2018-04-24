Require Export Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.   
Require Import CAS.basic. 
Require Import CAS.properties.
Require Import CAS.brel_add_constant.
Require Import CAS.bop_add_id.
Require Import CAS.bop_add_ann. 
Require Import CAS.bop_full_reduce. 


Definition uop_predicate_reduce_disjoint : ∀ {S : Type}, cas_constant -> (S -> bool) -> unary_op (cas_constant + S)
:= λ  {S} c p x,
   match x with     
   | inl a => x
   | inr a => if p a then inl c else x
   end.

Lemma uop_predicate_reduce_disjoint_congruence :
  ∀ (S : Type)(c : cas_constant) (P : S -> bool) (eq : brel S),
       brel_reflexive S eq ->
       pred_congruence S eq P -> 
       uop_congruence (cas_constant + S) (brel_add_constant eq c) (uop_predicate_reduce_disjoint c P). 
Proof. intros S c P eq refS congP [l1 | r1] [l2 | r2]; compute; intro H; compute; auto.
       discriminate H. discriminate H. 
       case_eq(P r1); intro H1; case_eq(P r2); intro H2; auto.
       apply congP in H. rewrite H1 in H. rewrite H2 in H. discriminate H.
       apply congP in H. rewrite H1 in H. rewrite H2 in H. discriminate H.        
Qed.

Lemma uop_predicate_reduce_disjoint_idempotent :
  ∀ (S : Type)(c : cas_constant) (P : S -> bool) (eq : brel S),
       brel_reflexive S eq -> 
       uop_idempotent (cas_constant + S) (brel_add_constant eq c) (uop_predicate_reduce_disjoint c P). 
Proof. intros S c P eq refS [l | r]; compute; auto.
       case_eq(P r); intro H; auto.
       rewrite H. apply refS. 
Qed.

Definition bop_fprd_add_id {S : Type} (c : cas_constant) (P : S -> bool) (bS : binary_op S) := 
  (bop_full_reduce (uop_predicate_reduce_disjoint c P) (bop_add_id bS c)).

Definition bop_fprd_add_ann {S : Type} (c : cas_constant) (P : S -> bool) (bS : binary_op S) := 
  (bop_full_reduce (uop_predicate_reduce_disjoint c P) (bop_add_ann bS c)).


Lemma bop_congruence_fprd_add_id :
  ∀ (S : Type)(c : cas_constant) (P : S -> bool) (eq : brel S) (bS : binary_op S),
    brel_reflexive S eq ->
    brel_symmetric S eq ->     
    pred_congruence S eq P -> 
    bop_congruence S eq bS -> 
    bop_congruence (cas_constant + S) (brel_reduce (uop_predicate_reduce_disjoint c P) (brel_add_constant eq c)) (bop_fprd_add_id c P bS). 
Proof. intros S c P eq bS refS symS Pcong cong.
       apply bop_full_reduce_congruence; auto.
       apply uop_predicate_reduce_disjoint_congruence; auto.
       apply bop_add_id_congruence; auto.
Qed.        

Lemma bop_congruence_fprd_add_ann :
  ∀ (S : Type)(c : cas_constant) (P : S -> bool) (eq : brel S) (bS : binary_op S),
    brel_reflexive S eq ->
    brel_symmetric S eq ->     
    pred_congruence S eq P -> 
    bop_congruence S eq bS -> 
    bop_congruence (cas_constant + S) (brel_reduce (uop_predicate_reduce_disjoint c P) (brel_add_constant eq c)) (bop_fprd_add_ann c P bS). 
Proof. intros S c P eq bS refS symS Pcong cong.
       apply bop_full_reduce_congruence; auto.
       apply uop_predicate_reduce_disjoint_congruence; auto.
       apply bop_add_ann_congruence; auto.
Qed.        



Lemma bop_pseudo_associative_fprd_add_id :
  ∀ (S : Type)(c : cas_constant) (P : S -> bool) (eq : brel S) (bS : binary_op S),
    brel_reflexive S eq ->
    bop_associative S eq bS -> 
    pred_bop_decompose S P bS -> 
       bop_pseudo_associative (cas_constant + S) (brel_add_constant eq c) (uop_predicate_reduce_disjoint c P) (bop_add_id bS c). 
Proof. intros S c P eq bS refS assoc H [r1 | l1] [r2 | l2] [r3 | l3]; compute; auto.
       case_eq(P l3); intro H1; auto. rewrite H1. rewrite H1. apply refS. 
       case_eq(P l2); intro H1; auto. rewrite H1. rewrite H1. apply refS. 
       case_eq(P l2); intro H1; case_eq(P l3); intro H2; auto. rewrite H2. rewrite H2. apply refS. 
       rewrite H1. rewrite H1. apply refS. rewrite H1.
       case_eq(P (bS l2 l3)); intro H3; auto. rewrite H3. apply refS. 
       case_eq(P l1); intro H1; auto. rewrite H1. rewrite H1. apply refS.
       case_eq(P l1); intro H1; case_eq(P l3); intro H2; auto. rewrite H2. rewrite H2. apply refS.        
       rewrite H1. rewrite H1. apply refS. rewrite H1.
       case_eq(P (bS l1 l3)); intro H3; auto. rewrite H2. rewrite H3; auto. 
       rewrite H2. rewrite H3. apply refS. 
       case_eq(P l1); intro H1; case_eq(P l2); intro H2; auto. rewrite H2. rewrite H2. apply refS.
       rewrite H1. rewrite H1. apply refS. 
       case_eq(P (bS l1 l2)); intro H3; auto. rewrite H2. rewrite H3; auto.
       rewrite H3. rewrite H2. rewrite H3. apply refS.
       case_eq(P l1); intro H1; case_eq(P l2); intro H2; case_eq(P l3); intro H3; auto.
       rewrite H3. rewrite H3. apply refS.       
       rewrite H2. rewrite H2. apply refS.       
       rewrite H2.
       case_eq(P (bS l2 l3)); intro H4; auto. rewrite H4. apply refS.        
       rewrite H1. rewrite H1. apply refS.
       rewrite H1.
       case_eq(P (bS l1 l3)); intro H4; auto. rewrite H3. rewrite H4; auto.
       rewrite H3. rewrite H4. apply refS.
       case_eq(P (bS l1 l2)); intro H4; auto. rewrite H2. rewrite H4; auto.
       rewrite H4. rewrite H2. rewrite H4. apply refS.       
       case_eq(P (bS l1 l2)); intro H4; auto. 
       destruct (H l1 l2 H4) as [L | R].
       rewrite L in H1. discriminate.
       rewrite R in H2. discriminate.
       case_eq(P (bS (bS l1 l2) l3)); intro H5; auto.
       destruct (H _ _ H5) as [L | R].
       rewrite L in H4. discriminate.
       rewrite R in H3. discriminate.
       case_eq(P (bS l2 l3)); intro H6; auto. 
       destruct (H _ _ H6) as [L | R].
       rewrite L in H2. discriminate.
       rewrite R in H3. discriminate.
       case_eq(P (bS l1 (bS l2 l3))); intro H7. 
       destruct (H _ _ H7) as [L | R].
       rewrite L in H1. discriminate.
       rewrite R in H6. discriminate.
       apply assoc.        
Qed.


Lemma bop_associative_fprd_add_id :
  ∀ (S : Type)(c : cas_constant) (P : S -> bool) (eq : brel S) (bS : binary_op S),
    pred_congruence S eq P -> 
    brel_reflexive S eq ->
    brel_symmetric S eq ->  
    brel_transitive S eq ->
    bop_congruence S eq bS ->     
    bop_associative S eq bS ->
    pred_bop_decompose S P bS -> 
        bop_associative (cas_constant + S) (brel_reduce (uop_predicate_reduce_disjoint c P) (brel_add_constant eq c)) (bop_fprd_add_id c P bS). 
Proof. intros S c P eq bS P_cong refS symS tranS cong accos H. unfold bop_fprd_add_id. 
       apply bop_full_reduce_pseudo_associative_implies_associative; auto.
       apply brel_add_constant_reflexive; auto. 
       apply brel_add_constant_symmetric; auto.
       apply brel_add_constant_transitive; auto.        
       apply uop_predicate_reduce_disjoint_idempotent; auto.
       apply uop_predicate_reduce_disjoint_congruence; auto.
       apply bop_add_id_congruence; auto. 
       apply bop_pseudo_associative_fprd_add_id; auto. 
Qed. 



Lemma bop_left_uop_invariant_fprd_add_ann :
  ∀ (S : Type)(c : cas_constant) (P : S -> bool) (eq : brel S) (bS : binary_op S),
       brel_reflexive S eq -> 
       pred_bop_compose S P bS -> 
       bop_left_uop_invariant (cas_constant + S) (brel_add_constant eq c) (bop_reduce (uop_predicate_reduce_disjoint c P) (bop_add_ann bS c)) (uop_predicate_reduce_disjoint c P).
Proof. intros S c P eq bS refS H [r1 | l1] [r2 | l2]; compute; auto; case_eq(P l1); intro H1; auto. 
       assert (K := H l1 l2 (inl H1)). rewrite K; auto. 
       case_eq(P (bS l1 l2)); intro H2; auto. 
Qed. 

Lemma bop_right_uop_invariant_fprd_add_ann :
  ∀ (S : Type)(c : cas_constant) (P : S -> bool) (eq : brel S) (bS : binary_op S),
    brel_reflexive S eq ->
    pred_bop_compose S P bS -> 
       bop_right_uop_invariant (cas_constant + S) (brel_add_constant eq c) (bop_reduce (uop_predicate_reduce_disjoint c P) (bop_add_ann bS c)) (uop_predicate_reduce_disjoint c P).
Proof. intros S c P eq bS refS H [r1 | l1] [r2 | l2]; compute; auto; case_eq(P l2); intro H1; auto. 
       assert (K := H l1 l2 (inr H1)). rewrite K; auto. 
       case_eq(P (bS l1 l2)); intro H2; auto. 
Qed.

Lemma bop_associative_fprd_add_ann_compositional :
  ∀ (S : Type)(c : cas_constant) (P : S -> bool) (eq : brel S) (bS : binary_op S),
    pred_congruence S eq P ->     
    brel_reflexive S eq ->
    brel_symmetric S eq ->  
    brel_transitive S eq ->
    pred_bop_compose S P bS ->
    bop_congruence S eq bS ->         
    bop_associative S eq bS ->
        bop_associative (cas_constant + S) (brel_reduce (uop_predicate_reduce_disjoint c P) (brel_add_constant eq c)) (bop_fprd_add_ann c P bS).      
Proof. intros S c P eq bS P_cong refS symS tranS H cong assoc.
       apply bop_full_reduce_left_right_invariant_implies_associative; auto.
       apply brel_add_constant_reflexive; auto. 
       apply brel_add_constant_symmetric; auto.
       apply brel_add_constant_transitive; auto.        
       apply uop_predicate_reduce_disjoint_idempotent; auto.
       apply uop_predicate_reduce_disjoint_congruence; auto.
       apply bop_add_ann_congruence; auto. 
       apply bop_add_ann_associative; auto. 
       apply bop_left_uop_invariant_fprd_add_ann; auto.
       apply bop_right_uop_invariant_fprd_add_ann; auto.
Qed.

Lemma bop_pseudo_associative_fprd_add_ann :
  ∀ (S : Type)(c : cas_constant) (P : S -> bool) (eq : brel S) (bS : binary_op S),
    brel_reflexive S eq ->
    pred_congruence S eq P ->         
    bop_associative S eq bS -> 
    pred_bop_decompose S P bS -> 
       bop_pseudo_associative (cas_constant + S) (brel_add_constant eq c) (uop_predicate_reduce_disjoint c P) (bop_add_ann bS c). 
Proof. intros S c P eq bS refS P_cong assoc H [r1 | l1] [r2 | l2] [r3 | l3]; compute; auto.
       case_eq(P l1); intro H1; auto.
       case_eq(P l1); intro H1; case_eq(P l3); intro H3; auto. 
       case_eq(P l1); intro H1; case_eq(P l2); intro H2; auto. 
       case_eq(P (bS l1 l2)); intro H4; auto. 
       case_eq(P l1); intro H1; case_eq(P l2); intro H2; case_eq(P l3); intro H3; auto.
       case_eq(P (bS l1 l2)); intro H4; auto.
       case_eq(P (bS l1 l2)); intro H4; auto.
       destruct (H _ _ H4) as [L | R].
       rewrite L in H1. discriminate.
       rewrite R in H2. discriminate.
       assert (K := assoc l1 l2 l3). 
       case_eq( P (bS (bS l1 l2) l3)); intro H5; auto.
       destruct (H _ _ H5) as [L | R].
       rewrite L in H4. discriminate.
       rewrite R in H3. discriminate.
       assert (J := P_cong _ _ K). rewrite H5 in J.
       case_eq(P (bS l2 l3)); intro H6; auto.
       destruct (H _ _ H6) as [L | R].
       rewrite L in H2. discriminate.
       rewrite R in H3. discriminate.
       rewrite <- J.
       exact K. 
Qed.

Lemma bop_associative_fprd_add_ann_decompositional :
  ∀ (S : Type)(c : cas_constant) (P : S -> bool) (eq : brel S) (bS : binary_op S),
    pred_congruence S eq P -> 
    brel_reflexive S eq ->
    brel_symmetric S eq ->  
    brel_transitive S eq ->
    bop_congruence S eq bS ->     
    bop_associative S eq bS ->
    pred_bop_decompose S P bS -> 
        bop_associative (cas_constant + S) (brel_reduce (uop_predicate_reduce_disjoint c P) (brel_add_constant eq c)) (bop_fprd_add_ann c P bS). 
Proof. intros S c P eq bS P_cong refS symS tranS cong accos H. unfold bop_fprd_add_ann. 
       apply bop_full_reduce_pseudo_associative_implies_associative; auto.
       apply brel_add_constant_reflexive; auto. 
       apply brel_add_constant_symmetric; auto.
       apply brel_add_constant_transitive; auto.        
       apply uop_predicate_reduce_disjoint_idempotent; auto.
       apply uop_predicate_reduce_disjoint_congruence; auto.
       apply bop_add_ann_congruence; auto. 
       apply bop_pseudo_associative_fprd_add_ann; auto. 
Qed. 

(* 
*) 

Lemma bop_left_distributive_full_predicate_reduce_disjoint : 
  ∀ (S : Type)(c : cas_constant) (P : S -> bool) (eq : brel S) (add mul : binary_op S),
     brel_reflexive S eq -> 
     pred_congruence S eq P -> 
     pred_bop_decompose S P add ->     
     pred_bop_decompose S P mul -> 
     bop_left_distributive S eq add mul ->    
     bop_left_distributive (cas_constant + S)
                           (brel_reduce (uop_predicate_reduce_disjoint c P) (brel_add_constant eq c))
                           (bop_fprd_add_id c P add)                                 
                           (bop_fprd_add_ann c P mul).      
Proof. intros S c P eq add mul refS P_cong Dadd Dmul ldist [c1 | x] [c2 | y] [c3 | z]; compute; auto.
       case_eq(P x); intro H1; auto.
       case_eq(P x); intro H1; case_eq(P z); intro H2; auto.
       rewrite H2. rewrite H2.
       case_eq(P (mul x z)); intro H3; auto.
       rewrite H3. rewrite H3. rewrite H3. apply refS. 
       case_eq(P x); intro H1; case_eq(P y); intro H2; auto.
       rewrite H2.  rewrite H2. 
       case_eq(P (mul x y)); intro H3; auto.
       rewrite H3. rewrite H3. rewrite H3. apply refS. 
       case_eq(P x); intro H1; case_eq(P y); intro H2; case_eq(P z); intro H3; auto.
       rewrite H3. rewrite H3.
       case_eq(P (mul x z)); intro H4; auto.
       rewrite H4. rewrite H4. rewrite H4. apply refS. 
       rewrite H2. rewrite H2.
       case_eq(P (mul x y)); intro H4; auto.
       rewrite H4. rewrite H4. rewrite H4. apply refS. 
       case_eq(P (add y z)); intro H4; auto.
       destruct (Dadd _ _ H4) as [L | R].
       rewrite L in H2. discriminate.
       rewrite R in H3. discriminate.
       rewrite H4.
       assert (K := ldist x y z). 
       case_eq(P (mul x (add y z))); intro H5; auto.
       case_eq(P (mul x y)); intro H6; case_eq(P (mul x z)); intro H7; auto.
       rewrite H7. rewrite H7. rewrite H7.
       destruct (Dmul _ _ H6) as [L | R].
       rewrite L in H1. discriminate.
       rewrite R in H2. discriminate.
       rewrite H6. rewrite H6. rewrite H6.
       destruct (Dmul _ _ H7) as [L | R].
       rewrite L in H1. discriminate.
       rewrite R in H3. discriminate.
       rewrite H6. rewrite H7.
       case_eq(P (add (mul x y) (mul x z))); intro H8; auto.
       rewrite H8.
       destruct (Dmul _ _ H5) as [L | R].
       rewrite L in H1. discriminate.
       rewrite R in H4. discriminate.
       case_eq(P (mul x (add y z))); intro H6; auto.
       rewrite H6 in H5. discriminate. 
       case_eq(P (mul x y)); intro H7; case_eq(P (mul x z)); intro H8; auto.
       destruct (Dmul _ _ H7) as [L | R].
       rewrite L in H1. discriminate.
       rewrite R in H2. discriminate.
       rewrite H8. rewrite H8. rewrite H8.
       destruct (Dmul _ _ H7) as [L | R].
       rewrite L in H1. discriminate.
       rewrite R in H2. discriminate.
       rewrite H7. rewrite H7. rewrite H7.
       destruct (Dmul _ _ H8) as [L | R].
       rewrite L in H1. discriminate.
       rewrite R in H3. discriminate.
       rewrite H7. rewrite H8. 
       assert (K1 := P_cong _ _ K). rewrite H5 in K1.
       rewrite <- K1. rewrite <- K1. 
       exact K. 
Qed. 
      

Lemma bop_right_distributive_full_predicate_reduce_disjoint : 
  ∀ (S : Type)(c : cas_constant) (P : S -> bool) (eq : brel S) (add mul : binary_op S),
     brel_reflexive S eq -> 
     pred_congruence S eq P -> 
     pred_bop_decompose S P add ->     
     pred_bop_decompose S P mul -> 
     bop_right_distributive S eq add mul ->    
     bop_right_distributive (cas_constant + S)
                           (brel_reduce (uop_predicate_reduce_disjoint c P) (brel_add_constant eq c))
                           (bop_fprd_add_id c P add)                                 
                           (bop_fprd_add_ann c P mul).      
Proof. intros S c P eq add mul refS P_cong Dadd Dmul rdist [c1 | x] [c2 | y] [c3 | z]; compute; auto.
       case_eq(P z); intro H1; auto. rewrite H1. rewrite H1. reflexivity.
       case_eq(P y); intro H1; auto. rewrite H1. rewrite H1. reflexivity.
       case_eq(P y); intro H1; case_eq(P z); intro H2; auto.
       rewrite H2. rewrite H2. reflexivity.
       rewrite H1. rewrite H1. reflexivity.
       case_eq(P (add y z)); intro H3; auto.
       rewrite H3. reflexivity. 
       case_eq(P x); intro H1; case_eq(P z); intro H2; auto.
       rewrite H2. rewrite H2. reflexivity.
       rewrite H2. rewrite H2.
       case_eq(P (mul z x)); intro H3; auto.
       rewrite H3. rewrite H3. rewrite H3. apply refS.
       case_eq(P x); intro H1; case_eq(P y); intro H2; auto.
       rewrite H2. rewrite H2. reflexivity.      
       rewrite H2. rewrite H2.
       case_eq(P (mul y x)); intro H3; auto.
       rewrite H3. rewrite H3. rewrite H3. apply refS.
       case_eq(P x); intro H1; case_eq(P y); intro H2; case_eq(P z); intro H3; auto.
       rewrite H3. rewrite H3. reflexivity.      
       rewrite H2. rewrite H2. reflexivity.             
       case_eq(P (add y z)); intro H4; auto.
       rewrite H4. reflexivity.             
       rewrite H3. rewrite H3.
       case_eq(P (mul z x)); intro H4; auto.
       rewrite H4. rewrite H4. rewrite H4. apply refS. 
       rewrite H2. rewrite H2.
       case_eq(P (mul y x)); intro H4; auto.
       rewrite H4. rewrite H4. rewrite H4. apply refS. 
       case_eq(P (add y z)); intro H4; auto.
       destruct (Dadd _ _ H4) as [L | R].
       rewrite L in H2. discriminate.
       rewrite R in H3. discriminate.
       rewrite H4.
       assert (K := rdist x y z). 
       case_eq(P (mul (add y z) x)); intro H5; auto.
       case_eq(P (mul y x)); intro H6; case_eq(P (mul z x)); intro H7; auto.
       rewrite H7. rewrite H7. rewrite H7.
       destruct (Dmul _ _ H6) as [L | R].
       rewrite L in H2. discriminate.
       rewrite R in H1. discriminate.
       rewrite H6. rewrite H6. rewrite H6.
       destruct (Dmul _ _ H7) as [L | R].
       rewrite L in H3. discriminate.
       rewrite R in H1. discriminate.
       rewrite H6. rewrite H7.
       case_eq(P (add (mul y x) (mul z x))); intro H8; auto.
       rewrite H8.
       destruct (Dmul _ _ H5) as [L | R].
       rewrite L in H4. discriminate.
       rewrite R in H1. discriminate.
       case_eq(P (mul (add y z) x)); intro H6; auto.
       rewrite H6 in H5. discriminate. 
       case_eq(P (mul y x)); intro H7; case_eq(P (mul z x)); intro H8; auto.
       destruct (Dmul _ _ H7) as [L | R].
       rewrite L in H2. discriminate.
       rewrite R in H1. discriminate.
       rewrite H8. rewrite H8. rewrite H8.
       destruct (Dmul _ _ H7) as [L | R].
       rewrite L in H2. discriminate.
       rewrite R in H1. discriminate.
       rewrite H7. rewrite H7. rewrite H7.
       destruct (Dmul _ _ H8) as [L | R].
       rewrite L in H3. discriminate.
       rewrite R in H1. discriminate.
       rewrite H7. rewrite H8. 
       assert (K1 := P_cong _ _ K). rewrite H5 in K1.
       rewrite <- K1. rewrite <- K1. 
       exact K. 
Qed. 
      

