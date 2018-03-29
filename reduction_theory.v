Require Export Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.   
Require Import CAS.basic. 
Require Import CAS.properties. 
Require Import CAS.structures.
Require Import CAS.facts.

Section ReductionTheory.

Lemma observation1 (S : Type) (eq : brel S) (r : unary_op S) (b : binary_op S) :
  (bop_left_uop_invariant S eq (bop_reduce r b) r)
  <-> 
  (bop_left_uop_invariant S (brel_reduce r eq) b r).
Proof. compute. split; auto.   Qed. 

Lemma observation2 (S : Type) (eq : brel S) (r : unary_op S) (b : binary_op S) :
  (bop_right_uop_invariant S eq (bop_reduce r b) r)
  <-> 
  (bop_right_uop_invariant S (brel_reduce r eq) b r).
Proof. split; auto.   Qed. 

  

  Variable S : Type. 
  Variable b : binary_op S.
  Variable r : unary_op S.
  Variable eqS    : brel S.    

  Variable refS   : brel_reflexive S eqS. 
  Variable symS   : brel_symmetric S eqS. 
  Variable transS : brel_transitive S eqS.
  Variable eqS_cong : brel_congruence S eqS eqS.
  
  Definition transSf1 := brel_transitive_f1 S eqS symS transS. 
  Definition transSf2 := brel_transitive_f2 S eqS symS transS. 

  Variable b_cong : bop_congruence S eqS b. 
  Variable b_ass  : bop_associative S eqS b.

  (* make assumptions about r required to build the reduced semigroup *) 
  Variable r_cong  : uop_congruence S eqS r. 
  Variable r_idem  : uop_idempotent S eqS r. 
  Variable r_left  : bop_left_uop_invariant S eqS (bop_reduce r b) r.  (* eqS (r (b (r s1) s2)) (r (b s1 s2))  = true. *) 
  Variable r_right : bop_right_uop_invariant S eqS (bop_reduce r b) r. (* eqS (r (b s1 (r s2))) (r (b s1 s2))  = true. *)
  
   Lemma r_left_and_right : ∀ (s1 s2 : S), eqS (r (b s1 s2)) (r (b (r s1) (r s2))) = true. 
    Proof. intros s1 s2. 
           assert (H1 := r_left s1 s2). compute in H1. 
           assert (H2 := r_right (r s1) s2). compute in H2.            
           assert (H3 := transS _ _ _ H2 H1). apply symS. 
           exact H3.            
    Qed. 

  Definition Pr (x : S) := eqS (r x) x = true.  
  Definition red_Type   := { x : S & Pr x}.

  (* equality on red_Type is just equality on S, but need to project out first components! *) 
  Definition red_eq : brel red_Type := λ p1 p2, eqS ((projT1 p1)) ((projT1 p2)).

  Lemma red_ref : brel_reflexive red_Type red_eq. 
  Proof. intros [s p]. compute. apply refS. Qed.

       
  Lemma red_sym : brel_symmetric red_Type red_eq. 
  Proof. intros [s1 p1] [s2 p2].   compute. apply symS. Qed.

  Lemma red_cong : brel_congruence red_Type red_eq red_eq. 
  Proof. intros [s1 p1] [s2 p2] [s3 p3] [s4 p4].   compute. apply eqS_cong. Qed. 


  Lemma red_trans : brel_transitive red_Type red_eq. 
  Proof. intros [s1 p1] [s2 p2] [s3 p3]. compute. apply transS. Qed.

  Lemma Pr_br : ∀ (p1 p2 : red_Type), Pr (bop_reduce r b (projT1 p1) (projT1 p2)).
  Proof. intros [s1 p1] [s2 p2]. compute. apply r_idem. Defined. 

  Definition red_bop : binary_op red_Type :=
    λ p1 p2,  existT Pr (bop_reduce r b (projT1 p1) (projT1 p2)) (Pr_br p1 p2).

  Lemma red_bop_cong : bop_congruence red_Type red_eq red_bop.
  Proof. intros [s1 p1] [s2 p2] [s3 p3] [s4 p4]. compute.
         unfold Pr in *.  intros H1 H2.
         apply r_cong.
         apply b_cong; auto.
   Qed.          

  Lemma red_bop_ass : bop_associative red_Type red_eq red_bop. 
  Proof. intros [s1 p1] [s2 p2] [s3 p3]. compute.
         assert (H1 := r_left (b s1 s2) s3).
         assert (H2 := r_right s1 (b s2 s3)).
         assert (H3 := r_cong _ _ (b_ass s1 s2 s3)).
         apply symS in H2. 
         assert (H4 := transS _ _ _ H3 H2).
         assert (H5 := transS _ _ _ H1 H4).
         exact H5. 
  Qed.

  Definition inj (s : S) : red_Type := existT Pr (r s) (r_idem s).

  (*
     Look at IFF properties 
  *) 

  Lemma red_ref_iso : brel_reflexive red_Type red_eq <-> brel_reflexive S (brel_reduce r eqS).
  Proof. split. intros H s. compute.
         assert (K := H (inj s)).
         unfold red_eq in K. simpl in K.
         exact K. 
         intros H [s p]. unfold Pr in p.
         compute.
         assert (J1 := symS _ _ p).
         assert (J2 := transS _ _ _ J1 p).
         exact J2.
Qed.          

Lemma red_sym_iso : brel_symmetric red_Type red_eq <-> brel_symmetric S (brel_reduce r eqS).
  Proof. split. intros H s1 s2. compute.
         assert (K := H (inj s1) (inj s2)).
         unfold red_eq in K. simpl in K.
         exact K. 
         intros H [s1 p1] [s2 p2]. unfold Pr in p1. unfold Pr in p2.
         compute. intro H2. 
         assert (K := symS _ _ H2).
         exact K.
Qed.          

  Lemma red_tran_iso : brel_transitive red_Type red_eq <-> brel_transitive S (brel_reduce r eqS).
  Proof. split. intros H s1 s2 s3. compute. intros H1 H2. 
         assert (K := H (inj s1) (inj s2) (inj s3)). compute in K. 
         apply K; auto. 
         intros H [s1 p1] [s2 p2] [s3 p3]. 
         compute. apply transS. 
Qed.          

Lemma red_comm_iso :  bop_commutative red_Type red_eq red_bop <-> bop_commutative S (brel_reduce r eqS) (bop_full_reduce r b).
Proof. split.
         intros H s1 s2. compute.
         assert (K := H (inj s1) (inj s2)). compute in K.
         apply r_cong.
         exact K. 
         intros H1 [s1 p1] [s2 p2]. compute.
         assert (K := H1 s1 s2). compute in K. 
         unfold Pr in p1. unfold Pr in p2.
         assert (J1 := r_idem (b (r s1) (r s2))).
         assert (J2 := r_idem (b (r s2) (r s1))).
         apply symS in J1.
         assert (J3 := transS _ _ _ J1 K).
         assert (J4 := transS _ _ _ J3 J2).
         assert (J5 := b_cong _ _ _ _ p1 p2). apply r_cong in J5. 
         assert (J6 := b_cong _ _ _ _ p2 p1). apply r_cong in J6. 
         assert (J7 := transS _ _ _ J4 J6).         
         apply symS in J5. 
         assert (J8 := transS _ _ _ J5 J7).
         exact J8.
 Qed.




Lemma red_not_comm_iso_left :  bop_not_commutative red_Type red_eq red_bop -> bop_not_commutative S (brel_reduce r eqS) (bop_full_reduce r b).
Proof.   intros [[[s1 p1] [s2 p2]]  p3]. compute in p3.  unfold Pr in p1. unfold Pr in p2. 
         exists (s1, s2). compute.
         admit. 
Admitted.


Lemma red_not_comm_iso_right :  bop_not_commutative S (brel_reduce r eqS) (bop_full_reduce r b) -> bop_not_commutative red_Type red_eq red_bop. 
Proof.  intros [[s1 s2]  p]. exists (inj s1, inj s2). compute.  
        compute in p. 
         admit. 
Admitted.


  
         (* 
    Commutativity 
   *)
  (* 
    First, a sufficient condition ...
  *) 
  Lemma red_bop_comm : bop_commutative S eqS b -> bop_commutative red_Type red_eq red_bop. 
  Proof. intros H1 [s1 p1] [s2 p2]. compute.
         unfold bop_commutative in H1. 
         apply r_cong. apply H1. 
  Qed.

  (*
   f is a homomorphism for b and b' if 
    f(b(x, y)) = b'(f(x), f(y))

   The following show that 
    1) inj is a homomorphism for (bop_full_reduce r b) and red_bop. 
    2) projT1 is a homomorphism for red_bop and (bop_full_reduce r b). 
    3) (inj o projT1) is id on red_Type
    4) (projT1 o inj) is id on r(S), the image of r 

    so we have an isomorphism between (S, (bop_full_reduce r b) and (red_Type, bop_red) 

    HOWEVER, the isomorphism only works on the image of r, r(S). 

*)
  
  Lemma inj_homomorphism : ∀ (s1 s2 : S),  red_eq (inj (bop_full_reduce r b s1 s2)) (red_bop (inj s1) (inj s2)) = true. 
  Proof. intros s1 s2. compute. apply r_idem. Qed.
  
  Lemma proj1_homomorphism : ∀ (p1 p2 : red_Type),  eqS (projT1 (red_bop p1 p2)) (bop_full_reduce r b (projT1 p1) (projT1 p2)) = true. 
  Proof. intros [s1 P1] [s2 P2]. compute. compute in P1. compute in P2.
         apply r_cong.
         assert (K := b_cong _ _ _ _ P1 P2).  apply symS.
         exact K. 
  Qed. 

  Lemma inj_proj1_is_id : ∀ p : red_Type,  red_eq p (inj (projT1 p)) = true.
  Proof. intros [s P]. compute. compute in P. apply symS. exact P. Qed. 
  
  Lemma proj1_inj_is_id_on_image_of_r : ∀ s : S,  eqS (r s) (projT1 (inj (r s))) = true.
  Proof. intro s. compute. apply symS. apply r_idem. Qed.

  Lemma equality_lemma_1 : ∀ (p1 p2 : red_Type),  eqS (projT1 p1) (projT1 p2) = red_eq p1 p2.
  Proof. intros [s1 P1] [s2 P2]. compute. reflexivity. Qed.

  Lemma equality_lemma_2 : ∀ (s1 s2 : S),  eqS (r s1) (r s2) = red_eq (inj s1) (inj s2).
  Proof. intros s1 s2. compute. reflexivity. Qed. 

(* Now, let's look at preservation of basic properties 

*) 

  Lemma congruence_iso :
          (∀ s : S, eqS (r s) s = true -> {z : S & eqS (r z) s = true}) -> 
              (bop_congruence S eqS (bop_full_reduce r b) <-> 
               bop_congruence red_Type red_eq red_bop). 
  Proof. intro C. split.
         (* bop_congruence S eqS (bop_full_reduce r b) → bop_congruence red_Type red_eq red_bop *) 
         compute.
         intros H [x1 P1] [x2 P2] [x3 P3] [x4 P4] H1 H2. 
         destruct (C x1 P1) as [z1 R1].
         destruct (C x2 P2) as [z2 R2].
         destruct (C x3 P3) as [z3 R3].
         destruct (C x4 P4) as [z4 R4].         
         assert (J1 := b_cong _ _ _ _ R1 R2). apply r_cong in J1. 
         assert (J2 := b_cong _ _ _ _ R3 R4). apply r_cong in J2. 
         apply symS in J1.
         assert (K := H (r z1) (r z2) (r z3) (r z4)).
         assert (E1 : eqS (r z1) (r z3) = true).
             assert (E3 := transS _ _ _ R1 H1). apply symS in R3.
             assert (E4 := transS _ _ _ E3 R3).
             exact E4. 
         assert (E2 : eqS (r z2) (r z4) = true).
             assert (E3 := transS _ _ _ R2 H2). apply symS in R4.
             assert (E4 := transS _ _ _ E3 R4).
             exact E4.              
         assert (K2 := K E1 E2).
         (* r_left_and_right : ∀ (s1 s2 : S), eqS (r (b s1 s2)) (r (b (r s1) (r s2))) = true.  *)          
         assert (K3 := r_left_and_right (r z1) (r z2)). 
         assert (J3 := transS _ _ _ J1 K3).
         assert (J4 := transS _ _ _ J3 K2).
         assert (K4 := r_left_and_right (r z3) (r z4)). apply symS in K4.
         assert (J5 := transS _ _ _ J4 K4).
         assert (J6 := transS _ _ _ J5 J2).                  
         exact J6.
         (* bop_congruence red_Type red_eq red_bop → bop_congruence S eqS (bop_full_reduce r b) *)
         compute. 
         intros H s1 s2 s3 s4 H1 H2.
         apply r_cong in H1.
         apply r_cong in H2.                   
         assert (K := H (inj s1) (inj s2) (inj s3) (inj s4) H1 H2). 
         exact K. 
  Qed.
  
  

  Lemma commutative_iso_1 :
          (∀ s : S, eqS (r s) s = true -> {z : S & eqS (r z) s = true}) -> 
              bop_commutative S eqS (bop_full_reduce r b) -> bop_commutative red_Type red_eq red_bop. 
  Proof. intro C.  compute.
         intros H [s P] [t Q].
         destruct (C s P) as [z1 R1].
         destruct (C t Q) as [z2 R2].         
         assert (K := H z1 z2).
         assert (J1 := b_cong _ _ _ _ R1 R2). apply r_cong in J1. 
         assert (J2 := b_cong _ _ _ _ R2 R1). apply r_cong in J2. 
         apply symS in J1.
         assert (J3 := transS _ _ _ J1 K).
         assert (J4 := transS _ _ _ J3 J2).
         exact J4.
  Qed.

  Lemma commutative_iso_2 :
            bop_commutative red_Type red_eq red_bop → bop_commutative S eqS (bop_full_reduce r b).
  Proof. compute. 
         intros H s t.
         assert (K := H (inj s) (inj t)).
         compute in K.
         exact K. 
  Qed.

  Lemma sanity : ∀ s : S, eqS (r s) s = true → {z : S & eqS (r z) s = true}.
  Proof. intros s H. exists (r s).
         assert (K := r_idem s).
         assert (J := transS _ _ _ K H). 
         exact J.
   Qed. 
 
  Lemma commutative_iso :
            bop_commutative red_Type red_eq red_bop <-> bop_commutative S eqS (bop_full_reduce r b).
  Proof. split.
         apply commutative_iso_2.
         apply commutative_iso_1.
         apply sanity. 
  Qed.

 Lemma not_commutative_implies :
    bop_not_commutative S eqS (bop_full_reduce r b) → bop_not_commutative red_Type red_eq red_bop.
  Proof. intros [[s1 s2] Q]. compute in Q. 
         exists (inj s1, inj s2). compute. 
         exact Q. 
  Qed.

Definition brel_symmetric_f (S : Type) (r : brel S) := 
    ∀ s t : S, (r s t = false) → (r t s = false). 

Lemma not_commutative_2:
    bop_not_commutative red_Type red_eq red_bop ->
    bop_not_commutative S eqS (bop_full_reduce r b).
Proof. intros  [[s1 s2] Q]. compute in s1. compute in s2.
          compute. 
          exists (projT1 s1, projT1 s2). compute. compute in Q.
          assert (M := r_left_and_right (let (a, _) := s2 in a) (let (a, _) := s1 in a)).
          assert (N := r_left_and_right (let (a, _) := s1 in a) (let (a, _) := s2 in a)).
          assert (X := brel_transitive_f1 S eqS symS transS 
                (r (b (let (a, _) := s1 in a) (let (a, _) := s2 in a)))
                (r (b (let (a, _) := s2 in a) (let (a, _) := s1 in a)))
                (r (b (r (let (a, _) := s2 in a)) (r (let (a, _) := s1 in a))))
                Q M).
          apply symS in N.
          assert (Y := brel_transitive_f2 S eqS symS transS 
                  (r (b (r (let (a, _) := s1 in a)) (r (let (a, _) := s2 in a))))
                  (r (b (let (a, _) := s1 in a) (let (a, _) := s2 in a)))
                  (r (b (r (let (a, _) := s2 in a)) (r (let (a, _) := s1 in a))))
                  N X).
          exact Y.
Qed.
        

  Lemma associative_iso :
          (∀ s : S, eqS (r s) s = true -> {z : S & eqS (r z) s = true}) -> 
              (bop_associative S eqS (bop_full_reduce r b) <-> bop_associative red_Type red_eq red_bop). 
  Proof. intro C. split.
         (*  bop_associative S eqS (bop_full_reduce r b) → bop_associative red_Type red_eq red_bop   *) 
         compute.
         intros H [x1 P1] [x2 P2] [x3 P3]. 
         destruct (C x1 P1) as [z1 R1].
         destruct (C x2 P2) as [z2 R2].
         destruct (C x3 P3) as [z3 R3].
         assert (K := H z1 z2 z3).
         assert (K2 := r_left (r (b (r z1) (r z2))) (r z3)). compute in K2. apply symS in K2.
         assert (K3 := transS _ _ _ K2 K). 
         assert (K4 := r_right (r z1) (r (b (r z2) (r z3)))). compute in K4.
         assert (K5 := transS _ _ _ K3 K4).
         assert (K6 : eqS (r (b (r (b x1 x2)) x3)) (r (b (r (b (r z1) (r z2))) (r z3))) = true).
             apply r_cong.
             apply b_cong.
             apply r_cong.
             apply b_cong.
             apply symS; auto.
             apply symS; auto.              
             apply symS; auto. 
         assert (K7 : eqS (r (b (r z1) (r (b (r z2) (r z3))))) (r (b x1 (r (b x2 x3)))) = true).
             apply r_cong.
             apply b_cong.
             apply symS; auto.             
             apply r_cong.
             apply b_cong.
             apply symS; auto.              
             apply symS; auto.              
         assert (K8 := transS _ _ _ K6 K5).
         assert (K9 := transS _ _ _ K8 K7).          
         exact K9.  
         (*  bop_associative red_Type red_eq red_bop → bop_associative S eqS (bop_full_reduce r b) *)
         compute. 
         intros H s1 s2 s3.
         assert (K := H (inj s1) (inj s2) (inj s3)). compute in K.
         assert (J1 := r_left (r (b (r s1) (r s2))) (r s3)). compute in J1.
         assert (J2 := transS _ _ _ J1 K).
         assert (J3 := r_right (r s1) (r (b (r s2) (r s3)))). compute in J3.
         apply symS in J3.
         assert (J4 := transS _ _ _ J2 J3).         
         exact J4. 
  Qed.
  
  



  (* 
      idempotence 
  *)   
  Lemma red_bop_idem : bop_idempotent S eqS b -> bop_idempotent red_Type red_eq red_bop. 
  Proof. intros idemS [s p]. compute.
         assert (H1 := idemS s).
         unfold Pr in p.
         assert (H2 := r_cong _ _ H1).
         assert (H3 := transS _ _ _ H2 p). 
         exact H3. 
  Qed.                                  

  (* 
      Selectivity 
  *)   
  Lemma red_bop_sel : bop_selective S eqS b -> bop_selective red_Type red_eq red_bop. 
  Proof. intros selS [s1 p1] [s2 p2]. compute.
         destruct (selS s1 s2) as [H1 | H1].
         left. unfold Pr in p1. 
         assert (H2 := r_cong _ _ H1).
         assert (H3 := transS _ _ _ H2 p1). 
         exact H3.
         right. unfold Pr in p2. 
         assert (H2 := r_cong _ _ H1).
         assert (H3 := transS _ _ _ H2 p2). 
         exact H3. 
  Qed.                                  

  Lemma red_bop_id : uop_preserves_id S eqS b r -> bop_exists_id S eqS b -> bop_exists_id red_Type red_eq red_bop. 
  Proof. intros H [id p]. exists (inj id). unfold bop_is_id in p. unfold bop_is_id.
         intros [t pt]. compute.
         destruct (p t) as [H1  H2]. split. 
         assert (H3 := H id p).
          assert (H4 := r_left  id t). compute in H4.
          assert (H5 := r_cong _ _ H1).
          assert (H6 := transS _ _ _ H4 H5).
          compute in pt.
          assert (H7 := transS _ _ _ H6 pt).
          exact H7.
          assert (H3 := H id p).
          assert (H4 := r_right  t id). compute in H4.
          assert (H5 := r_cong _ _ H2).
          assert (H6 := transS _ _ _ H4 H5).
          compute in pt.
          assert (H7 := transS _ _ _ H6 pt).
          exact H7.
Qed.


  Lemma red_bop_ann : uop_preserves_ann S eqS b r -> bop_exists_ann S eqS b -> bop_exists_ann red_Type red_eq red_bop. 
  Proof. intros H [ann p]. exists (inj ann). unfold bop_is_ann in p. unfold bop_is_ann.
         intros [t pt]. compute.
         destruct (p t) as [H1  H2]. split. 
         assert (H3 := H ann p).
          assert (H4 := r_left  ann t). compute in H4.
          assert (H5 := r_cong _ _ H1).
          assert (H6 := transS _ _ _ H4 H5).
          exact H6.
          assert (H3 := H ann p).
          assert (H4 := r_right  t ann). compute in H4.
          assert (H5 := r_cong _ _ H2).
assert (H6 := transS _ _ _ H4 H5).
          exact H6.
  Qed.



End ReductionTheory.
