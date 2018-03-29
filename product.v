Require Export Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.   
Require Import CAS.basic. 
Require Import CAS.properties. 
Require Import CAS.structures.

Section ProductTheory.

  Variable S : Type.
  Variable T : Type.

  Variable eqS    : brel S.
  Variable eqT    : brel T.

  Variable wS    : S.
  Variable wT    : T.

  Variable eqS_cong : brel_congruence S eqS eqS.
  Variable eqT_cong : brel_congruence T eqT eqT.   

  Variable bS : binary_op S.
  Variable bT : binary_op T.      

  Variable refS   : brel_reflexive S eqS. 
  Variable symS   : brel_symmetric S eqS. 
  Variable transS : brel_transitive S eqS.

  Variable refT   : brel_reflexive T eqT. 
  Variable symT   : brel_symmetric T eqT. 
  Variable transT : brel_transitive T eqT.

  Variable bS_cong : bop_congruence S eqS bS. 
  Variable bS_ass  : bop_associative S eqS bS.

  Variable bT_cong : bop_congruence T eqT bT. 
  Variable bT_ass  : bop_associative T eqT bT.  

Lemma andb_intro : ∀ b1 b2 : bool, (b1 = true) * (b2 = true) → b1 && b2 = true. 
Proof. induction b1; induction b2; simpl; auto; intros [L R]; auto. Qed. 

Lemma andb_elim : ∀ b1 b2 : bool, b1 && b2 = true → (b1 = true) * (b2 = true). 
Proof. induction b1; induction b2; auto. Qed.
  
Lemma brel_product_symmetric : brel_symmetric (S * T) (brel_product eqS eqT). 
Proof. intros [s1 t1] [s2 t2]; simpl. intro H. 
     apply andb_intro. 
     apply andb_elim in H. 
     destruct H as [HL HR]; split; auto. 
Qed. 

Lemma brel_product_reflexive : brel_reflexive (S * T) (brel_product eqS eqT). 
Proof. intros [s t] ; simpl; apply andb_intro; auto. Qed.

Lemma brel_product_transitive : brel_transitive (S * T) (brel_product eqS eqT). 
Proof. intros [s1 t1] [s2 t2] [s3 t3]; simpl. intros H1 H2.
       apply andb_elim in H1; apply andb_elim in H2.
       apply andb_intro. 
       destruct H1 as [H1L H1R]; destruct H2 as [H2L H2R]; split.
       apply (transS _ _ _ H1L H2L).
       apply (transT _ _ _ H1R H2R).
Qed.

Lemma brel_product_congruence : brel_congruence (S * T) (brel_product eqS eqT) (brel_product eqS eqT). 
Proof. intros [s1 s2] [t1 t2] [u1 u2] [w1 w2]; simpl. intros H1 H2. 
       destruct (andb_elim _ _ H1) as [C1 C2].
       destruct (andb_elim _ _ H2) as [C3 C4].
       assert (CS := eqS_cong _ _ _ _ C1 C3).
       assert (CT := eqT_cong _ _ _ _ C2 C4).
       rewrite CS, CT. reflexivity. 
Qed. 

Lemma bop_product_congruence : bop_congruence (S * T) (brel_product eqS eqT) (bop_product bS bT). 
Proof. intros [s1 s2] [t1 t2] [u1 u2] [w1 w2]; simpl. intros H1 H2. 
       destruct (andb_elim _ _ H1) as [C1 C2].
       destruct (andb_elim _ _ H2) as [C3 C4].
       apply andb_intro. split.  
          apply bS_cong; auto. 
          apply bT_cong; auto. 
Qed. 

Lemma bop_product_associative : bop_associative (S * T) (brel_product eqS eqT) (bop_product bS bT). 
Proof. intros [s1 s2] [t1 t2] [u1 u2]; simpl.
       apply andb_intro. split.
       apply bS_ass. apply bT_ass.
Qed.        


Lemma bop_product_commutative : bop_commutative S eqS bS -> bop_commutative T eqT bT -> bop_commutative (S * T) (brel_product eqS eqT) (bop_product bS bT). 
Proof. intros Scomm Tcomm [s1 s2] [t1 t2] ; compute. 
       apply andb_intro. split.
       apply Scomm. apply Tcomm.
Qed.        


Lemma bop_product_not_commutative_left : bop_not_commutative S eqS bS -> bop_not_commutative (S * T) (brel_product eqS eqT) (bop_product bS bT). 
Proof. intros [ [s1 s2] P].
       exists ((s1, wT), (s2, wT)).
       compute. rewrite P. reflexivity. 
Qed.        

Lemma bop_product_not_commutative_right : bop_not_commutative T eqT bT -> bop_not_commutative (S * T) (brel_product eqS eqT) (bop_product bS bT).
Proof. intros [ [t1 t2] P].
       exists ((wS, t1), (wS, t2)).
       compute. rewrite refS. exact P. 
Qed.        

Lemma bop_product_commutative_decidable :
  bop_commutative_decidable S eqS bS -> bop_commutative_decidable T eqT bT -> bop_commutative_decidable (S * T) (brel_product eqS eqT) (bop_product bS bT). 
Proof. intros [Scomm | SNcomm] [Tcomm | TNcomm].
       exact (inl (bop_product_commutative Scomm Tcomm)).
       exact (inr (bop_product_not_commutative_right TNcomm)).
       exact (inr (bop_product_not_commutative_left SNcomm)).
       exact (inr (bop_product_not_commutative_right TNcomm)).               
Qed.        


Lemma  bop_product_is_ann : ∀ (aS : S) (aT : T) (is_annS : bop_is_ann S eqS bS aS) (is_annS : bop_is_ann T eqT bT aT),  
       bop_is_ann (S * T) (brel_product eqS eqT) (bop_product bS bT) (aS, aT).
Proof. intros aS aT is_annS is_annT [s t]; compute. destruct (is_annS s) as [LS RS]. destruct (is_annT t) as [LT RT].
       rewrite LS, RS. rewrite LT, RT; auto. 
Qed.


Lemma  bop_product_is_id : ∀ (aS : S) (aT : T) (is_idS : bop_is_id S eqS bS aS) (is_idT : bop_is_id T eqT bT aT),  
       bop_is_id (S * T) (brel_product eqS eqT) (bop_product bS bT) (aS, aT).
Proof. intros aS aT is_idS is_idT [s t]; compute. destruct (is_idS s) as [LS RS]. destruct (is_idT t) as [LT RT].
       rewrite LS, RS. rewrite LT, RT; auto. 
Qed.


End ProductTheory.

Section Product_Semigroup.


  
Definition eqv_proofs_product : ∀ (S T : Type) (eqS : brel S) (eqT : brel T),  
    eqv_proofs S eqS → eqv_proofs T eqT → eqv_proofs (S * T) (brel_product eqS eqT)
:= λ S T eqS eqT eqvS eqvT,
{|
  eqv_reflexive      := brel_product_reflexive S T eqS eqT (eqv_reflexive S eqS eqvS) (eqv_reflexive T eqT eqvT)
; eqv_transitive     := brel_product_transitive S T eqS eqT (eqv_transitive S eqS eqvS) (eqv_transitive T eqT eqvT)
; eqv_symmetric      := brel_product_symmetric S T eqS eqT (eqv_symmetric S eqS eqvS) (eqv_symmetric T eqT eqvT)
; eqv_congruence     := brel_product_congruence S T eqS eqT (eqv_congruence S eqS eqvS) (eqv_congruence T eqT eqvT)  
; eqv_witness        := (eqv_witness S eqS eqvS, eqv_witness T eqT eqvT)                                               
|}.


Definition sg_proofs_product :
  ∀ (S T : Type) (eqS : brel S) (eqT : brel T) (eqvS : eqv_proofs S eqS) (eqvT : eqv_proofs T eqT) (bS : binary_op S) (bT : binary_op T),
    (semigroup_proofs S eqS bS) -> (semigroup_proofs T eqT bT)
               -> semigroup_proofs (S * T) (brel_product eqS eqT )(bop_product bS bT) 
:= λ S T eqS eqT eqvS eqvT bS bT sgpS sgpT,
{|
  sg_associative := bop_product_associative S T eqS eqT bS bT (sg_associative S eqS bS sgpS) (sg_associative T eqT bT sgpT)
; sg_congruence  := bop_product_congruence S T eqS eqT bS bT (sg_congruence S eqS bS sgpS) (sg_congruence T eqT bT sgpT)
; sg_commutative_d  := bop_product_commutative_decidable S T eqS eqT
                           (eqv_witness S eqS eqvS)
                           (eqv_witness T eqT eqvT) bS bT
                           (eqv_reflexive S eqS eqvS)
                           (sg_commutative_d S eqS bS sgpS)
                           (sg_commutative_d T eqT bT sgpT)                           
|}.

Definition sg_proofs_commutative_product :
  ∀ (S T : Type) (eqS : brel S) (eqT : brel T) (eqvS : eqv_proofs S eqS) (eqvT : eqv_proofs T eqT) (bS : binary_op S) (bT : binary_op T),
    (commutative_semigroup_proofs S eqS bS) -> (commutative_semigroup_proofs T eqT bT)
               -> commutative_semigroup_proofs (S * T) (brel_product eqS eqT )(bop_product bS bT) 
:= λ S T eqS eqT eqvS eqvT bS bT sgpS sgpT,
{|
  csg_associative := bop_product_associative S T eqS eqT bS bT (csg_associative S eqS bS sgpS) (csg_associative T eqT bT sgpT)
; csg_congruence  := bop_product_congruence S T eqS eqT bS bT (csg_congruence S eqS bS sgpS) (csg_congruence T eqT bT sgpT)
; csg_commutative := bop_product_commutative S T eqS eqT bS bT (csg_commutative S eqS bS sgpS) (csg_commutative T eqT bT sgpT)
|}.


(* simple semigroup combinators! *)

Definition semigroup_product : ∀ {S T : Type},  semigroup S -> semigroup T -> semigroup (S * T)
:= λ {S T} sgS sgT,
{|
   eq   := brel_product (eq S sgS) (eq T sgT) 
;  bop  := bop_product (bop S sgS) (bop T sgT) 
;  eqv  := eqv_proofs_product S T (eq S sgS) (eq T sgT) (eqv S sgS) (eqv T sgT) 
;  sgp  := sg_proofs_product S T (eq S sgS) (eq T sgT) (eqv S sgS) (eqv T sgT) (bop S sgS) (bop T sgT) (sgp S sgS) (sgp T sgT) 
|}.
  
Definition commutative_semigroup_product : ∀ {S T : Type},  commutative_semigroup S -> commutative_semigroup T -> commutative_semigroup (S * T)
:= λ {S T} sgS sgT,
{|
   ceq   := brel_product (ceq S sgS) (ceq T sgT) 
;  cbop  := bop_product (cbop S sgS) (cbop T sgT) 
;  ceqv  := eqv_proofs_product S T (ceq S sgS) (ceq T sgT) (ceqv S sgS) (ceqv T sgT) 
;  csgp  := sg_proofs_commutative_product S T (ceq S sgS) (ceq T sgT) (ceqv S sgS) (ceqv T sgT) (cbop S sgS) (cbop T sgT) (csgp S sgS) (csgp T sgT) 
|}.
  
End Product_Semigroup.

