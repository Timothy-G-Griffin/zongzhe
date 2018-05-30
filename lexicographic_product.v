Require Export Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.   
Require Import CAS.basic. 
Require Import CAS.properties. 
Require Import CAS.structures.
Require Import CAS.product.
Require Import CAS.facts.

Section LexicographicProduct.

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
  Variable bS_sel  : bop_selective S eqS bS.

  Variable bS_comm : bop_commutative S eqS bS.  

  Variable bT_cong : bop_congruence T eqT bT. 
  Variable bT_ass  : bop_associative T eqT bT.  


  (* maybe can't be proved 
  Lemma bop_lexicographic_product_congruence : bop_congruence (S * T) (brel_product eqS eqT) (bop_llex eqS bS bT).
  Proof. intros [s1 t1] [s2 t2] [s3 t3] [s4 t4]; simpl. intros H1 H2. 
         destruct (andb_elim _ _ H1) as [C1 C2].
         destruct (andb_elim _ _ H2) as [C3 C4].
         apply andb_intro. split.
         apply bS_cong; auto. 
         compute.
         case_eq (eqS s1 s2); intro A.
         case_eq (eqS s3 s4); intro B.
         assert (C := bT_cong t1 t2 t3 t4 C2 C4). exact C.
         assert (C := bS_sel s3 s4). destruct C.
         apply symS in e. rewrite e.
     Admitted.
*)

(* proofs come from L11 slides *)
Lemma bop_lexicographic_product_congruence : 
bop_associative S eqS bS ->
bop_commutative S eqS bS ->
bop_selective S eqS bS ->
bop_congruence S eqS bS ->
bop_congruence T eqT bT ->
bop_congruence (S * T) (brel_product eqS eqT) (bop_llex eqS bS bT).
Proof. 
Admitted.

Lemma bop_lexicographic_product_associative : 
bop_associative S eqS bS ->
bop_commutative S eqS bS ->
bop_selective S eqS bS ->
bop_associative T eqT bT ->
bop_associative (S * T) (brel_product eqS eqT) (bop_llex eqS bS bT). 
Proof. 
Admitted.     
   

Lemma bop_lexicographic_product_commutative : bop_commutative S eqS bS -> bop_commutative T eqT bT -> bop_commutative (S * T) (brel_product eqS eqT) (bop_llex eqS bS bT). 
Proof. intros Scomm Tcomm [s1 t1] [s2 t2] ; compute. 
       apply andb_intro. split.
       apply Scomm.
       case_eq (eqS s1 s2); intro A. apply symS in A. rewrite A. exact (Tcomm t1 t2).
       apply (brel_symmetric_false S eqS symS) in A. rewrite A.
       destruct (bS_sel s1 s2) as [B | B]; apply symS in B. rewrite B.
       assert (C := brel_transitive_f1 S eqS symS transS _ _ _ A B).
       assert (D := brel_transitive_f1 S eqS symS transS _ _ _ C (Scomm s1 s2)). rewrite D. auto.
       apply (brel_symmetric_false S eqS symS) in A.
       assert (C := brel_transitive_f1 S eqS symS transS _ _ _ A B). rewrite C.
       assert (D := transS _ _ _ B (Scomm s1 s2)). rewrite D. auto.
Qed. 

Lemma bop_lexicographic_product_selective : bop_selective S eqS bS -> bop_selective T eqT bT -> bop_selective (S * T) (brel_product eqS eqT) (bop_llex eqS bS bT).
Proof. intros selS selT [s1 t1] [s2 t2]. compute.
   destruct (selS s1 s2); rewrite e; case_eq (eqS s1 s2); intro A.
   assert (B := transS _ _ _ e A). rewrite B. exact (selT t1 t2).
   apply symS in e; rewrite e. apply symS in e.
   left. auto.
   apply symS in e.
   assert (B := transS _ _ _ A e). apply symS in B. rewrite B. exact (selT t1 t2).
   apply (brel_symmetric_false S eqS symS) in A.
   assert (B := brel_transitive_f2 S eqS symS transS _ _ _ e A).
   rewrite B.  apply (brel_symmetric_false S eqS symS) in B. rewrite B. right. auto.
Qed.


Lemma  bop_lexicographic_product_is_ann : ∀ (aS : S) (aT : T) (is_annS : bop_is_ann S eqS bS aS) (is_annS : bop_is_ann T eqT bT aT),  
       bop_is_ann (S * T) (brel_product eqS eqT) (bop_llex eqS bS bT) (aS, aT).
Proof. intros aS aT is_annS is_annT [s t]; compute. destruct (is_annS s) as [LS RS]. destruct (is_annT t) as [LT RT].
       rewrite LS, RS. apply symS in LS. rewrite LS.
       case_eq(eqS aS s); intro A; split;auto.
       apply symS in A.  rewrite A. rewrite RT. auto.
       apply (brel_symmetric_false S eqS symS) in A. rewrite A. apply symS in RS.
       assert (C := brel_transitive_f1 S eqS symS transS _ _ _ A RS). rewrite C. auto.
Qed.


Lemma  bop_lexicographic_product_is_id : ∀ (aS : S) (aT : T) (is_idS : bop_is_id S eqS bS aS) (is_idT : bop_is_id T eqT bT aT),  
       bop_is_id (S * T) (brel_product eqS eqT) (bop_llex eqS bS bT) (aS, aT).
       Proof. intros aS aT is_idS is_idT [s t]; compute. destruct (is_idS s) as [LS RS]. destruct (is_idT t) as [LT RT].
        rewrite LS, RS. apply symS in LS.
        case_eq (eqS aS s); intro A. split. auto.
        apply symS in A. rewrite A. auto.
        split. 
        assert (C := brel_transitive_f1 S eqS symS transS _ _ _ A LS). rewrite C. auto.
        apply (brel_symmetric_false S eqS symS) in A. rewrite A. apply symS in RS. rewrite RS. auto.
       Qed.


End LexicographicProduct.