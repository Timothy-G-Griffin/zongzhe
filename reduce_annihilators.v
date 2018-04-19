Require Export Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.   
Require Import CAS.basic. 
Require Import CAS.properties. 
Require Import CAS.structures.
Require Import CAS.facts.
Require Import CAS.reduction_theory.
Require Import CAS.product.
Require Import CAS.bop_full_reduce.
Require Import CAS.rsemigroup.


Section Reduce_Annihilators.

(* 
   Suppose that S as annihilator aS and T as annihilator aT. 
   Then this reduction treats all pairs (s, aT) and (aS, t) 
   as (aS, aT). 
 *)

Definition bop_reduce_annihilators {S T : Type} (aS : S) (aT : T) (eqS : brel S) (eqT : brel T) : unary_op (S * T)
  := λ p, let (s, t) := p in if orb (eqS s aS) (eqT t aT) then (aS, aT) else p.

Lemma bop_reduce_annihilators_idempotent (S T : Type) (aS : S) (aT : T) (eqS : brel S) (eqT : brel T) :
  brel_reflexive S eqS -> brel_reflexive T eqT -> 
  uop_idempotent (S * T) (brel_product eqS eqT) (bop_reduce_annihilators aS aT eqS eqT).
Proof. intros refS refT [s t].   compute. 
       case_eq (eqS s aS); intro Hs; case_eq (eqT t aT); intro Ht.
       rewrite refS. rewrite refT. rewrite refS. reflexivity.
       rewrite refS. rewrite refT. rewrite refS. reflexivity.
       rewrite refS. rewrite refT. rewrite refS. reflexivity.
       rewrite Hs. rewrite Ht. rewrite refS. rewrite refT. reflexivity.
Qed.

Lemma bop_reduce_annihilators_left_invariant
      (S T : Type)
      (aS : S)
      (aT : T)
      (eqS : brel S)
      (eqT : brel T)
      (bS : binary_op S)
      (bT : binary_op T)      
  :   brel_reflexive S eqS -> brel_reflexive T eqT -> 
    bop_is_ann S eqS bS aS ->
    bop_is_ann T eqT bT aT ->     
    bop_left_uop_invariant
      (S * T)
      (brel_product eqS eqT)
      (bop_full_reduce (bop_reduce_annihilators aS aT eqS eqT) (bop_product bS bT))
      (bop_reduce_annihilators aS aT eqS eqT).
Proof. intros refS refT AS AT [s1 t1] [s2 t2]. compute. compute in AS. compute in AT.
       destruct (AS s1) as [ASL1 ASR1].
       destruct (AS s2) as [ASL2 ASR2].
       destruct (AS aS) as [ASLaS ASRaS].       
       destruct (AT t1) as [ATL1 ATR1].
       destruct (AT t2) as [ATL2 ATR2].
       destruct (AT aT) as [ATLaT ATRaT].                      
       case_eq (eqS s1 aS); intro Hs1; case_eq (eqT t1 aT); intro Ht1;
       case_eq (eqS s2 aS); intro Hs2; case_eq (eqT t2 aT); intro Ht2.
       rewrite refS. rewrite refT. rewrite refS. rewrite ASLaS. rewrite refS. apply refT. 
       rewrite refS. rewrite refT. rewrite refS. rewrite ASLaS. rewrite refS. apply refT.
       rewrite refS. rewrite refT. rewrite refS. rewrite ASLaS. rewrite refS. apply refT.
       rewrite refS. rewrite refT. rewrite refS. rewrite ASL2. rewrite refS. apply refT.
       rewrite refS. rewrite refT. rewrite refS. rewrite ASLaS. rewrite refS. apply refT.
       rewrite refS. rewrite refT. rewrite refS. rewrite ASLaS. rewrite refS. apply refT.
       rewrite refS. rewrite refT. rewrite refS. rewrite ASLaS. rewrite refS. apply refT.
       rewrite refS. rewrite refT. rewrite refS. rewrite ASL2. rewrite refS. apply refT.
       rewrite refS. rewrite refT. rewrite refS. rewrite ASLaS. rewrite refS. apply refT.
       rewrite refS. rewrite refT. rewrite refS. rewrite ASLaS. rewrite refS. apply refT.
       rewrite refS. rewrite refT. rewrite refS. rewrite ASLaS. rewrite refS. apply refT.
       rewrite refS. rewrite refT. rewrite refS. rewrite ASL2. rewrite refS. apply refT.
       rewrite ASR1. rewrite Ht1. rewrite Hs1. rewrite ASR1. rewrite refS. apply refT.
       rewrite ASR1. rewrite Ht1. rewrite Hs1. rewrite ASR1. rewrite refS. apply refT.
       rewrite ASR1. rewrite Ht1. rewrite Hs1. rewrite ASR1. rewrite refS. apply refT.
       rewrite Ht1. rewrite Hs1.
       case_eq(eqS (bS s1 s2) aS); intro J1.
       rewrite refS. apply refT.
       case_eq(eqT (bT t1 t2) aT); intro J2.
       rewrite refS. apply refT.
       rewrite refS. apply refT.
Qed.


Lemma bop_reduce_annihilators_right_invariant
      (S T : Type)
      (aS : S)
      (aT : T)
      (eqS : brel S)
      (eqT : brel T)
      (bS : binary_op S)
      (bT : binary_op T)      
  :   brel_reflexive S eqS -> brel_reflexive T eqT -> 
    bop_is_ann S eqS bS aS ->
    bop_is_ann T eqT bT aT ->     
    bop_right_uop_invariant
      (S * T)
      (brel_product eqS eqT)
      (bop_full_reduce (bop_reduce_annihilators aS aT eqS eqT) (bop_product bS bT))
      (bop_reduce_annihilators aS aT eqS eqT).
Proof. intros refS refT AS AT [s1 t1] [s2 t2].  compute. compute in AS. compute in AT.
       destruct (AS s1) as [ASL1 ASR1].
       destruct (AS s2) as [ASL2 ASR2].
       destruct (AS aS) as [ASLaS ASRaS].       
       destruct (AT t1) as [ATL1 ATR1].
       destruct (AT t2) as [ATL2 ATR2].
       destruct (AT aT) as [ATLaT ATRaT].                      
       case_eq (eqS s1 aS); intro Hs1; case_eq (eqT t1 aT); intro Ht1;
       case_eq (eqS s2 aS); intro Hs2; case_eq (eqT t2 aT); intro Ht2.
       rewrite refS. rewrite refT. rewrite refS. rewrite ASLaS. rewrite refS. apply refT. 
       rewrite refS. rewrite refT. rewrite refS. rewrite ASLaS. rewrite refS. apply refT.
       rewrite refS. rewrite refT. rewrite refS. rewrite ASLaS. rewrite refS. apply refT.
       rewrite ASL2. rewrite Hs2. rewrite Ht2. rewrite ASL2. rewrite refS. apply refT.
       rewrite refS. rewrite refT. rewrite refS. rewrite ASLaS. rewrite refS. apply refT.
       rewrite refS. rewrite refT. rewrite refS. rewrite ASLaS. rewrite refS. apply refT.
       rewrite refS. rewrite refT. rewrite refS. rewrite ASLaS. rewrite refS. apply refT.
       rewrite Hs2. rewrite Ht2. rewrite ASL2. rewrite refS. apply refT.
       rewrite refS. rewrite refT. rewrite refS. rewrite ASLaS. rewrite refS. apply refT.
       rewrite refS. rewrite refT. rewrite refS. rewrite ASLaS. rewrite refS. apply refT.
       rewrite refS. rewrite refT. rewrite refS. rewrite ASLaS. rewrite refS. apply refT.
       rewrite Hs2. rewrite Ht2. rewrite ASL2. rewrite refS. apply refT.
       rewrite ASR1. rewrite refS. rewrite refS. rewrite ASR1. rewrite refS. apply refT.
       rewrite ASR1. rewrite refS. rewrite refS. rewrite ASR1. rewrite refS. apply refT.
       rewrite ASR1. rewrite refS. rewrite refS. rewrite ASR1. rewrite refS. apply refT.
       rewrite Hs2. rewrite Ht2.
       case_eq(eqS (bS s1 s2) aS); intro J1.
       rewrite refS. apply refT.
       case_eq(eqT (bT t1 t2) aT); intro J2.
       rewrite refS. apply refT.
       rewrite refS. apply refT.
Qed.

Lemma bop_reduce_annihilators_congruence (S T : Type) (aS : S) (aT : T) (eqS : brel S) (eqT : brel T) :
  brel_reflexive S eqS -> brel_symmetric S eqS -> brel_transitive S eqS -> 
  brel_reflexive T eqT -> brel_symmetric T eqT -> brel_transitive T eqT -> 
  uop_congruence (S * T) (brel_product eqS eqT) (bop_reduce_annihilators aS aT eqS eqT).
Proof. intros refS symS tranS refT symT tranT [s1 t1] [s2 t2].   compute. 
       case_eq (eqS s1 s2); intro Hs; case_eq (eqT t1 t2); intro Ht; intro H. 
       case_eq(eqS s1 aS); intro J1; case_eq(eqS s2 aS); intro J2.
          rewrite refS. rewrite refT.
          reflexivity.
          case_eq(eqT t2 aT); intro K1.
             rewrite refS. rewrite refT.
             reflexivity.
          apply symS in Hs. assert (F1 := tranS _ _ _ Hs J1).  rewrite F1 in J2. discriminate. 
          case_eq(eqT t1 aT); intro K1.
             rewrite refS. rewrite refT.
             reflexivity.
          assert (F1 := tranS _ _ _ Hs J2).  rewrite F1 in J1. discriminate. 
          case_eq(eqT t1 aT); intro K1; case_eq(eqT t2 aT); intro K2.
             rewrite refS. rewrite refT.
             reflexivity.
             apply symT in Ht. assert (F1 := tranT _ _ _ Ht K1).  rewrite F1 in K2. discriminate. 
             assert (F1 := tranT _ _ _ Ht K2).  rewrite F1 in K1. discriminate. 
          rewrite Hs. rewrite Ht.
          reflexivity.    
       discriminate.
       discriminate.
       discriminate.        
Qed.

Definition reduce_annihilators_reduction_eqv_proofs (S T : Type) (aS : S) (aT : T) (eqS : brel S) (eqT : brel T) :
  brel_reflexive S eqS -> brel_symmetric S eqS -> brel_transitive S eqS ->
  brel_reflexive T eqT -> brel_symmetric T eqT -> brel_transitive T eqT ->
         reduction_eqv_proofs (S * T) (brel_product eqS eqT) (bop_reduce_annihilators aS aT eqS eqT)
:= λ refS symS transS refT symT transT ,
{|
  rep_cong  := bop_reduce_annihilators_congruence S T aS aT eqS eqT refS symS transS refT symT transT 
; rep_idem  := bop_reduce_annihilators_idempotent S T aS aT eqS eqT refS refT 
|}.

Definition reduce_annihilators_reduction_bop_proofs (S T : Type) (eqS : brel S) (eqT : brel T)  (bS : binary_op S) (bT : binary_op T) 
    (aS : S) (aaS : bop_is_ann S eqS bS aS)
    (aT : T) (aaT : bop_is_ann T eqT bT aT) : 
    brel_reflexive S eqS ->   brel_reflexive T eqT ->   
    reduction_bop_proofs (S * T)
                         (brel_product eqS eqT)
                         (bop_reduce_annihilators aS aT eqS eqT)
                         (bop_full_reduce (bop_reduce_annihilators aS aT eqS eqT) (bop_product bS bT))
:= λ refS refT,
{|
  rb_left  := bop_reduce_annihilators_left_invariant S T aS aT eqS eqT bS bT refS refT aaS aaT 
; rb_right := bop_reduce_annihilators_right_invariant S T aS aT eqS eqT bS bT refS refT aaS aaT 
|}.


Lemma bop_reduce_annihilators_psedo_associative 
(S T : Type)
      (aS : S)
      (aT : T)
      (eqS : brel S)
      (eqT : brel T)
      (bS : binary_op S)
      (bT : binary_op T): 
      brel_reflexive S eqS -> brel_reflexive T eqT ->
      brel_symmetric S eqS -> brel_symmetric T eqT ->
      brel_transitive S eqS -> brel_transitive T eqT -> 
      bop_associative S eqS bS ->
      bop_associative T eqT bT -> 
      bop_congruence S eqS bS ->
      bop_congruence T eqT bT -> 
      bop_is_ann S eqS bS aS ->
      bop_is_ann T eqT bT aT ->
      bop_pseudo_associative (S * T) (brel_product eqS eqT) (bop_reduce_annihilators aS aT eqS eqT) (bop_product bS bT) .
Proof. compute. intros refS refT symS symT tranS tranT assS assT congS congT annS annT s t u . destruct s as [s1 t1], t as [s2 t2], u as [s3 t3].
       case_eq (eqS s1 aS); intro J;case_eq (eqS s2 aS); intro K.
       assert (M := annS aS). destruct M as [M _]; rewrite M.
       case_eq(eqS s3 aS); intro L. rewrite M. rewrite M. rewrite (refS aS), (refT aT). auto.
       case_eq(eqT t3 aT); intro H. rewrite M. rewrite M. rewrite (refS aS), (refT aT). auto.
       assert (N := annS s3). destruct N as [Nl Nr]; rewrite Nl. rewrite M. rewrite (refS aS), (refT aT). auto.
       case_eq (eqT t2 aT);intro L. assert (M := annS aS). destruct M as [M _]; rewrite M.
       case_eq (eqS s3 aS); intro O. rewrite M. rewrite M. rewrite (refS aS), (refT aT). auto.
       case_eq (eqT t3 aT); intro P. rewrite M. rewrite M. rewrite (refS aS), (refT aT). auto.
       assert (N := annS s3). destruct N as [Nl Nr]; rewrite Nl. rewrite M. rewrite (refS aS), (refT aT). auto.
       assert (N := annS s2). destruct N as [Nl Nr]; rewrite Nl. 
       case_eq (eqS s3 aS); intro O. assert (M := annS aS). destruct M as [M _]; rewrite M. rewrite Nr. rewrite M. rewrite (refS aS), (refT aT). auto.
       case_eq (eqT t3 aT); intro P. assert (M := annS aS). destruct M as [M _]; rewrite M. rewrite Nr. rewrite M. rewrite (refS aS), (refT aT). auto.
       assert (N' := annS s3). destruct N' as [Nl' Nr']; rewrite Nl'. 
       case_eq (eqS (bS s2 s3) aS); intro Q. assert (M := annS aS). destruct M as [M _]; rewrite M.  rewrite (refS aS), (refT aT). auto.
       case_eq (eqT (bT t2 t3) aT); intro R. assert (M := annS aS). destruct M as [M _]; rewrite M.  rewrite (refS aS), (refT aT). auto.
       assert (I := annS (bS s2 s3)). destruct I as [Il Ir]. rewrite Il. rewrite (refS aS), (refT aT). auto.
       assert (M := annS aS). destruct M as [M _].
       case_eq (eqT t1 aT); intro L. rewrite M. 
       case_eq (eqS s3 aS); intro O. rewrite M. rewrite M. rewrite (refS aS), (refT aT). auto.
       case_eq (eqT t3 aT); intro P. rewrite M. rewrite M. rewrite (refS aS), (refT aT). auto.
       assert (N := annS s3). destruct N as [Nl Nr]; rewrite Nl. rewrite M. rewrite (refS aS), (refT aT). auto.
       assert (N := annS s1). destruct N as [Nl Nr]; rewrite Nr.
       case_eq (eqS s3 aS); intro O. rewrite M. rewrite Nr. rewrite (refS aS), (refT aT). auto.
       case_eq (eqT t3 aT); intro P. rewrite M. rewrite Nr. rewrite (refS aS), (refT aT). auto.
       assert (N' := annS s3). destruct N' as [Nl' Nr']; rewrite Nl'. rewrite Nr.  rewrite (refS aS), (refT aT). auto.
       assert (M := annS aS). destruct M as [M _].
       case_eq (eqT t1 aT); intro L.
       case_eq (eqS s3 aS); intro O.
       case_eq (eqT t2 aT); intro P. rewrite M. rewrite M. rewrite (refS aS), (refT aT). auto.
       assert (N := annS s2). destruct N as [Nl Nr]; rewrite Nl. rewrite M. rewrite Nr. rewrite M. rewrite (refS aS), (refT aT). auto.
       case_eq (eqT t2 aT ); intro P. rewrite M.
       case_eq (eqT t3 aT); intro Q. rewrite M. rewrite M. rewrite (refS aS), (refT aT). auto.
       assert (N := annS s3). destruct N as [Nl Nr]; rewrite Nl. rewrite M. rewrite (refS aS), (refT aT). auto.
       assert (N := annS s2). destruct N as [Nl Nr]; rewrite Nl.
       case_eq (eqT t3 aT); intro Q. rewrite M. rewrite Nr. rewrite M. rewrite (refS aS), (refT aT). auto.
       assert (N' := annS s3). destruct N' as [Nl' Nr']; rewrite Nl'. 
       case_eq (eqS (bS s2 s3) aS); intro R. rewrite M. rewrite (refS aS), (refT aT). auto.
       case_eq (eqT (bT t2 t3) aT); intro U. rewrite M. rewrite (refS aS), (refT aT). auto.
       assert (I := annS (bS s2 s3)). destruct I as [Il Ir]. rewrite Il. rewrite (refS aS), (refT aT). auto.
       case_eq (eqT t2 aT); intro P.
       assert (N := annS s1). destruct N as [Nl Nr]; rewrite Nr.
       case_eq (eqS s3 aS); intro O. rewrite M. rewrite Nr. rewrite (refS aS), (refT aT). auto.
       case_eq (eqT t3 aT); intro Q. rewrite M. rewrite Nr. rewrite (refS aS), (refT aT). auto.
       assert (N' := annS s3). destruct N' as [Nl' Nr']; rewrite Nl'. rewrite Nr.  rewrite (refS aS), (refT aT). auto.
       case_eq (eqS (bS s1 s2) aS); intro Q. case_eq (eqS s3 aS); intro R. rewrite M. 
       assert (N := annS s2). destruct N as [Nl Nr]; rewrite Nr. 
       assert (N' := annS s1). destruct N' as [Nl' Nr']; rewrite Nr'. rewrite (refS aS), (refT aT). auto.
       case_eq (eqT t3 aT); intro U. rewrite M. assert (N := annS s2). destruct N as [Nl Nr]; rewrite Nr.
       assert (N' := annS s1). destruct N' as [Nl' Nr']; rewrite Nr'. rewrite (refS aS), (refT aT). auto.
       assert (N := annS s3). destruct N as [Nl Nr]; rewrite Nl. 
       case_eq (eqS (bS s2 s3) aS); intro V. 
       assert (N' := annS s1). destruct N' as [Nl' Nr']; rewrite Nr'. rewrite (refS aS), (refT aT). auto.
       case_eq (eqT (bT t2 t3) aT); intro W. 
       assert (N' := annS s1). destruct N' as [Nl' Nr']; rewrite Nr'. rewrite (refS aS), (refT aT). auto.
       assert (A := assS s1 s2 s3).
       assert (B := congS (bS s1 s2) s3 aS s3 Q (refS s3)).
       assert (C := tranS _ _ _ B Nl). apply symS in A.
       assert (D := tranS _ _ _ A C). rewrite D. rewrite (refS aS), (refT aT). auto.
       case_eq (eqT (bT t1 t2) aT); intro O; case_eq (eqS s3 aS); intro R. 
       rewrite M. assert (N' := annS s2). destruct N' as [Nl' Nr']; rewrite Nr'.  
       assert (N := annS s1). destruct N as [Nl Nr]; rewrite Nr.  rewrite (refS aS), (refT aT). auto.
       case_eq (eqT t3 aT); intro U. rewrite M. assert (N' := annS s2). destruct N' as [Nl' Nr']; rewrite Nr'.  
       assert (N := annS s1). destruct N as [Nl Nr]; rewrite Nr.  rewrite (refS aS), (refT aT). auto.
       assert (N := annS s3). destruct N as [Nl Nr]; rewrite Nl.  
       case_eq (eqS (bS s2 s3) aS); intro V. assert (N' := annS s1). destruct N' as [Nl' Nr']; rewrite Nr'. rewrite (refS aS), (refT aT). auto.
       case_eq (eqT (bT t2 t3) aT); intro W. assert (N' := annS s1). destruct N' as [Nl' Nr']; rewrite Nr'. rewrite (refS aS), (refT aT). auto.
       case_eq (eqS (bS s1 (bS s2 s3)) aS); intro X. rewrite (refS aS), (refT aT). auto.
       assert (A := assT t1 t2 t3).
       assert (B := congT (bT t1 t2) t3 aT t3 O (refT t3)).
       assert (N' := annT t3). destruct N' as [Nl' Nr'].
       assert (C := tranT _ _ _ B Nl'). apply symT in A.
       assert (D := tranT _ _ _ A C). rewrite D. rewrite (refS aS), (refT aT). auto.
       assert (I := annS (bS s1 s2)). destruct I as [Il Ir]. rewrite Ir. 
       assert (N' := annS s2). destruct N' as [Nl' Nr']; rewrite Nr'.
       assert (N := annS s1). destruct N as [Nl Nr]; rewrite Nr.  rewrite (refS aS), (refT aT). auto.
       case_eq (eqT t3 aT); intro U.
       assert (I := annS (bS s1 s2)). destruct I as [Il Ir]. rewrite Ir. 
       assert (N' := annS s2). destruct N' as [Nl' Nr']; rewrite Nr'.
       assert (N := annS s1). destruct N as [Nl Nr]; rewrite Nr.  rewrite (refS aS), (refT aT). auto.
       case_eq (eqS (bS (bS s1 s2) s3) aS); intro V. 
       case_eq (eqS (bS s2 s3) aS); intro W. assert (N := annS s1). destruct N as [Nl Nr]; rewrite Nr.  rewrite (refS aS), (refT aT). auto.
       case_eq (eqT (bT t2 t3) aT); intro X. assert (N := annS s1). destruct N as [Nl Nr]; rewrite Nr.  rewrite (refS aS), (refT aT). auto.
       assert (A := assS s1 s2 s3). apply symS in A.
       assert (B := tranS _ _ _ A V). rewrite B. rewrite (refS aS), (refT aT). auto.
       case_eq (eqT (bT (bT t1 t2) t3) aT); intro W. 
       case_eq (eqS (bS s2 s3) aS); intro X. assert (N := annS s1). destruct N as [Nl Nr]; rewrite Nr.  rewrite (refS aS), (refT aT). auto.
       case_eq (eqT (bT t2 t3) aT); intro Y. assert (N := annS s1). destruct N as [Nl Nr]; rewrite Nr.  rewrite (refS aS), (refT aT). auto.
       assert (A := assS s1 s2 s3). apply symS in A.
       assert (B := brel_transitive_f2 S eqS symS tranS _ _ _ A V). rewrite B.
       assert (C := assT t1 t2 t3). apply symT in C.
       assert (D := tranT _ _ _ C W). rewrite D. rewrite (refS aS), (refT aT). auto.
       case_eq (eqS (bS s2 s3) aS ); intro X. 
       assert (A := assS s1 s2 s3).
       assert (B := congS s1 (bS s2 s3) s1 aS (refS s1) X).
       assert (C := tranS _ _ _ A B). assert (N := annS s1). destruct N as [Nl Nr].
       assert (D := tranS _ _ _ C Nr). rewrite D in V. discriminate.
       case_eq (eqT (bT t2 t3) aT); intro Y.
       assert (A := assT t1 t2 t3).
       assert (B := congT t1 (bT t2 t3) t1 aT (refT t1) Y).
       assert (C := tranT _ _ _ A B). assert (N := annT t1). destruct N as [Nl Nr].
       assert (D := tranT _ _ _ C Nr). rewrite D in W. discriminate.
       assert (A := assS s1 s2 s3). apply symS in A.
       assert (B := brel_transitive_f2 S eqS symS tranS _ _ _ A V). rewrite B.
       assert (C := assT t1 t2 t3). apply symT in C.
       assert (D := brel_transitive_f2 T eqT symT tranT _ _ _ C W). rewrite D.
       apply symS in A. rewrite A. apply symT in C. rewrite C. auto.
Qed.

Lemma bop_reduce_annihilators_associative_v2 
(S T : Type)
(aS : S)
(aT : T)
(eqS : brel S)
(eqT : brel T)
(bS : binary_op S)
(bT : binary_op T)  
: brel_reflexive S eqS -> brel_reflexive T eqT ->
brel_symmetric S eqS -> brel_symmetric T eqT ->
brel_transitive S eqS -> brel_transitive T eqT -> 
bop_associative S eqS bS ->
bop_associative T eqT bT -> 
bop_congruence S eqS bS ->
bop_congruence T eqT bT -> 
bop_is_ann S eqS bS aS ->
bop_is_ann T eqT bT aT ->
bop_associative (S * T) (brel_reduce (bop_reduce_annihilators aS aT eqS eqT) (brel_product eqS eqT)) (bop_full_reduce (bop_reduce_annihilators aS aT eqS eqT) (bop_product bS bT)).
Proof. intros refS refT symS symT tranS tranT assS assT congS congT annS annT. 
  apply bop_full_reduce_pseudo_associative_implies_associative.
  apply brel_product_reflexive. auto. auto.
  apply brel_product_symmetric; auto; auto.
  apply brel_product_transitive ; auto;auto.
  compute. intro a. destruct a as [s t]. 
  case_eq (eqS s aS); intro A. rewrite (refS aS). rewrite (refS aS), (refT aT). auto.
  case_eq (eqT t aT); intro B. rewrite (refS aS). rewrite (refS aS), (refT aT). auto.
  rewrite A. rewrite B. rewrite (refS s), (refT t). auto.
  compute. intros [s1 t1] [s2 t2] H.  
  case_eq (eqS s1 aS); intro A.
  case_eq (eqS s2 aS); intro B. rewrite (refS aS), (refT aT). auto.
  case_eq (eqT t2 aT); intro C.  rewrite (refS aS), (refT aT). auto.
  case_eq (eqS s1 s2); intro D; rewrite D in H. apply symS in A.
  assert (E := brel_transitive_f1 S eqS symS tranS _ _ _ B A). apply symS in D. rewrite D in E. discriminate. discriminate.
  case_eq (eqT t1 aT); intro B; case_eq(eqS s2 aS); intro C. rewrite (refS aS), (refT aT). auto.
  case_eq (eqT t2 aT); intro D. rewrite (refS aS), (refT aT). auto.
  case_eq (eqS s1 s2); intro E; rewrite E in H. apply symT in B.
  assert (F := brel_transitive_f1 T eqT symT tranT _ _ _ D B). assert (L := brel_symmetric_false T eqT symT _ _ F).  rewrite L in H. discriminate. discriminate.
  case_eq (eqS s1 s2); intro D; rewrite D in H.  apply symS in C.
  assert (E := brel_transitive_f1 S eqS symS tranS _ _ _ A C). rewrite E in D. discriminate. discriminate.
  case_eq (eqT t2 aT); intro D. 
  case_eq (eqS s1 s2); intro E; rewrite E in H.  apply symT in D.
  assert (F := brel_transitive_f1 T eqT symT tranT _ _ _ B D). rewrite F in H.  discriminate. discriminate.
  case_eq (eqS s1 s2); intro F; rewrite F in H. auto. discriminate.
  apply bop_product_congruence; auto;auto.
  apply bop_reduce_annihilators_psedo_associative; auto;auto; auto;auto; auto;auto; auto;auto; auto;auto; auto;auto.
Qed.

Lemma bop_reduce_annihilators_associative
      (S T : Type)
      (aS : S)
      (aT : T)
      (eqS : brel S)
      (eqT : brel T)
      (bS : binary_op S)
      (bT : binary_op T)      
  :   brel_reflexive S eqS -> brel_reflexive T eqT ->
      brel_symmetric S eqS -> brel_symmetric T eqT ->
      brel_transitive S eqS -> brel_transitive T eqT ->       
    bop_is_ann S eqS bS aS ->
    bop_is_ann T eqT bT aT ->
    bop_congruence S eqS bS ->
    bop_congruence T eqT bT ->     
    bop_associative S eqS bS ->
    bop_associative T eqT bT ->     
    bop_associative 
      (S * T)
      (brel_product eqS eqT)
      (bop_full_reduce (bop_reduce_annihilators aS aT eqS eqT) (bop_product bS bT)). 
Proof. intros refS refT symS symT transS transT AS AT congS congT assS assT [s1 t1] [s2 t2] [s3 t3].  compute. compute in AS. compute in AT.
       destruct (AS s1) as [ASL1 ASR1].
       destruct (AS s2) as [ASL2 ASR2].
       destruct (AS s3) as [ASL3 ASR3].
       destruct (AT t1) as [ATL1 ATR1].
       destruct (AT t2) as [ATL2 ATR2].  
       destruct (AT t3) as [ATL3 ATR3].     
       destruct (AS aS) as [ASLaS ASRaS].
       destruct (AT aT) as [ATLaT ATRaT].
       destruct (AS (bS s2 s3)) as [ASL4 ASR4].         
       destruct (AT (bT t2 t3)) as [ATL4 ATR4].
       destruct (AS (bS s1 s2)) as [ASL5 ASR5].         
       destruct (AT (bT t1 t1)) as [ATL5 ATR5].                
       case_eq (eqS s1 aS); intro Hs1; case_eq (eqT t1 aT); intro Ht1;
       case_eq (eqS s2 aS); intro Hs2; case_eq (eqT t2 aT); intro Ht2;
       case_eq (eqS s3 aS); intro Hs3; case_eq (eqT t3 aT); intro Ht3;                                                                  
         repeat (
             try (rewrite ASL1); try (rewrite ASR1);
             try (rewrite ASL2); try (rewrite ASR2);
             try (rewrite ASL3); try (rewrite ASR3);
             try (rewrite ATL1); try (rewrite ATR1);
             try (rewrite ATL2); try (rewrite ATR2);
             try (rewrite ATL3); try (rewrite ATR3);             
             try (rewrite ASLaS); try (rewrite ASRaS);
             try (rewrite ASLaT); try (rewrite ASRaT);
             try (rewrite refS); try (rewrite refT);
             try auto
           ).
       case_eq(eqS (bS s2 s3) aS); intro K1; case_eq (eqT (bT t2 t3) aT); intro K2;  
        repeat (
             try (rewrite ASL1); try (rewrite ASR1);
             try (rewrite ASL2); try (rewrite ASR2);
             try (rewrite ASL3); try (rewrite ASR3);
             try (rewrite ASL4); try (rewrite ASR4);             
             try (rewrite ATL1); try (rewrite ATR1);
             try (rewrite ATL2); try (rewrite ATR2);
             try (rewrite ATL3); try (rewrite ATR3);             
             try (rewrite ASLaS); try (rewrite ASRaS); 
             try (rewrite ASLaT); try (rewrite ASRaT);
             try (rewrite refS); try (rewrite refT);
             try (rewrite K1); try (rewrite K2);             
             try auto
          ).
       case_eq(eqS (bS s2 s3) aS); intro K1; case_eq (eqT (bT t2 t3) aT); intro K2;  
        repeat (
             try (rewrite ASL1); try (rewrite ASR1);
             try (rewrite ASL2); try (rewrite ASR2);
             try (rewrite ASL3); try (rewrite ASR3);
             try (rewrite ASL4); try (rewrite ASR4);             
             try (rewrite ATL1); try (rewrite ATR1);
             try (rewrite ATL2); try (rewrite ATR2);
             try (rewrite ATL3); try (rewrite ATR3);
             try (rewrite ATL4); try (rewrite ATR4);                          
             try (rewrite ASLaS); try (rewrite ASRaS); 
             try (rewrite ASLaT); try (rewrite ASRaT);
             try (rewrite refS); try (rewrite refT);
             try (rewrite K1); try (rewrite K2);             
             try auto
           ). 

       case_eq(eqS (bS s2 s3) aS); intro K1; case_eq (eqT (bT t2 t3) aT); intro K2;  
        repeat (
             try (rewrite ASL1); try (rewrite ASR1);
             try (rewrite ASL2); try (rewrite ASR2);
             try (rewrite ASL3); try (rewrite ASR3);
             try (rewrite ASL4); try (rewrite ASR4);             
             try (rewrite ATL1); try (rewrite ATR1);
             try (rewrite ATL2); try (rewrite ATR2);
             try (rewrite ATL3); try (rewrite ATR3);
             try (rewrite ATL4); try (rewrite ATR4);                          
             try (rewrite ASLaS); try (rewrite ASRaS); 
             try (rewrite ASLaT); try (rewrite ASRaT);
             try (rewrite refS); try (rewrite refT);
             try (rewrite K1); try (rewrite K2);             
             try auto
           ). 

       case_eq(eqS (bS s1 s2) aS); intro K1; case_eq (eqT (bT t1 t2) aT); intro K2;  
        repeat (
             try (rewrite ASL1); try (rewrite ASR1);
             try (rewrite ASL2); try (rewrite ASR2);
             try (rewrite ASL3); try (rewrite ASR3);
             try (rewrite ASL5); try (rewrite ASR5);             
             try (rewrite ATL1); try (rewrite ATR1);
             try (rewrite ATL2); try (rewrite ATR2);
             try (rewrite ATL3); try (rewrite ATR3);
             try (rewrite ATL5); try (rewrite ATR5);                          
             try (rewrite ASLaS); try (rewrite ASRaS); 
             try (rewrite ASLaT); try (rewrite ASRaT);
             try (rewrite refS); try (rewrite refT);
             try (rewrite K1); try (rewrite K2);             
             try auto
           ). 
       case_eq(eqS (bS s1 s2) aS); intro K1; case_eq (eqT (bT t1 t2) aT); intro K2;  
        repeat (
             try (rewrite ASL1); try (rewrite ASR1);
             try (rewrite ASL2); try (rewrite ASR2);
             try (rewrite ASL3); try (rewrite ASR3);
             try (rewrite ASL5); try (rewrite ASR5);             
             try (rewrite ATL1); try (rewrite ATR1);
             try (rewrite ATL2); try (rewrite ATR2);
             try (rewrite ATL3); try (rewrite ATR3);
             try (rewrite ATL5); try (rewrite ATR5);                          
             try (rewrite ASLaS); try (rewrite ASRaS); 
             try (rewrite ASLaT); try (rewrite ASRaT);
             try (rewrite refS); try (rewrite refT);
             try (rewrite K1); try (rewrite K2);             
             try auto
           ). 
       case_eq(eqS (bS s1 s2) aS); intro K1; case_eq (eqT (bT t1 t2) aT); intro K2;  
        repeat (
             try (rewrite ASL1); try (rewrite ASR1);
             try (rewrite ASL2); try (rewrite ASR2);
             try (rewrite ASL3); try (rewrite ASR3);
             try (rewrite ASL5); try (rewrite ASR5);             
             try (rewrite ATL1); try (rewrite ATR1);
             try (rewrite ATL2); try (rewrite ATR2);
             try (rewrite ATL3); try (rewrite ATR3);
             try (rewrite ATL5); try (rewrite ATR5);                          
             try (rewrite ASLaS); try (rewrite ASRaS); 
             try (rewrite ASLaT); try (rewrite ASRaT);
             try (rewrite refS); try (rewrite refT);
             try (rewrite K1); try (rewrite K2);             
             try auto
           ). 

       case_eq(eqS (bS s1 s2) aS); intro K1;         case_eq(eqS (bS s2 s3) aS); intro K2;
       case_eq (eqT (bT t1 t2) aT); intro K3;        case_eq (eqT (bT t2 t3) aT); intro K4;
        repeat (
             try (rewrite ASL1); try (rewrite ASR1);
             try (rewrite ASL2); try (rewrite ASR2);
             try (rewrite ASL3); try (rewrite ASR3);
             try (rewrite ASL4); try (rewrite ASR4);                          
             try (rewrite ASL5); try (rewrite ASR5);             
             try (rewrite ATL1); try (rewrite ATR1);
             try (rewrite ATL2); try (rewrite ATR2);
             try (rewrite ATL3); try (rewrite ATR3);
             try (rewrite ATL5); try (rewrite ATR5);
             try (rewrite ATL4); try (rewrite ATR4);                                       
             try (rewrite ASLaS); try (rewrite ASRaS); 
             try (rewrite ASLaT); try (rewrite ASRaT);
             try (rewrite refS); try (rewrite refT);
             try (rewrite K1); try (rewrite K2);
             try (rewrite K3); try (rewrite K4);
             try auto
           ). 

       case_eq(eqS (bS s1 (bS s2 s3)) aS); intro K5.
          rewrite refS. rewrite refT; auto.
          case_eq(eqT (bT t1 (bT t2 t3)) aT); intro K6.
             rewrite refS; rewrite refT; auto.
             assert (K7 := assS s1 s2 s3).
             assert (K8 : eqS (bS (bS s1 s2) s3) aS = true).
                assert(K9 := congS _ _ _ _ K1 (refS s3)).
                assert(K10 := transS _ _ _ K9 ASL3).  
                exact K10.
            apply symS in K7. assert(K9 := transS _ _ _ K7 K8). 
            rewrite K9 in K5.
            discriminate. 

       case_eq(eqS (bS s1 (bS s2 s3)) aS); intro K5.
          rewrite refS. rewrite refT; auto.
          case_eq(eqT (bT t1 (bT t2 t3)) aT); intro K6.
             rewrite refS; rewrite refT; auto.
            assert (K7 := assS s1 s2 s3).
            assert (K8 : eqS (bS (bS s1 s2) s3) aS = true).
                assert(K9 := congS _ _ _ _ K1 (refS s3)).
                assert(K10 := transS _ _ _ K9 ASL3).  
                exact K10.
             apply symS in K7. assert(K9 := transS _ _ _ K7 K8).
            rewrite K9 in K5.
            discriminate. 
             
       case_eq(eqS (bS (bS s1 s2) s3) aS); intro K5.
          rewrite refS. rewrite refT; auto.
          case_eq(eqT (bT (bT t1 t2) t3) aT); intro K6.
             rewrite refS; rewrite refT; auto.
            assert (K7 := assS s1 s2 s3).
            assert (K8 : eqS (bS (bS s1 s2) s3) aS = true).
                assert(K9 := congS _ _ _ _ (refS s1) K2).
                assert(K10 := transS _ _ _ K9 ASR1).
                assert(K11 := transS _ _ _ K7 K10).  
                exact K11.
            rewrite K8 in K5.
            discriminate.

       case_eq(eqS (bS (bS s1 s2) s3) aS); intro K5.
          rewrite refS. rewrite refT; auto.
          case_eq(eqT (bT (bT t1 t2) t3) aT); intro K6.
             rewrite refS; rewrite refT; auto.
             assert (K7 := assS s1 s2 s3).
            assert (K8 : eqS (bS (bS s1 s2) s3) aS = true).
                assert(K9 := congS _ _ _ _ (refS s1) K2).
                assert(K10 := transS _ _ _ K9 ASR1).
                assert(K11 := transS _ _ _ K7 K10).  
                exact K11.
            rewrite K8 in K5.
            discriminate.

       case_eq(eqS (bS s1 (bS s2 s3)) aS); intro K5.
          rewrite refS. rewrite refT; auto.
          case_eq(eqT (bT t1 (bT t2 t3)) aT); intro K6.
             rewrite refS; rewrite refT; auto.
             assert (K7 := assT t1 t2 t3).
             assert (K8 : eqT (bT t1 (bT t2 t3)) aT = true).
                    assert(K9 := congT _ _ _ _ K3 (refT t3)).
                    assert(K10 := transT _ _ _ K9 ATL3). apply symT in K7.
                    assert(K11 := transT _ _ _ K7 K10).
                    exact K11.
            rewrite K8 in K6.
            discriminate.

        case_eq(eqS (bS (bS s1 s2) s3) aS); intro K5.
          rewrite refS. rewrite refT; auto.
          case_eq(eqT (bT (bT t1 t2) t3) aT); intro K6.
             rewrite refS; rewrite refT; auto.
            assert (K7 := assT t1 t2 t3).
            assert (K8 : eqT (bT (bT t1 t2) t3) aT = true).
                assert(K9 := congT _ _ _ _ (refT t1) K4).
                assert(K10 := transT _ _ _ K9 ATR1).
                assert(K11 := transT _ _ _ K7 K10).
                exact K11.
            rewrite K8 in K6.
            discriminate.

       case_eq(eqS (bS (bS s1 s2) s3) aS); intro K5.
          assert(K6 := assS s1 s2 s3). apply symS in K6.
          assert(K7 := transS _ _ _ K6 K5). rewrite K7.
          rewrite refS; rewrite refT; auto.
          case_eq(eqT (bT (bT t1 t2) t3) aT ); intro K6.
             assert(K7 := assS s1 s2 s3). apply symS in K7.  
             assert(K8 := brel_transitive_f2 S eqS symS transS _ _ _ K7 K5).  rewrite K8.
             assert(K9 := assT t1 t2 t3). apply symT in K9.
             assert(K10 := transT _ _ _ K9 K6). rewrite K10.
             rewrite refS; rewrite refT; auto.
             assert(K7 := assS s1 s2 s3). apply symS in K7.  
             assert(K8 := brel_transitive_f2 S eqS symS transS _ _ _ K7 K5).  rewrite K8.
             assert(K9 := assT t1 t2 t3). apply symT in K9.
             assert(K10 := brel_transitive_f2 T eqT symT transT  _ _ _ K9 K6). rewrite K10.
             apply symS in K7. rewrite K7. apply symT in K9. exact K9.
Qed.


Lemma bop_reduce_annihilators_commutative_v2 
(S T : Type)
      (aS : S)
      (aT : T)
      (eqS : brel S)
      (eqT : brel T)
      (bS : binary_op S)
      (bT : binary_op T)      
  :   brel_reflexive S eqS -> brel_reflexive T eqT ->
      bop_commutative S eqS bS -> bop_commutative T eqT bT ->
      brel_symmetric S eqS -> brel_symmetric T eqT ->
     brel_transitive S eqS -> brel_transitive T eqT ->
    bop_is_ann S eqS bS aS ->
    bop_is_ann T eqT bT aT ->
bop_commutative (S * T) (brel_reduce (bop_reduce_annihilators aS aT eqS eqT) (brel_product eqS eqT)) (bop_full_reduce (bop_reduce_annihilators aS aT eqS eqT) (bop_product bS bT)).
Proof. intros refS refT comS comT symS symT tranS tranT AS AT [a b] [c d]. 
       apply bop_full_reduce_commutative. 
       compute. intros [s1 t1] [s2 t2] H.  
       case_eq (eqS s1 aS); intro A.
       case_eq (eqS s2 aS); intro B. rewrite (refS aS), (refT aT). auto.
       case_eq (eqT t2 aT); intro C.  rewrite (refS aS), (refT aT). auto.
       case_eq (eqS s1 s2); intro D; rewrite D in H. apply symS in A.
       assert (E := brel_transitive_f1 S eqS symS tranS _ _ _ B A). apply symS in D. rewrite D in E. discriminate. discriminate.
       case_eq (eqT t1 aT); intro B; case_eq(eqS s2 aS); intro C. rewrite (refS aS), (refT aT). auto.
       case_eq (eqT t2 aT); intro D. rewrite (refS aS), (refT aT). auto.
       case_eq (eqS s1 s2); intro E; rewrite E in H. apply symT in B.
       assert (F := brel_transitive_f1 T eqT symT tranT _ _ _ D B). assert (L := brel_symmetric_false T eqT symT _ _ F).  rewrite L in H. discriminate. discriminate.
       case_eq (eqS s1 s2); intro D; rewrite D in H.  apply symS in C.
       assert (E := brel_transitive_f1 S eqS symS tranS _ _ _ A C). rewrite E in D. discriminate. discriminate.
       case_eq (eqT t2 aT); intro D. 
       case_eq (eqS s1 s2); intro E; rewrite E in H.  apply symT in D.
       assert (F := brel_transitive_f1 T eqT symT tranT _ _ _ B D). rewrite F in H.  discriminate. discriminate.
       case_eq (eqS s1 s2); intro F; rewrite F in H. auto. discriminate.
       apply bop_product_commutative; auto;auto.
Qed.

Lemma bop_reduce_annihilators_commutative
      (S T : Type)
      (aS : S)
      (aT : T)
      (eqS : brel S)
      (eqT : brel T)
      (bS : binary_op S)
      (bT : binary_op T)      
  :   brel_reflexive S eqS -> brel_reflexive T eqT ->
      bop_commutative S eqS bS -> bop_commutative T eqT bT ->
      brel_symmetric S eqS -> brel_symmetric T eqT ->
     brel_transitive S eqS -> brel_transitive T eqT ->
    bop_is_ann S eqS bS aS ->
    bop_is_ann T eqT bT aT ->
    bop_commutative 
      (S * T)
      (brel_product eqS eqT)
      (bop_full_reduce (bop_reduce_annihilators aS aT eqS eqT) (bop_product bS bT)). 
Proof. intros refS refT comS comT symS symT transS transT AS AT [s1 t1] [s2 t2]. compute.
destruct (AS s1) as [ASL1 ASR1].
       destruct (AS s2) as [ASL2 ASR2].
       destruct (AS aS) as [ASLaS ASRaS].       
       destruct (AT t1) as [ATL1 ATR1].
       destruct (AT t2) as [ATL2 ATR2].
       destruct (AT aT) as [ATLaT ATRaT].
       case_eq (eqS s1 aS); intro Hs1; case_eq (eqT t1 aT); intro Ht1;
       case_eq (eqS s2 aS); intro Hs2; case_eq (eqT t2 aT); intro Ht2;    
        try (rewrite ASL1); try (rewrite ASR1);
             try (rewrite ASL2); try (rewrite ASR2);          
             try (rewrite ATL1); try (rewrite ATR1);
             try (rewrite ATL2); try (rewrite ATR2);                                     
             try (rewrite ASLaS); try (rewrite ASRaS); 
             try (rewrite ASLaT); try (rewrite ASRaT);
             try (rewrite refS); try (rewrite refT); try (auto).
         case_eq(eqS (bS s1 s2) aS); intro K1.
        assert (K2 : eqS (bS s2 s1) aS = true).
                    assert (K3 := comS s2 s1).
                    assert (K4 := transS _ _ _ K3 K1).
                    exact K4.
        rewrite K2. rewrite refS. rewrite refT. auto.
        case_eq(eqT (bT t1 t2) aT); intro K2.
        assert (K3 : eqS (bS s2 s1) aS = false).
                    assert (K4 := comS s2 s1).
                    assert (K5 := brel_transitive_f2 S eqS symS transS _ _ _ K4 K1).
                    exact K5.
        rewrite K3.
        assert (K4 : eqT (bT t2 t1) aT = true). 
              assert (K4 := comT t2 t1).
              assert (K5 := transT _ _ _ K4 K2).
              exact K5.
        rewrite K4. rewrite refS. rewrite refT. auto.
        assert (K3 : eqS (bS s2 s1) aS = false).
                    assert (K4 := comS s2 s1).
                    assert (K5 := brel_transitive_f2 S eqS symS transS _ _ _ K4 K1).
                    exact K5.
        rewrite K3.
        assert (K4 : eqT (bT t2 t1) aT = false).
                    assert (K4 := comT t2 t1).
                    assert (K5 := brel_transitive_f2 T eqT symT transT _ _ _ K4 K2).
                    exact K5.
        rewrite K4. rewrite comS. rewrite comT. auto.
Qed.

Lemma andb_is_true_elim : ∀ b1 b2 : bool, b1 && b2 = true → (b1 = true) * (b2 = true). 
Proof. induction b1; induction b2; simpl; intros.  
       split; reflexivity. 
       split. reflexivity. assumption. 
       split. assumption. reflexivity. 
       split. assumption. assumption. 
Defined. 

Lemma bop_reduce_annihilators_congruence_bop_v2 
(S T : Type)
(aS : S)
(aT : T)
(eqS : brel S)
(eqT : brel T)
(bS : binary_op S)
(bT : binary_op T)      
:   brel_reflexive S eqS -> brel_reflexive T eqT ->
bop_congruence S eqS bS ->
bop_congruence T eqT bT -> 
brel_transitive S eqS -> brel_transitive T eqT ->
brel_symmetric S eqS -> brel_symmetric T eqT ->      
bop_is_ann S eqS bS aS ->
bop_is_ann T eqT bT aT ->
bop_congruence (S * T) (brel_reduce (bop_reduce_annihilators aS aT eqS eqT) (brel_product eqS eqT)) (bop_full_reduce (bop_reduce_annihilators aS aT eqS eqT) (bop_product bS bT)).
Proof. intros refS refT congS congT tranS tranT symS symT AS AT a b c d H1 H2.
  apply bop_full_reduce_congruence. 
  compute. intros [s1 t1] [s2 t2] H.  
  case_eq (eqS s1 aS); intro A.
  case_eq (eqS s2 aS); intro B. rewrite (refS aS), (refT aT). auto.
  case_eq (eqT t2 aT); intro C.  rewrite (refS aS), (refT aT). auto.
  case_eq (eqS s1 s2); intro D; rewrite D in H. apply symS in A.
  assert (E := brel_transitive_f1 S eqS symS tranS _ _ _ B A). apply symS in D. rewrite D in E. discriminate. discriminate.
  case_eq (eqT t1 aT); intro B; case_eq(eqS s2 aS); intro C. rewrite (refS aS), (refT aT). auto.
  case_eq (eqT t2 aT); intro D. rewrite (refS aS), (refT aT). auto.
  case_eq (eqS s1 s2); intro E; rewrite E in H. apply symT in B.
  assert (F := brel_transitive_f1 T eqT symT tranT _ _ _ D B). assert (L := brel_symmetric_false T eqT symT _ _ F).  rewrite L in H. discriminate. discriminate.
  case_eq (eqS s1 s2); intro D; rewrite D in H.  apply symS in C.
  assert (E := brel_transitive_f1 S eqS symS tranS _ _ _ A C). rewrite E in D. discriminate. discriminate.
  case_eq (eqT t2 aT); intro D. 
  case_eq (eqS s1 s2); intro E; rewrite E in H.  apply symT in D.
  assert (F := brel_transitive_f1 T eqT symT tranT _ _ _ B D). rewrite F in H.  discriminate. discriminate.
  case_eq (eqS s1 s2); intro F; rewrite F in H. auto. discriminate.
  apply bop_product_congruence. auto. auto. auto. auto.
Qed.

Lemma bop_reduce_annihilators_congruence_bop
      (S T : Type)
      (aS : S)
      (aT : T)
      (eqS : brel S)
      (eqT : brel T)
      (bS : binary_op S)
      (bT : binary_op T)      
  :   brel_reflexive S eqS -> brel_reflexive T eqT ->
      bop_congruence S eqS bS ->
    bop_congruence T eqT bT -> 
(*
      bop_commutative S eqS bS -> bop_commutative T eqT bT ->
*)
     brel_transitive S eqS -> brel_transitive T eqT ->
      brel_symmetric S eqS -> brel_symmetric T eqT ->      
    bop_is_ann S eqS bS aS ->
    bop_is_ann T eqT bT aT ->
    bop_congruence 
      (S * T)
      (brel_product eqS eqT)
      (bop_full_reduce (bop_reduce_annihilators aS aT eqS eqT) (bop_product bS bT)). 
Proof. intros refS refT congS congT transS transT symS symT AS AT [s1 t1] [s2 t2] [s3 t3] [s4 t4] H1 H2. 
       unfold brel_product in H1, H2.
       apply andb_is_true_elim in H1.
       apply andb_is_true_elim in H2.
       destruct H1 as [HL1 HR1].
       destruct H2 as [HL2 HR2].     
        destruct (AS s1) as [ASL1 ASR1].
       destruct (AS s2) as [ASL2 ASR2].
       destruct (AS s3) as [ASL3 ASR3]. 
      destruct (AS s4) as [ASL4 ASR4]. 
       destruct (AS aS) as [ASLaS ASRaS].       
       destruct (AT t1) as [ATL1 ATR1].
       destruct (AT t2) as [ATL2 ATR2].
        destruct (AT t3) as [ATL3 ATR3].
       destruct (AT t4) as [ATL4 ATR4].
       destruct (AT aT) as [ATLaT ATRaT]. 
       compute. 
case_eq (eqS s1 aS); intro Hs1; case_eq (eqT t1 aT); intro Ht1;
case_eq (eqS s2 aS); intro Hs2; case_eq (eqT t2 aT); intro Ht2;
case_eq (eqS s3 aS); intro Hs3; case_eq (eqT t3 aT); intro Ht3;
case_eq (eqS s4 aS); intro Hs4; case_eq (eqT t4 aT); intro Ht4;
  repeat (        
             try (rewrite ASL1); try (rewrite ASR1);
             try (rewrite ASL2); try (rewrite ASR2);
             try (rewrite ASL3); try (rewrite ASR3);
             try (rewrite ASL4); try (rewrite ASR4);          
             try (rewrite ATL1); try (rewrite ATR1);
             try (rewrite ATL2); try (rewrite ATR2);
             try (rewrite ATL3); try (rewrite ATR3);
             try (rewrite ATL4); try (rewrite ATR4);                                      
             try (rewrite ASLaS); try (rewrite ASRaS);
             try (rewrite ASLaT); try (rewrite ASRaT);
             try (rewrite refS); try (rewrite refT); try (auto)).
apply symS in Hs1; assert (A := transS _ _ _ Hs1 HL1); apply symS in A; rewrite A in Hs3; discriminate.
apply symS in Hs1; assert (A := transS _ _ _ Hs1 HL1); apply symS in A; rewrite A in Hs3; discriminate.
apply symS in Hs1; assert (A := transS _ _ _ Hs1 HL1); apply symS in A; rewrite A in Hs3; discriminate.
apply symS in Hs1; assert (A := transS _ _ _ Hs1 HL1); apply symS in A; rewrite A in Hs3; discriminate.
apply symS in Hs1; assert (A := transS _ _ _ Hs1 HL1); apply symS in A; rewrite A in Hs3; discriminate.
apply symS in Hs1; assert (A := transS _ _ _ Hs1 HL1); apply symS in A; rewrite A in Hs3; discriminate.
apply symS in Hs1; assert (A := transS _ _ _ Hs1 HL1); apply symS in A; rewrite A in Hs3; discriminate.
apply symS in Hs1; assert (A := transS _ _ _ Hs1 HL1); apply symS in A; rewrite A in Hs3; discriminate.
apply symT in Ht1; assert (A := transT _ _ _ Ht1 HR1); apply symT in A; rewrite A in Ht3; discriminate.
apply symT in Ht1; assert (A := transT _ _ _ Ht1 HR1); apply symT in A; rewrite A in Ht3; discriminate.
apply symT in Ht1; assert (A := transT _ _ _ Ht1 HR1); apply symT in A; rewrite A in Ht3; discriminate.
apply symT in Ht1; assert (A := transT _ _ _ Ht1 HR1); apply symT in A; rewrite A in Ht3; discriminate.
apply symS in Hs2; assert (A := transS _ _ _ Hs2 HL2); apply symS in A; rewrite A in Hs4; discriminate.
apply symS in Hs2; assert (A := transS _ _ _ Hs2 HL2); apply symS in A; rewrite A in Hs4; discriminate.
apply symT in Ht2; assert (A := transT _ _ _ Ht2 HR2); apply symT in A; rewrite A in Ht4; discriminate.
assert (A := transS _ _ _ HL1 Hs3); rewrite A in Hs1; discriminate.
assert (A := transS _ _ _ HL1 Hs3); rewrite A in Hs1; discriminate.
assert (A := transS _ _ _ HL1 Hs3); rewrite A in Hs1; discriminate.
assert (A := transS _ _ _ HL1 Hs3); rewrite A in Hs1; discriminate.
assert (A := transS _ _ _ HL1 Hs3); rewrite A in Hs1; discriminate.
assert (A := transS _ _ _ HL1 Hs3); rewrite A in Hs1; discriminate.
assert (A := transS _ _ _ HL1 Hs3); rewrite A in Hs1; discriminate.
assert (A := transS _ _ _ HL1 Hs3); rewrite A in Hs1; discriminate.
assert (A := transT _ _ _ HR1 Ht3); rewrite A in Ht1; discriminate.
assert (A := transT _ _ _ HR1 Ht3); rewrite A in Ht1; discriminate.
assert (A := transT _ _ _ HR1 Ht3); rewrite A in Ht1; discriminate.
assert (A := transT _ _ _ HR1 Ht3); rewrite A in Ht1; discriminate.
assert (A := transS _ _ _ HL2 Hs4); rewrite A in Hs2; discriminate.
assert (A := transS _ _ _ HL2 Hs4); rewrite A in Hs2; discriminate.
assert (A := transT _ _ _ HR2 Ht4); rewrite A in Ht2; discriminate.
case_eq (eqS (bS s1 s2) aS); intros K.
assert (A:= congS s1 s2 s3 s4 HL1 HL2). apply symS in A. assert (B := transS _ _ _ A K). rewrite B. rewrite refS. rewrite refT. auto.
case_eq (eqT (bT t1 t2) aT); intros L.
assert (A:= congS s1 s2 s3 s4 HL1 HL2). apply symS in A. assert (B :=  brel_transitive_f2 S eqS symS transS _ _ _ A K). rewrite B.
assert (C:= congT t1 t2 t3 t4 HR1 HR2). apply symT in C. assert (D := transT _ _ _ C L). rewrite D. rewrite refS. rewrite refT. auto.
assert (A:= congS s1 s2 s3 s4 HL1 HL2). apply symS in A. assert (B :=  brel_transitive_f2 S eqS symS transS _ _ _ A K). rewrite B.
assert (C:= congT t1 t2 t3 t4 HR1 HR2). apply symT in C. assert (D :=  brel_transitive_f2 T eqT symT transT _ _ _ C L). rewrite D.
apply symS in A; rewrite A. apply symT in C; rewrite C. auto.
Qed.




Definition reduced_ann_eqv_proofs : forall (S T: Type) (aS : S) (aT : T)(eqS : brel S) (eqT : brel T)
    (bS : binary_op S)(bT : binary_op T) (brS: brel_reflexive S eqS)(brT:brel_reflexive T eqT),
    eqv_proofs S eqS -> eqv_proofs T eqT ->
    eqv_proofs (red_Type (S * T) (bop_reduce_annihilators aS aT eqS eqT) (brel_product eqS eqT)) 
                      (red_eq (S * T) (bop_reduce_annihilators aS aT eqS eqT) (brel_product eqS eqT))
:= λ S T aS aT eqS eqT bS bT brS brT eqvS eqvT,
{|
  eqv_reflexive := red_ref (S*T) 
                                        (bop_reduce_annihilators aS aT eqS eqT)
                                        (brel_product eqS eqT) 
                                        (eqv_reflexive (S*T) 
                                                               (brel_product eqS eqT) 
                                                               (eqv_proofs_product S T eqS eqT eqvS eqvT));
  eqv_transitive := red_trans (S*T) 
                                             (bop_reduce_annihilators aS aT eqS eqT)
                                             (brel_product eqS eqT)
                                             (eqv_transitive (S*T) 
                                                                     (brel_product eqS eqT) 
                                                                     (eqv_proofs_product S T eqS eqT eqvS eqvT));
  eqv_symmetric := red_sym (S*T) 
                                              (bop_reduce_annihilators aS aT eqS eqT)
                                              (brel_product eqS eqT)
                                              (eqv_symmetric (S*T) 
                                                                        (brel_product eqS eqT) 
                                                                        (eqv_proofs_product S T eqS eqT eqvS eqvT));
 eqv_congruence := red_cong (S*T) 
                                              (bop_reduce_annihilators aS aT eqS eqT)
                                              (brel_product eqS eqT)
                                              (brel_product_congruence S T eqS eqT (eqv_congruence S eqS eqvS) (eqv_congruence T eqT eqvT)); 
    
  eqv_witness := inj (S*T) 
                               (bop_reduce_annihilators aS aT eqS eqT) 
                               (brel_product eqS eqT) 
                               (bop_reduce_annihilators_idempotent S T aS aT eqS eqT brS brT) 
                               (eqv_witness (S*T) 
                                                     (brel_product eqS eqT) 
                                                     (eqv_proofs_product S T eqS eqT eqvS eqvT))
|}.

Definition reduced_ann_commutative_semigroup_proofs : forall (S T: Type) (eqS : brel S) (eqT : brel T) (bS : binary_op S)(bT : binary_op T)
    (eqvS:eqv_proofs S eqS) (eqvT:eqv_proofs T eqT)
    (sgS : commutative_semigroup_proofs S eqS bS)
    (sgT : commutative_semigroup_proofs T eqT bT)                                        
    (aS : S) (aaS : bop_is_ann S eqS bS aS)
    (aT : T) (aaT : bop_is_ann T eqT bT aT), 
    commutative_semigroup_proofs (S * T) (brel_product eqS eqT) (bop_full_reduce (bop_reduce_annihilators aS aT eqS eqT) (bop_product bS bT))
:=  λ S T eqS eqT bS bT eqvS eqvT sgS sgT aS aaS aT aaT,
{|
  csg_associative   := 
bop_reduce_annihilators_associative S T aS aT eqS eqT bS bT 
(eqv_reflexive S eqS eqvS)
(eqv_reflexive T eqT eqvT)
(eqv_symmetric S eqS eqvS)
(eqv_symmetric T eqT eqvT)
(eqv_transitive S eqS eqvS)
(eqv_transitive T eqT eqvT) aaS aaT
(csg_congruence S eqS bS sgS)
(csg_congruence T eqT bT sgT)
(csg_associative S eqS bS sgS)
(csg_associative T eqT bT sgT)
; csg_congruence    := 
 bop_reduce_annihilators_congruence_bop S T aS aT eqS eqT bS bT
(eqv_reflexive S eqS eqvS)
(eqv_reflexive T eqT eqvT)
(csg_congruence S eqS bS sgS)
(csg_congruence T eqT bT sgT)
(eqv_transitive S eqS eqvS)
(eqv_transitive T eqT eqvT)
(eqv_symmetric S eqS eqvS)
(eqv_symmetric T eqT eqvT)
aaS aaT
; csg_commutative   := 
bop_reduce_annihilators_commutative S T aS aT eqS eqT bS bT 
(eqv_reflexive S eqS eqvS)
(eqv_reflexive T eqT eqvT)
(csg_commutative S eqS bS sgS)
(csg_commutative T eqT bT sgT)
(eqv_symmetric S eqS eqvS)
(eqv_symmetric T eqT eqvT)
(eqv_transitive S eqS eqvS)
(eqv_transitive T eqT eqvT) aaS aaT                                   
|}.

Definition commutative_rsemigroup_ann_reduced : 
  forall (S T : Type) (eqS : brel S) (eqT : brel T) (eqvS : eqv_proofs S eqS) (eqvT : eqv_proofs T eqT) (bS : binary_op S) (bT : binary_op T)
    (sgpS : commutative_semigroup_proofs S eqS bS)
    (sgpT : commutative_semigroup_proofs T eqT bT)
    (aS : S) (aaS : bop_is_ann S eqS bS aS)
    (aT : T) (aaT : bop_is_ann T eqT bT aT),     
               commutative_rsemigroup (S * T)
:=  λ S T eqS eqT eqvS eqvT bS bT sgpS sgpT aS aaS aT aaT,
{|
   cr_eq   := brel_product eqS eqT
;  cr_rep  := bop_reduce_annihilators aS aT eqS eqT                   
;  cr_bop  := bop_full_reduce (bop_reduce_annihilators aS aT eqS eqT) (bop_product bS bT) 
;  cr_eqv  := eqv_proofs_product S T eqS eqT eqvS eqvT 
;  cr_rpv  :=
reduce_annihilators_reduction_eqv_proofs S T aS aT eqS eqT
(eqv_reflexive S eqS eqvS)
(eqv_symmetric S eqS eqvS)
(eqv_transitive S eqS eqvS)
(eqv_reflexive T eqT eqvT)
(eqv_symmetric T eqT eqvT)
(eqv_transitive T eqT eqvT)          
;  cr_sgp  := reduced_ann_commutative_semigroup_proofs S T eqS eqT bS bT eqvS eqvT sgpS sgpT aS aaS aT aaT
|}.

Lemma bop_is_ann_product (S : Type) ( T : Type)(eqS : brel S)(eqT : brel T) (bS : binary_op S)(bT : binary_op T)  (annS : S) (annT : T)
             (refS : brel_reflexive S eqS)(refT: brel_reflexive T eqT):
             bop_is_ann S eqS bS annS -> bop_is_ann T eqT bT annT ->
            bop_is_ann (S*T) (brel_product eqS eqT) (bop_full_reduce (bop_reduce_annihilators annS annT eqS eqT) (bop_product bS bT)) (annS,annT).
Proof. intros isAnnS isAnnT. compute. rewrite refS. intro st. destruct st. compute in isAnnS. compute in isAnnT.
case_eq (eqS s annS); intro K.
assert (A := isAnnS annS). destruct A as [A1 A2]. rewrite A1.  rewrite refS. rewrite refT. split;auto.
case_eq(eqT t annT); intro L.
assert (A := isAnnS annS). destruct A as [A1 A2]. rewrite A1.  rewrite refS. rewrite refT. split;auto.
assert (A := isAnnS s). destruct A as [A1 A2]. rewrite A1. rewrite A2.  rewrite refS. rewrite refT. auto.
Qed.

Lemma bop_self_divisor_product (S : Type) ( T : Type)(eqS : brel S)(eqT : brel T) (bS : binary_op S)(bT : binary_op T)  (annS : S) (annT : T) : 
  bop_self_divisor (S * T)
                   (brel_product eqS eqT)
                    (bop_full_reduce (bop_reduce_annihilators annS annT eqS eqT)
                                     (bop_product bS bT)) (annS, annT). 
Admitted. 

Definition commutative_semigroup_ann_reduced_proof : 
  forall (S T : Type)(eqS : brel S)(eqT : brel T) (bS : binary_op S)(bT : binary_op T)  (annS : S) (annT : T)
          (eqvS:eqv_proofs S eqS) (eqvT:eqv_proofs T eqT)
           (csgapS : commutative_semigroup_with_ann_proofs S eqS bS annS) 
           (csgapT : commutative_semigroup_with_ann_proofs T eqT bT annT),     
               commutative_semigroup_with_ann_proofs (S * T) (brel_product eqS eqT) (bop_full_reduce (bop_reduce_annihilators annS annT eqS eqT) (bop_product bS bT)) (annS,annT)
:=  λ S T eqS eqT bS bT annS annT eqvS eqvT csgapS csgapT,
{|
csgwa_associative   :=
bop_reduce_annihilators_associative S T annS annT eqS eqT bS bT 
(eqv_reflexive S eqS eqvS)
(eqv_reflexive T eqT eqvT)
(eqv_symmetric S eqS eqvS)
(eqv_symmetric T eqT eqvT)
(eqv_transitive S eqS eqvS)
(eqv_transitive T eqT eqvT) (csgwa_is_ann  S eqS bS annS csgapS) (csgwa_is_ann  T eqT bT annT csgapT)
(csgwa_congruence S eqS bS annS csgapS)
(csgwa_congruence T eqT bT annT csgapT)
(csgwa_associative S eqS bS annS csgapS)
(csgwa_associative T eqT bT annT csgapT)
; csgwa_congruence    := 
 bop_reduce_annihilators_congruence_bop S T annS annT eqS eqT bS bT
(eqv_reflexive S eqS eqvS)
(eqv_reflexive T eqT eqvT)
(csgwa_congruence S eqS bS annS csgapS)
(csgwa_congruence T eqT bT annT csgapT)
(eqv_transitive S eqS eqvS)
(eqv_transitive T eqT eqvT)
(eqv_symmetric S eqS eqvS)
(eqv_symmetric T eqT eqvT)
(csgwa_is_ann  S eqS bS annS csgapS) (csgwa_is_ann  T eqT bT annT csgapT)
; csgwa_commutative   :=
bop_reduce_annihilators_commutative S T annS annT eqS eqT bS bT 
(eqv_reflexive S eqS eqvS)
(eqv_reflexive T eqT eqvT)
(csgwa_commutative S eqS bS annS csgapS)
(csgwa_commutative T eqT bT annT csgapT)
(eqv_symmetric S eqS eqvS)
(eqv_symmetric T eqT eqvT)
(eqv_transitive S eqS eqvS)
(eqv_transitive T eqT eqvT)
(csgwa_is_ann  S eqS bS annS csgapS) (csgwa_is_ann  T eqT bT annT csgapT)
; csgwa_is_ann  :=  bop_is_ann_product S T eqS eqT  bS bT annS annT (eqv_reflexive S eqS eqvS) (eqv_reflexive T eqT eqvT) (csgwa_is_ann S eqS bS annS csgapS) (csgwa_is_ann T eqT bT annT csgapT)
; csgwa_div := bop_self_divisor_product S T eqS eqT  bS bT annS annT                                        
|}.

Definition commutative_semigroup_ann_reduced : 
  forall (S T : Type)
           (csgaS : commutative_semigroup_with_ann S) 
           (csgaT : commutative_semigroup_with_ann T),     
               commutative_semigroup_with_ann (S * T)
:= λ S T csgaS csgaT,
{|
    ceqa    := brel_product (ceqa S csgaS) (ceqa T csgaT)      
;  cbopa  := bop_full_reduce (bop_reduce_annihilators (canna S csgaS) (canna T csgaT) (ceqa S csgaS) (ceqa T csgaT)) (bop_product (cbopa S csgaS) (cbopa T csgaT))
;  canna  :=  (canna S csgaS, canna T csgaT)
;  ceqva  := eqv_proofs_product S T (ceqa S csgaS) (ceqa T csgaT) (ceqva S csgaS) (ceqva T csgaT)               
;  csgpa  := commutative_semigroup_ann_reduced_proof S T (ceqa S csgaS) (ceqa T csgaT)
(cbopa S csgaS) (cbopa T csgaT)(canna S csgaS) (canna T csgaT) (ceqva S csgaS) (ceqva T csgaT) (csgpa S csgaS) (csgpa T csgaT)
|}.



End Reduce_Annihilators. 
