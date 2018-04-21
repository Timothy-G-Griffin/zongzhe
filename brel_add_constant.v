Require Import Coq.Bool.Bool.    
Require Import CAS.basic. 
Require Import CAS.properties. 

Section AddConstant. 

Variable S  : Type. 
Variable rS : brel S.
Variable c : cas_constant.
Variable wS : S. 
Variable conS : brel_congruence S rS rS.
Variable refS : brel_reflexive S rS.
Variable symS : brel_symmetric S rS.
Variable tranS : brel_transitive S rS.

Notation "a <+> b"  := (brel_add_constant b a) (at level 15).

Lemma brel_add_constant_congruence : 
       brel_congruence S rS rS → brel_congruence (cas_constant + S) (c <+> rS) (c <+> rS). 
Proof. unfold brel_congruence. 
     intros congS [s | s] [t | t] [u | u] [v | v]; simpl; intros H Q; auto. 
     discriminate. discriminate. discriminate. discriminate. discriminate. discriminate.
Qed. 

Lemma brel_add_constant_reflexive : brel_reflexive (cas_constant + S) (c <+> rS). 
Proof. intros [a | b]; simpl. reflexivity. apply refS. Qed. 

Lemma brel_add_constant_symmetric : brel_symmetric (cas_constant + S) (c <+> rS). 
Proof.  intros [c1 | s1] [c2 | s2]; simpl; intro H; auto. Qed. 

Lemma brel_add_constant_transitive : brel_transitive (cas_constant + S) (c <+> rS). 
Proof. intros [s1 | t1] [s2 | t2] [s3 | t3]; simpl; intros H1 H2; auto. discriminate. apply (tranS _ _ _ H1 H2). Qed. 

End AddConstant. 

