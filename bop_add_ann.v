Require Import Coq.Bool.Bool. 
Require Import CAS.basic.
Require Import CAS.properties. 
Require Import CAS.brel_add_constant. 

Section AddAnn. 

Variable S  : Type. 
Variable rS : brel S.
Variable c : cas_constant.
Variable bS : binary_op S.

Variable refS : brel_reflexive S rS.
Variable congS : bop_congruence S rS bS.

Notation "a <+> b"  := (brel_add_constant b a) (at level 15).
Notation "a [+] b"  := (bop_add_ann b a)       (at level 15).

Lemma bop_add_ann_congruence : bop_congruence (cas_constant + S ) (c <+> rS) (c [+] bS). 
Proof. unfold bop_congruence. intros [s1 | t1] [s2 | t2] [s3 | t3] [s4 | t4]; simpl; intros H1 H2;auto. Qed. 

Lemma bop_add_ann_associative : bop_associative S rS bS -> bop_associative (cas_constant + S ) (c <+> rS) (c [+] bS). 
Proof. intros assS [s1 | t1] [s2 | t2] [s3 | t3]; simpl; auto. Qed. 

Lemma bop_add_ann_idempotent : bop_idempotent S rS bS → bop_idempotent (cas_constant + S ) (c <+> rS) (c [+] bS). 
Proof. intros idemS [s1 | t1]; simpl; auto. Qed. 

Lemma bop_add_ann_not_idempotent : bop_not_idempotent S rS bS → bop_not_idempotent (cas_constant + S ) (c <+> rS) (c [+] bS). 
Proof. intros [s P]. exists (inr _ s). simpl. assumption. Defined. 

Lemma bop_add_ann_commutative : bop_commutative S rS bS → bop_commutative (cas_constant + S ) (c <+> rS) (c [+] bS). 
Proof. intros commS [s1 | t1] [s2 | t2]; simpl; auto. Qed. 

Lemma bop_add_ann_not_commutative : bop_not_commutative S rS bS → bop_not_commutative (cas_constant + S ) (c <+> rS) (c [+] bS). 
Proof. intros [ [s t] P]. exists (inr _ s, inr _ t); simpl. assumption. Defined. 

Lemma bop_add_ann_selective : bop_selective S rS bS → bop_selective (cas_constant + S ) (c <+> rS) (c [+] bS). 
Proof. intros selS [s1 | t1] [s2 | t2]; simpl; auto. Qed. 

Lemma bop_add_ann_not_selective : bop_not_selective S rS bS → bop_not_selective (cas_constant + S ) (c <+> rS) (c [+] bS). 
Proof. intros [ [s1 s2] P]. exists (inr _ s1, inr _ s2). simpl. assumption. Defined. 

Lemma bop_add_ann_exists_ann : bop_exists_ann (cas_constant + S ) (c <+> rS) (c [+] bS).
Proof. exists (inl S c). intros [a | b]; compute; auto. Defined. 

Lemma bop_add_ann_exists_id : bop_exists_id S rS bS -> bop_exists_id (cas_constant + S ) (c <+> rS) (c [+] bS).
Proof. intros [annS pS]. exists (inr _ annS). intros [s | t]; compute; auto. Defined. 

(* Decide *)

Definition bop_add_ann_idempotent_decide : 
     bop_idempotent_decidable S rS bS  → bop_idempotent_decidable (cas_constant + S) (c <+> rS) (c [+] bS)
:= λ dS,  
   match dS with 
   | inl idemS     => inl _ (bop_add_ann_idempotent idemS)
   | inr not_idemS => inr _ (bop_add_ann_not_idempotent not_idemS)
   end.  

Definition bop_add_ann_commutative_decide : 
     bop_commutative_decidable S rS bS  → bop_commutative_decidable (cas_constant + S) (c <+> rS) (c [+] bS)
:= λ dS,  
   match dS with 
   | inl commS     => inl _ (bop_add_ann_commutative commS)
   | inr not_commS => inr _ (bop_add_ann_not_commutative not_commS)
   end. 

Definition bop_add_ann_selective_decide : 
     bop_selective_decidable S rS bS  → bop_selective_decidable (cas_constant + S) (c <+> rS) (c [+] bS)
:= λ dS,  
   match dS with 
   | inl selS       => inl _ (bop_add_ann_selective selS)
   | inr not_selS   => inr _ (bop_add_ann_not_selective not_selS)
   end. 

End AddAnn. 