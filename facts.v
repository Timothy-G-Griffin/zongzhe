Require Import CAS.basic. 
Require Import CAS.properties. 

Section Facts. 
Variable S : Type.
  Variable eq    : brel S.
  Variable ref   : brel_reflexive S eq. 
  Variable sym   : brel_symmetric S eq. 
  Variable trans : brel_transitive S eq.

Lemma brel_transitive_f1 : 
  ∀ s t u: S, (eq s t = false) → (eq t u = true) → (eq s u = false).
Proof. intros s t u H1 H2.
       case_eq (eq s t); intro J1; case_eq (eq s u); intro J2.
       rewrite J1 in H1. exact H1. 
       reflexivity. 
       apply sym in J2. 
       assert (J3 := trans _ _ _ H2 J2). 
       apply sym in J3.
       rewrite J3 in H1. exact H1. 
       reflexivity. 
Qed.        

Lemma brel_transitive_f2 : 
  ∀ s t u: S, (eq s t = true) → (eq t u = false) → (eq s u = false).
Proof. intros s t u H1 H2.
       case_eq (eq t u); intro J1; case_eq (eq s u); intro J2.
       rewrite J1 in H2. exact H2. 
       reflexivity. 
       apply sym in J2. 
       assert (J3 := trans _ _ _ J2 H1). 
       apply sym in J3.
       rewrite J3 in H2. exact H2.
       reflexivity. 
Qed.          

End Facts. 