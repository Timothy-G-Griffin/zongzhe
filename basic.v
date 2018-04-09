Require Export Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.   
Close Scope nat.

Definition brel (S : Type)              := S → S → bool.
Definition unary_op (S : Type)          := S → S. 
Definition binary_op (S : Type)         := S → S → S.

Definition brel_product {S T : Type} (eqS : brel S) (eqT : brel T) : brel (S * T)
:= λ x y, 
   match x, y with
   | (s1, t1), (s2, t2) => andb (eqS s1 s2) (eqT t1 t2) 
   end.

Definition brel_reduce {S : Type} (r : unary_op S) (eq : brel S) : brel S
  := λ x y,  eq (r x) (r y).   

Definition uop_id {S : Type} : unary_op S
:= λ s, s.

Definition uop_compose {S : Type} (r1 : unary_op S) (r2 : unary_op S) : unary_op S
:= λ s, r1 (r2 s).

Definition uop_product : ∀ {S T : Type}, unary_op S → unary_op T → unary_op (S * T) 
:= λ {S} {T} f g p,  
   match p with
    | (s, t) => (f s, g t) 
   end.

Definition bop_product {S T : Type} (bS : binary_op S) (bT : binary_op T): binary_op (S * T) 
  := λ x y,
   match x, y with
    | (s1, t1), (s2, t2) => (bS s1 s2, bT t1 t2) 
   end.

Definition bop_reduce {S : Type} (r : unary_op S) (b : binary_op S) : binary_op S
  := λ x y,  r (b x y).

Definition bop_reduce_args {S : Type} (r : unary_op S) (b : binary_op S) : binary_op S
  := λ x y,  b (r x) (r y).   

Definition bop_full_reduce {S : Type} (r : unary_op S) (b : binary_op S) : binary_op S
  := λ x y,  r(b (r x) (r y)).   

Require Import Coq.Strings.String.   
Open Scope list_scope.

Definition cas_constant : Type          := string.   
Definition bop_concat : ∀ {S : Type}, binary_op (list S) := λ {S} x y,  x ++ y.

Definition brel_list : ∀ {S : Type}, brel S → brel(list S)
:= fix f {S} U x y := 
      match x, y with
         | nil, nil => true 
         | nil, _ => false 
         | _, nil => false 
         | a::tla, b::tlb => andb (U a b) (f U tla tlb)
      end.

Definition bop_add_ann : ∀ {S : Type}, binary_op S → cas_constant → binary_op (cas_constant + S)
:= λ {S} bS c x y, 
   match x, y with
   | (inl _), _       => inl c
   |       _, (inl _) => inl c
   | (inr a), (inr b) => inr _ (bS a b)
   end.

Definition brel_add_constant : ∀ {S : Type}, brel S → cas_constant → brel (cas_constant + S)
:= λ  {S} rS c x y, 
   match x, y with
   | (inl _), (inl _) => true (* all constants equal! *) 
   | (inl _), (inr _) => false 
   | (inr _), (inl _) => false 
   | (inr a), (inr b) => rS a b 
   end.

Definition bop_add_id : ∀ {S : Type}, binary_op S → cas_constant → binary_op (cas_constant + S)
:= λ  {S} bS c x y, 
   match x, y with
   | (inl _), (inl _) => inl c 
   | (inl _), (inr _) => y
   | (inr _), (inl _) => x
   | (inr a), (inr b) => inr _ (bS a b)
   end.

Definition brel_complement : ∀ {S : Type}, brel S -> brel S 
   := λ {S} r x y,  if (r x y) then false else true. 
   
Definition brel_conjunction : ∀ {S : Type}, brel S -> brel S -> brel S 
   := λ {S} r1 r2 x y,  (r1 x y) && (r2 x y). 
   
(* r' x y = true  <-> r x (b x y) *) 
Definition brel_llte : ∀ {S : Type}, brel S → binary_op S → brel S 
   := λ {S} eq b x y, eq x (b x y). 
   
Definition brel_llt : ∀ {S : Type}, brel S → binary_op S → brel S 
   := λ {S} eq b, brel_conjunction (brel_llte eq b) (brel_complement eq). 

(*
(a, b) llex (c, d) = (a + c, test(=, a,  c, b + d, test(<, a, c, b, d)))
*) 
Definition bop_llex : ∀ {S T : Type}, brel S → binary_op S → binary_op T → binary_op (S * T) 
:= λ {S T} eq b1 b2 x y,  
   match x, y with
    | (a, b), (c, d) => 
        (b1 a c, 
         if eq a c 
         then (b2 b d)
         else if brel_llt eq b1 a c 
              then b 
              else d)
   end.