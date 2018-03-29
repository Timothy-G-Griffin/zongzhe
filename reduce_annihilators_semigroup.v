Require Export Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.   
Require Import CAS.basic. 
Require Import CAS.properties. 
Require Import CAS.structures.
Require Import CAS.reduce_annihilators_redux. 



Lemma bop_rap_mul_no_divisor (S T : Type) (eqS : brel S) (eqT : brel T) (mulS : binary_op S) (mulT : binary_op T) (aS : S) (aT : T) :
           brel_reflexive S eqS ->
           brel_reflexive T eqT ->
           bop_is_ann S eqS mulS aS ->           
           bop_is_ann T eqT mulT aT ->                      
           bop_self_divisor S eqS mulS aS ->
           bop_self_divisor T eqT mulT aT -> 
           bop_self_divisor (S * T)
                          (brel_reduce (uop_rap S T eqS eqT aS aT) (brel_product eqS eqT))
                          (bop_rap_mul S T eqS eqT aS aT mulS mulT)
                          (aS, aT).
Proof. unfold bop_self_divisor. intros refS refT is_annS is_annT H1 H2 [s1 t1] [s2 t2]; compute.
       destruct (is_annS aS) as [IS _].
       destruct (is_annT aT) as [IT _].
       case_eq(eqS s1 aS); intro J1; case_eq(eqS s2 aS); intro J2. 
       rewrite IS. rewrite refS, refT. rewrite refS. auto. 
       case_eq(eqT t2 aT); intro J3. rewrite IS. rewrite refS. rewrite refS. rewrite refT. auto. 
       case_eq(eqS (mulS aS s2) aS); intro J4.  rewrite refS. rewrite refS. rewrite refT. left. auto. 
       case_eq(eqT (mulT aT t2) aT); intro J5.  rewrite refS. rewrite refS. rewrite refT. left. auto.        
       rewrite J4. rewrite J5. rewrite refS. rewrite J4. intro F. discriminate F.
       case_eq(eqT t1 aT); intro J3. rewrite IS. rewrite refS. rewrite refS. rewrite refT. auto.
       case_eq(eqS (mulS s1 aS) aS); intro J4.  rewrite refS. rewrite refS. rewrite refT. intro F. right; auto.
       case_eq(eqT (mulT t1 aT) aT); intro J5.  rewrite refS. rewrite refS. rewrite refT. intro F. right; auto.
       rewrite J4. rewrite J5. rewrite refS. rewrite refS. intro F. right; auto.
       case_eq(eqT t1 aT); intro J3; case_eq(eqT t2 aT); intro J4. rewrite IS. rewrite refS. rewrite refS. rewrite refT; auto. 
       case_eq(eqS (mulS aS s2) aS); intro J5.  rewrite refS. rewrite refS. rewrite refT. intro F. left; auto.
       case_eq(eqT (mulT aT t2) aT); intro J6.  rewrite refS. rewrite refS. rewrite refT. intro F. left; auto.
       rewrite J5, J6. rewrite refS. rewrite refS. intro F. left; auto.
       case_eq(eqS (mulS s1 aS) aS); intro J5.  rewrite refS. rewrite refS. intro F. right; auto.
       case_eq(eqT (mulT t1 aT) aT); intro J6.  rewrite refS. rewrite refS. intro F. right; auto.
       rewrite J5, J6. rewrite refS. rewrite refS. intro F. right; auto.      
       case_eq(eqS (mulS s1 s2) aS); intro J5.
       destruct(H1 _ _ J5) as [J6 | J6]. rewrite J6 in J1. discriminate J1. rewrite J6 in J2. discriminate J2.
       case_eq(eqT (mulT t1 t2) aT); intro J6.
       destruct(H2 _ _ J6) as [J7 | J7]. rewrite J7 in J3. discriminate J3. rewrite J7 in J4. discriminate J4.
       rewrite J5, J6. rewrite refS. rewrite J5. intro F. discriminate F. 
Qed.

Definition rap_mul_product_proofs (S T : Type)
           (eqS : brel S) (eqT : brel T)
           (eqvS : eqv_proofs S eqS) (eqvT : eqv_proofs T eqT)                       
           (aS : S) (aT : T)
           (mulS : binary_op S) (mulT : binary_op T) : 
  commutative_semigroup_with_ann_proofs S eqS mulS aS ->
  commutative_semigroup_with_ann_proofs T eqT mulT aT ->
  commutative_semigroup_with_ann_proofs (S * T)
                                        (brel_reduce (uop_rap S T eqS eqT aS aT) (brel_product eqS eqT))
                                        (bop_rap_mul S T eqS eqT aS aT mulS mulT) (aS, aT) 
:= λ pS pT,
let refS       := eqv_reflexive S eqS eqvS in
let symS       := eqv_symmetric S eqS eqvS in
let tranS      := eqv_transitive S eqS eqvS in
let eqS_cong   := eqv_congruence S eqS eqvS in   
let refT       := eqv_reflexive T eqT eqvT in
let symT       := eqv_symmetric T eqT eqvT in
let tranT      := eqv_transitive T eqT eqvT in
let eqT_cong   := eqv_congruence T eqT eqvT in
let is_annS    := csgwa_is_ann S eqS mulS aS pS in
let is_annT    := csgwa_is_ann T eqT mulT aT pT in
let mulS_cong  := csgwa_congruence S eqS mulS aS pS in
let mulT_cong  := csgwa_congruence T eqT mulT aT pT in
let mulS_assoc := csgwa_associative S eqS mulS aS pS in
let mulT_assoc := csgwa_associative T eqT mulT aT pT in
let commS      := csgwa_commutative S eqS mulS aS pS in
let commT      := csgwa_commutative T eqT mulT aT pT in
let divS       := csgwa_div S eqS mulS aS pS in 
let divT       := csgwa_div T eqT mulT aT pT in
{|
    csgwa_associative   := bop_rap_mul_associative S T eqS eqT refS symS tranS refT symT tranT aS aT mulS mulT mulS_cong mulT_cong mulS_assoc mulT_assoc is_annS is_annT divS divT
  ; csgwa_congruence    := bop_rap_mul_congruence S T eqS eqT refS symS tranS refT symT tranT aS aT mulS mulT mulS_cong mulT_cong 
  ; csgwa_commutative   := bop_rap_mul_commutative_v2 S T eqS eqT refS symS tranS refT symT tranT aS aT mulS mulT commS commT 
  ; csgwa_is_ann        := bop_rap_mul_is_ann_v2 S T eqS eqT refS refT aS aT mulS mulT is_annS is_annT
  ; csgwa_div           := bop_rap_mul_no_divisor S T eqS eqT mulS mulT aS aT refS refT is_annS is_annT divS divT
|}. 


Definition rap_mul_product (S T : Type) :
  commutative_semigroup_with_ann S ->  commutative_semigroup_with_ann T ->  commutative_semigroup_with_ann (S * T) := 
λ sg1 sg2,
let eqS := ceqa S sg1 in
let eqT := ceqa T sg2 in
let aS := canna S sg1 in
let aT := canna T sg2 in
let mulS := cbopa S sg1 in
let mulT := cbopa T sg2 in
let eqvS := ceqva S sg1 in
let eqvT := ceqva T sg2 in
(* need better abstraction here *) 
let refS := eqv_reflexive _ _ eqvS in
let symS := eqv_symmetric _ _ eqvS in
let tranS := eqv_transitive _ _ eqvS in
let congS := eqv_congruence _ _ eqvS in
let refT := eqv_reflexive _ _ eqvT in
let symT := eqv_symmetric _ _ eqvT in
let tranT := eqv_transitive _ _ eqvT in
let congT := eqv_congruence _ _ eqvT in 
{|
   ceqa   := brel_reduce (uop_rap S T eqS eqT aS aT) (brel_product eqS eqT)
;  cbopa  := bop_rap_mul S T eqS eqT aS aT mulS mulT 
;  canna  := (aS, aT)
;  csgpa  := rap_mul_product_proofs S T eqS eqT eqvS eqvT aS aT mulS mulT (csgpa S sg1) (csgpa T sg2)
;  ceqva  := reduce_rap_eqv_proofs S T eqS eqT refS symS tranS congS refT symT tranT congT aS aT 
|}.
  
