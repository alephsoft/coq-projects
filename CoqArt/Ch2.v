Require Import Arith.
Require Import ZArith.
Require Import Bool.
Check (fun a b c:Z => (b*b-4*a*c)%Z).

Check (fun (f g:nat->nat)(n:nat) => g (f n)).

Section ex_2_7.
  Definition my_fun (z:Z) : Z := 2*z*z + 3*z + 3.  
End ex_2_7.
Print my_fun.
Eval cbv iota beta zeta delta in (my_fun 3).

Section Minimal_propositional_logic.
  Variables P Q R T : Prop.
  Theorem imp_trans : (P->Q)->(Q->R)->P->R.
    Proof. intros. 
           apply H0. 
           apply H. 
           assumption.
    Qed.
  Lemma id_P : P->P.
    Proof. intro H. 
           assumption.
    Qed.
  Lemma id_PP : (P->P)->(P->P).
    Proof. intro H. 
           assumption.
    Qed.
  Lemma imp_perm : (P->Q->R)->(Q->P->R).
    Proof. intros H J K. 
           apply H. 
           assumption. 
           assumption.
    Qed.
  Lemma ignore_Q : (P->R)->P->Q->R.
    Proof. intros H J K. 
           apply H. 
           assumption.
    Qed.
  Lemma delta_imp : (P->P->Q)->P->Q.
    Proof. intros H J. 
           apply H. 
           assumption. 
           assumption.
    Qed.
  Lemma delta_impR : (P->Q)->(P->P->Q).
    Proof. intros H J. 
           assumption.
    Qed.
  Lemma diamond : (P->Q)->(P->R)->(Q->R->T)->P->T.
    Proof. intros H J K L. 
           apply K. 
           apply H. 
           assumption. 
           apply J. 
           assumption.
    Qed.
  Lemma weak_peirce : ((((P->Q)->P)->P)->Q)->Q.
    Proof. intro H. 
           apply H. 
           intro J. 
           apply J. 
           intro K. 
           apply H. 
           intro L. 
           assumption.
    Qed.
End Minimal_propositional_logic.

