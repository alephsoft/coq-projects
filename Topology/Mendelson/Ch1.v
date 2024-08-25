(* Introduction to Topology by Bert Mendelson *)
(* Chapter 1 *)

Require Export Coq.Sets.Powerset.

Section Ch1.

Theorem ex_1_2_1a : forall (U:Type) (A:Ensemble U), 
  In (Ensemble U) (Power_set U A) A. 
Proof.
  intros.
  apply Definition_of_Power_set.
  unfold Included.
  tauto. (* p -> p is true for any prop p *)
Qed.

(* exercise 1_2_1b is false *)
(* exercise 1_2_1c is true  *)

Theorem ex_1_2_1d : forall (U:Type) (A:Ensemble U),
  In (Ensemble U) (Power_set U A) (Empty_set U).
Proof.
  intros.
  apply Definition_of_Power_set.
  unfold Included.
  intros.
  inversion H. (* empty set is a subset of any set *)
Qed.

(* exercise 1_2_1e is true  *)
(* exercise 1_2_1f is false *)

Theorem ex_1_2_1g : forall (U:Type) (A B:Ensemble U), 
  Included U A B -> Included (Ensemble U) (Power_set U A) (Power_set U B).
Proof.
  intros U A B h1.
  unfold Included. 
  intros C h2.
  apply Definition_of_Power_set.
  replace C with A.
  - apply h1.
  - (* proof that A = C *)
Admitted.

(* exercise 1_2_1h is true *)

Theorem ex_1_2_2 : forall (U:Type) (A B C:Ensemble U), 
  (Included U A B /\ Included U B C) -> Included U A C.
Proof.
  intros U A B C h.
  unfold Included.
  intros x h0.
  unfold Included in h.
  destruct h as [h1 h2].
  apply h1 in h0.
  apply h2.
  tauto.
Qed.

(* Theorem ex_1_2_3 : *)

Theorem ex_1_3_1a : forall (U:Type) (A B:Ensemble U),
  Included U A B <-> Union U A B = B.
Proof.
  intros U A B. 
  split.
  - intros h. 
Admitted.

Theorem ex_1_3_1b : forall (U:Type) (A B:Ensemble U),
  Included U A B <-> Intersection U A B = A.
Proof.
  intros U A B. 
  split.
  - intros h.
Admitted.

Theorem ex_1_3_1c : forall (U:Type) (A B:Ensemble U),
  Included U A (Complement U B) <-> Intersection U A B = Empty_set U.
Proof.
  intros U A B.
  split.
  - intros h. 
Admitted.

Theorem ex_1_3_1d : forall (U:Type) (A B:Ensemble U),
  Included U (Complement U A) B <-> Union U A B = Full_set U.
Proof.
  intros U A B.
  split.
  - intros h. 
Admitted.

Theorem ex_1_3_1e : forall (U:Type) (A B:Ensemble U),
  Included U A B <-> Included U (Complement U B) (Complement U A).
Proof.
  intros U A B.
  split.
  - intros h. 
    unfold Included in h. 
    unfold Included. 
    intros x h0. 
Admitted.

Theorem ex_1_3_1f : forall (U:Type) (A B:Ensemble U),
  Included U A (Complement U B) <-> Included U B (Complement U A).
Proof.
  intros U A B.
  split.
  - intros h. 
Admitted.

Theorem ex_1_3_2a : forall (U:Type) (X Y Z:Ensemble U),
  Included U X Y /\ Included U Y Z -> Included U (Setminus U Y X) (Setminus U Z X).
Proof.
  intros U X Y Z h.
  destruct h as [h0 h1].
Admitted.

Theorem ex_1_3_2b : forall (U:Type) (X Y Z:Ensemble U),
  Included U X Y /\ Included U Y Z -> Setminus U Z (Setminus U Y X) = Union U X (Setminus U Z Y).
Proof.
  intros U X Y Z h.
  destruct h as [h0 h1].
Admitted.

End Ch1.