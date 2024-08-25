(* Charles C. Pinter - A Book of Abstract Algebra *)

Require Export Coq.Sets.Ensembles.

Section Ch3.
(* Definition of a Group *)
Variable G : Set.
Variable f : G -> G -> G.
Variable e : G.
Variable i : G -> G.
Infix "<o>" := f (at level 50, left associativity).

Axiom assoc : forall a b c : G, a <o> b <o> c = a <o> (b <o> c).
Axiom id_r : forall a : G, a <o> e = a.
Axiom inv_r : forall a : G, a <o> i a = e.

(*** Chapter 3 Exercises ***)

(* Section C - Groups of Subsets of a Set *)

Infix "(-)" := Setminus (at level 50, left associativity).

Definition SymDiff (A B:Ensemble) : Ensemble :=
  
Theorem C_1a : forall A B : Set, A (+) B = B (+) A.


