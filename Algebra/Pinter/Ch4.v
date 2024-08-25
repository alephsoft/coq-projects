(* Charles C. Pinter - A Book of Abstract Algebra *)

Require Export Coq.Sets.Ensembles.

(* Definition of a Group *)
Variable G : Set.
Variable f : G -> G -> G.
Variable e : G.
Variable i : G -> G.
Infix "<+>" := f (at level 50, left associativity).

Axiom assoc : forall a b c : G, 
  a <+> b <+> c = a <+> (b <+> c).
Axiom id_r : forall a : G, 
  a <+> e = a.
Axiom inv_r : forall a : G, 
  a <+> i a = e.

(* all of these theorems need to be proven using crush.*)

(* The identity [e] is unique. *)
Theorem unique_id : forall a, a <+> a = a -> a = e.
Proof. intros a Idem.
       replace a with (a <+> a <+> i a).
       rewrite Idem.
       apply inv_r.
       rewrite assoc.
       rewrite inv_r.
       apply id_r.
Qed.

Theorem unique_id_crushed : 
  forall a, 
    a <+> a = a
    -> (a <+> a) <+> i a = a <+> i a
    -> a <+> (a <+> i a) = e
    -> a <+> e = e
    -> a = e.
  (*crush.*)
Admitted. 
    
(* Parentheses can move left with 4 arguments. *)
Lemma quatre : forall a b c d, a <+> b <+> (c <+> d) = a <+> (b <+> c) <+> d.
Proof. intros a b c d.
       rewrite -> assoc.
       rewrite -> assoc.
       rewrite assoc. 
       reflexivity.
Qed.

(* [i a] is the left-inverse of [a]. *)
Theorem inv_l : forall a, i a <+> a = e.
Proof. intros a.
       apply unique_id.
       rewrite quatre.
       rewrite inv_r.
       rewrite id_r.
       reflexivity.
Qed.

(* [e] is the left-identity. *)
Theorem id_l : forall a, e <+> a = a.
Proof. intros a.
       replace e with (a <+> i a).
       rewrite assoc.
       rewrite inv_l.
       apply id_r.
       apply inv_r.
Qed.

(* equality if, and only if, inverse are equal. *)
(*Lemma eq_iff_inveq : forall a b, a = b <-> i a = i b.
  Proof. intros a b.
       split.
       2:{ intro H1.
           assert (H2: b <+> i a = e).
           rewrite -> H1.
           apply inv_r.
           assert (H3 :).
           rewrite -> H1.
         }
       1:{ intro H0.
           rewrite H0.
           reflexivity.
         }
Admitted. *)

(* [x] can be cancelled on the right. *)
Theorem cancel_r : forall a b x, a <+> x = b <+> x -> a = b.
Proof. intros a b x H0.
       assert (H1: a <+> x <+> i x = b <+> x <+> i x).
       - rewrite H0.
         reflexivity.
       - rewrite assoc in H1.
         rewrite inv_r in H1.
         rewrite id_r  in H1.
         rewrite assoc in H1.
         rewrite inv_r in H1.
         rewrite id_r  in H1.
         assumption.  
Qed. 

(* [x] can be cancelled on the left. *)
Theorem cancel_l : forall a b x, x <+> a = x <+> b -> a = b.
Proof. intros a b x H0.
       assert (H1: i x <+> (x <+> a) = i x <+> (x <+> b)).
       - rewrite H0.
         reflexivity.
       - rewrite <- assoc in H1.
         rewrite inv_l in H1.
         rewrite id_l in H1.
         rewrite <- assoc in H1.
         rewrite inv_l in H1.
         rewrite id_l in H1.
         assumption.
Qed.

(* The left identity is unique. *)
Theorem e_uniq_l : forall a p, p <+> a = a -> p = e.
Proof. intros a p H0.
       assert (H1: p <+> a <+> i a = a <+> i a).
       - rewrite H0. reflexivity.
       - rewrite assoc in H1.
         rewrite inv_r in H1.
         rewrite id_r in H1.
         assumption. 
Qed.

(* The left inverse is unique. *)
Theorem inv_uniq_l : forall a b, a <+> b = e <-> a = i b.
Proof. intros a b. split.
       - intros H. 
         assert (H0: a <+> b <+> i b = e <+> i b).
           rewrite H. reflexivity.
         rewrite assoc in H0.
         rewrite inv_r in H0.
         rewrite id_l in H0.
         rewrite id_r in H0.
         assumption.
       - intros J.
         assert (J0: a <+> b = i b <+> b).
           rewrite J. reflexivity.
         rewrite inv_l in J0.
         assumption.
Qed.

(* The right inverse is unique. *)
Theorem inv_uniq_r : forall a b, a <+> b = e <-> b = i a.
Proof. intros a b. split.
       - intros H. 
         assert (H0: i a <+> a <+> b = i a <+> e).
           rewrite assoc. rewrite H. reflexivity.
         rewrite inv_l in H0.
         rewrite id_l in H0.
         rewrite id_r in H0.
         assumption. 
       - intros J.
         rewrite J.
         rewrite inv_r.
         reflexivity.
Qed.

(* The inverse operator contravariantly distributes over the group operator. *)
Theorem inv_distr : forall a b, i (a <+> b) = i b <+> i a.
Proof. intros a b.
       assert (H0: i (a <+> b) <+> (a <+> b) = e).
       - rewrite inv_l. reflexivity.
       - assert (H1: i b <+> i a <+> (a <+> b) = e).
         rewrite quatre. 
         rewrite inv_l. 
         rewrite id_r. 
         rewrite inv_l. 
         reflexivity.
         rewrite <- H1 in H0.
         apply cancel_r in H0.
         assumption.
Qed.

(* The inverse of an inverse produces the original element. *)
Theorem inv_double : forall a, i (i a) = a.
Proof. intros a.
       assert (H0: i (i a) <+> i a = e).
       - rewrite inv_l. reflexivity.
       - assert (H1: a <+> i a = e).
         rewrite inv_r.
         reflexivity.
         rewrite <- H1 in H0.
         apply cancel_r in H0.
         assumption. 
Qed.

(* The identity is its own inverse. *)
Theorem inv_id : i e = e.
Proof. assert (H0: i e <+> e = e).
       - rewrite inv_l. reflexivity.
       - rewrite id_r in H0.
         assumption. 
Qed.

Section Ch4.

Theorem ex_4_A_1 : forall a b c x : G,
  a <+> x <+> b = c -> x = i a <+> c <+> i b.
Proof. intros a b c x H0.
       assert (i a <+> a <+> x <+> b = i a <+> c).
       - rewrite assoc.
         rewrite assoc.
         replace (a <+> (x <+> b)) with (a <+> x <+> b).
         2:{ apply assoc. }
         rewrite H0.
         reflexivity.
       - assert (i a <+> a <+> x <+> b <+> i b = i a <+> c <+> i b).
         rewrite H. reflexivity.
         rewrite inv_l in H1.
         rewrite id_l in H1.
         rewrite assoc in H1.
         rewrite inv_r in H1.
         rewrite id_r in H1.
         assumption.
Qed.

Theorem ex_4_A_2 : forall a b x : G,
  x <+> x <+> b = x <+> i a -> x = i (b <+> a).
Proof. intros a b x H0.
       assert (i x <+> x <+> x <+> b = i x <+> x <+> i a).
       rewrite -> assoc.
       rewrite -> assoc.
       replace (x <+> (x <+> b)) with (x <+> x <+> b).
       rewrite H0. rewrite assoc. reflexivity.
       rewrite assoc. reflexivity.
       rewrite inv_l in H.
       rewrite id_l in H. rewrite id_l in H.
       assert (x <+> b <+> i b = i a <+> i b).
       rewrite H. reflexivity.
       rewrite assoc in H1.
       rewrite inv_r in H1.
       rewrite id_r in H1.
       rewrite inv_distr.
       assumption.
Qed.

Lemma assoc_quatre : forall a b c d : G,
  a <+> b <+> c <+> d = a <+> b <+> (c <+> d).
Proof. intros a b c d.
       rewrite assoc.
       reflexivity.
Qed.

Lemma assoc_4selec3 : forall a b c d : G,
  a <+> b <+> c <+> d = a <+> (b <+> c <+> d).
Proof. intros a b c d.
       rewrite assoc. rewrite assoc. rewrite assoc.
       reflexivity.
Qed. 

Lemma assoc_4selec2 : forall a b c d : G,
  a <+> b <+> c <+> d = a <+> (b <+> c) <+> d.
Proof. intros a b c d.
       rewrite assoc.
       rewrite quatre.
       reflexivity.
Qed. (* these associativity lemmas could probably be summed up in an all-encompassing theorem, whereby one sets the number of elements in all and the line of elements to parenthesize. *) 

  
Theorem ex_4_A_3 : forall a b c x : G,
    (x <+> x <+> a = b <+> x <+> i c) 
 /\ (a <+> c <+> x = x <+> a <+> c)
 -> (x = b <+> i (a <+> c)).
Proof. intros a b c x H0.
       destruct H0.
       assert (x <+> x <+> a <+> c = b <+> x <+> i c <+> c).
       - rewrite H. reflexivity.
       - rewrite assoc_quatre in H1.
         rewrite assoc_quatre in H1.
         rewrite <- assoc_quatre in H1. (* how can I rewrite RHS w/o LHS? *)
         rewrite inv_l in H1.
         rewrite assoc_4selec3 in H1.
         rewrite <- H0 in H1.
         rewrite <- assoc_4selec3 in H1.
         rewrite id_r in H1.
         assert (x <+> a <+> c <+> x <+> i x = b <+> x <+> i x).
         rewrite H1. reflexivity.
         rewrite assoc in H2.
         rewrite inv_r in H2.
         rewrite id_r in H2.
         rewrite assoc in H2. rewrite assoc in H2. rewrite <- assoc in H2.
         rewrite inv_r in H2.
         rewrite id_r in H2.
         assert (x <+> a <+> c <+> i (a <+> c) = b <+> i (a <+> c)).
         rewrite H2. reflexivity.
         rewrite assoc_4selec2 in H3.
         rewrite assoc in H3.
         rewrite inv_r in H3.
         rewrite id_r in H3.
         assumption.
Qed.

Theorem ex_4_A_4 : forall a b x : G,
    (a <+> x <+> x = b) 
 /\ (x <+> x <+> x = e) 
 -> (x = i b <+> a).  
Proof. intros a b x H0.
       destruct H0.
       assert (a <+> x <+> x <+> x = b <+> x).
       rewrite H. reflexivity.
       rewrite assoc_4selec3 in H1.
       rewrite H0 in H1.
       rewrite id_r in H1.
       assert (i b <+> a = i b <+> b <+> x).
       rewrite H1. rewrite assoc. reflexivity.
       rewrite inv_l in H2.
       rewrite id_l in H2.
       symmetry.
       assumption.
Qed. 

Theorem ex_4_A_5 : forall a x : G,
    (x <+> x = a <+> a) 
 /\ (x <+> x <+> x <+> x <+> x = e) 
 -> (x = i (a <+> a <+> a <+> a)).
Proof. intros a x H0. destruct H0.
       assert (x <+> x <+> x <+> x <+> x <+> i x = i x).
       rewrite H0. rewrite id_l. reflexivity.
       rewrite assoc in H1. 
       rewrite inv_r in H1. 
       rewrite id_r in H1.
       assert (i (x <+> x <+> x <+> x) = i (i x)).
       rewrite H1. reflexivity.
       rewrite <- H. rewrite assoc. rewrite <- H. rewrite <- assoc.
       rewrite H2.
       rewrite inv_double.
       reflexivity.
Qed.

Lemma assoc_9selec3 : forall a b c d g h j k l : G,
  a <+> b <+> c <+> d <+> g <+> h <+> j <+> k <+> l
= a <+> b <+> (c <+> d <+> g) <+> (h <+> j <+> k) <+> l.
Proof. intros a b c d g h j k l.
       symmetry.
       rewrite <- assoc.
       rewrite <- assoc. 
       rewrite <- assoc. 
       rewrite <- assoc.
       reflexivity.
Qed. 

Theorem ex_4_A_6 : forall a b x : G,
    ((x <+> a <+> x) <+> (x <+> a <+> x) <+> (x <+> a <+> x) = b <+> x) 
 /\ (x <+> x <+> a = i (x <+> a)) 
 -> (x = i (a <+> b)).
    Proof. intros a b x H0. destruct H0.
       rewrite <- assoc in H.
       rewrite <- assoc in H.
       rewrite <- assoc in H.
       rewrite <- assoc in H.
       rewrite assoc_9selec3 in H.
       rewrite H0 in H.
       rewrite inv_r in H.
       rewrite id_l in H.
       rewrite inv_distr in H.
       rewrite assoc in H. 
       rewrite inv_l in H. 
       rewrite id_r in H.
       assert (i (a <+> b) = i b <+> b <+> x).
       rewrite assoc. rewrite <- H. apply inv_distr.
       rewrite inv_l in H1. rewrite id_l in H1.
       symmetry. assumption.
Qed.

Theorem ex_4_B_1 : forall x : G,
    ~ (x <+> x = e -> x = e).
    Proof. intros x. unfold "~". intros H.
      (* proof by contradiction goes here *)
    Admitted.      

Theorem ex_4_B_2 : forall x a : G, 
    ~ (x <+> x = a <+> a -> x = a).
    Proof.
      (* proof by contradiction goes here *)
    Admitted.
      
Theorem ex_4_B_3 : forall a b : G,
    ~ (a <+> b <+> (a <+> b) = a <+> a <+> b <+> b).
    Proof.       
      (* proof by contradiction goes here *)
    Admitted.
    
Theorem ex_4_B_4 : forall x : G,
    x <+> x = x 
 -> x = e.
    Proof. apply unique_id. Qed.
      
Theorem ex_4_B_5 : 
    ~ (exists y : G, forall x : G,   x = y <+> y) 
<-> forall y : G, exists x : G, ~(x = y <+> y) 
/\  ~ (exists y : G, forall x : G,   x = y <+> y) 
<-> forall y : G, exists x : G, ~(x = y <+> y). 
    Proof.       
      (* proof by contradiction goes here *)
    Admitted.

(*Theorem ex_4_B_6 :*)

Theorem ex_4_C_1 : forall a b : G,
    a <+> b = b <+> a 
 -> i a <+> i b = i b <+> i a.
    Proof. intros a b H.
           rewrite <- inv_distr.
           rewrite <- inv_distr.
           rewrite H. reflexivity.
Qed.

Theorem ex_4_C_2 : forall a b : G,
    a <+> b = b <+> a 
 -> a <+> i b = i b <+> a.
    Proof. 
      intros a b Comm.
      assert (a = i b <+> a <+> b).
        rewrite assoc. 
        rewrite Comm. 
        rewrite <- assoc. 
        rewrite inv_l. 
        rewrite id_l. 
        reflexivity.
      rewrite H.
      rewrite assoc.
      rewrite inv_r.
      rewrite id_r.
      rewrite assoc.
      rewrite Comm.
      rewrite <- assoc.
      rewrite quatre.
      rewrite inv_l.
      rewrite id_r.
      reflexivity.
Qed.

Theorem ex_4_C_3 : forall a b : G,
    a <+> b = b <+> a 
 -> a <+> (a <+> b) = (a <+> b) <+> a.
    Proof. 
      intros a b Comm.
      rewrite assoc.
      rewrite Comm.
      reflexivity.
Qed.

Theorem ex_4_C_4 : forall a b : G,
    a <+> b = b <+> a 
 -> (a <+> a) <+> (b <+> b) = (b <+> b) <+> (a <+> a).
    Proof. 
      intros a b Comm.       
      rewrite quatre. rewrite Comm. 
      rewrite <- quatre. rewrite Comm.
      rewrite  quatre. rewrite Comm.
      rewrite quatre. reflexivity.
Qed.

Lemma six : forall a b c d g h : G,
    a <+> b <+> c <+> d <+> g <+> h = a <+> b <+> (c <+> d) <+> g <+> h.
    Proof.
      intros a b c d g h.
      rewrite assoc. 
      rewrite assoc. 
      rewrite assoc. 
      rewrite assoc.
      rewrite assoc.
      rewrite assoc.
      rewrite assoc.
      rewrite assoc.
      reflexivity.
Qed.

(*removing the parentheses breaks the proof - why?*)
Theorem ex_4_C_5 : forall a b x : G,
    a <+> b = b <+> a 
-> (x <+> a <+> i x) <+> (x <+> b <+> i x) = (x <+> b <+> i x) <+> (x <+> a <+> i x).
    Proof.
      intros a b x Comm.
      rewrite assoc. 
      rewrite assoc. 
      rewrite assoc. 
      rewrite assoc. 
      rewrite assoc. 
      rewrite assoc.
      rewrite <- assoc. 
      rewrite <- assoc. 
      rewrite <- assoc. 
      rewrite <- assoc. 
      rewrite <- assoc. 
      rewrite <- assoc. 
      rewrite <- assoc. 
      rewrite <- assoc.
      rewrite six. rewrite inv_l. rewrite id_r.
      rewrite six. rewrite inv_l. rewrite id_r.
      rewrite assoc.
      rewrite quatre. rewrite Comm. 
      rewrite assoc. 
      rewrite assoc. 
      rewrite assoc. 
      rewrite assoc. 
      reflexivity.
Qed.

Lemma left_annex_4_3 : forall a b c d : G,
    a <+> b <+> (c <+> d) = a <+> (b <+> c <+> d).
    Proof.
      intros a b c d.
      rewrite assoc.
      rewrite assoc.
      reflexivity.
Qed.
 
Theorem ex_4_C_6 : forall a b : G,
    a <+> b = b <+> a 
<-> a <+> b <+> i a = b.
    Proof.
      intros a b. split.
      - intros H. 
        rewrite H. 
        rewrite assoc. 
        rewrite inv_r. 
        rewrite id_r. 
        reflexivity.
      - intros J.
        symmetry in J.
        rewrite J.
        rewrite assoc. 
        rewrite <- quatre. 
        rewrite inv_l. 
        rewrite id_r.
        rewrite <- assoc.
        rewrite <- assoc.
        symmetry in J.
        rewrite assoc.
        rewrite left_annex_4_3.
        rewrite J.
        reflexivity.
Qed.

Theorem ex_4_C_7 : forall a b : G,
    a <+> b = b <+> a 
<-> a <+> b <+> i a <+> i b = e.
    Proof.
      intros a b. split.
      - intros H.
        rewrite H. 
        rewrite assoc. 
        rewrite quatre. 
        rewrite inv_r. 
        rewrite id_r. 
        rewrite inv_r. 
        reflexivity.
      - intros J.
        assert (J0 : a <+> b <+> i a <+> i b <+> b = b).
        rewrite J. rewrite id_l. reflexivity.
        rewrite assoc in J0. 
        rewrite inv_l in J0.
        rewrite id_r in J0.
        assert (J1 : a <+> b <+> i a <+> a = b <+> a).
        rewrite J0. reflexivity.
        rewrite assoc in J1.
        rewrite inv_l in J1.
        rewrite id_r in J1.
        assumption.
Qed.

Theorem ex_4_D_1 : forall a b : G,
    a <+> b = e 
 -> b <+> a = e.
    Proof.
      intros a b H.
      apply inv_uniq_l in H.
      rewrite H.
      rewrite inv_r.
      reflexivity.
Qed.

Theorem ex_4_D_2 : forall a b c : G,
    a <+> b <+> c = e 
 -> c <+> a <+> b = e /\ b <+> c <+> a = e.
    Proof.
      intros a b c H. split.
      - assert (H0: c <+> a <+> b <+> c = c).
        rewrite assoc. 
        rewrite left_annex_4_3. 
        rewrite H. 
        rewrite id_r. 
        reflexivity.
        assert (H1: c <+> a <+> b <+> c <+> i c = c <+> i c).
        rewrite H0. reflexivity.
        rewrite assoc in H1.
        rewrite inv_r in H1.
        rewrite id_r in H1.
        assumption.
      - assert (J: i a <+> a <+> b <+> c = i a).
        rewrite assoc. 
        rewrite left_annex_4_3. 
        rewrite H.
        rewrite id_r. reflexivity.
        assert (J0: i a <+> a <+> b <+> c <+> a = i a <+> a).
        rewrite J. reflexivity.
        rewrite inv_l in J0.
        rewrite id_l in J0.
        assumption.
Qed.

(* generalization of 1 and 2 : Theorem ex_4_D_3 : forall *)

Theorem ex_4_D_4 : forall a x y : G,
    x <+> a <+> y = i a 
 -> y <+> a <+> x = i a.
    Proof. intros a x y H.
      assert (H0: i (x <+> a <+> y) = i (i a)).
        rewrite H. reflexivity.
      rewrite inv_double in H0.
      rewrite inv_distr in H0.
      rewrite inv_distr in H0.
      rewrite <- assoc in H0.
      symmetry in H0. 
      rewrite H0.
      rewrite assoc. rewrite assoc. 
      rewrite inv_l. rewrite id_r.
      rewrite <- assoc. 
      rewrite inv_r. rewrite id_l. 
      rewrite <- H0. reflexivity.
Qed.

Theorem ex_4_D_5 : forall a : G,
    a = i a 
<-> a <+> a = e.
    Proof. intros a. split.
      - intros H. replace e with (a <+> i a).
        rewrite <- H. reflexivity.
        rewrite inv_r. reflexivity.
      - intros J. apply inv_uniq_l in J. assumption.
Qed.

Theorem ex_4_D_6 : forall a b c : G,
    c = i c 
 -> a <+> b = c <-> a <+> b <+> c = e.
    Proof. intros a b c H. split.
      - intros H0. rewrite H in H0. 
        rewrite H0. rewrite inv_l. 
        reflexivity.
      - intros J0. apply inv_uniq_l in J0. rewrite <- H in J0. 
        assumption.
Qed.

Theorem ex_4_D_7 : forall a b c : G,
    a = i a /\ b = i b /\ c = i c
 -> a <+> b = c 
 -> b <+> c = a /\ c <+> a = b.  
    Proof. intros a b c H J. 
      destruct H. destruct H0.
      split.
      - assert (J0: a <+> b <+> c = i c <+> c).
          rewrite J. rewrite <- H1. reflexivity.
        rewrite inv_l in J0.
        assert (J1: a <+> (a <+> b <+> c) = a <+> e).
          rewrite J0. reflexivity.
        rewrite assoc in J1. 
        rewrite <- assoc in J1.
        rewrite <- assoc in J1.
        assert (J2: a <+> a = e). 
          apply inv_uniq_l. assumption.
        rewrite J2 in J1. 
        rewrite id_l in J1.
        rewrite id_r in J1.
        assumption.
      - assert (K0: c <+> (a <+> b) = c <+> i c).
          rewrite J. rewrite <- H1. reflexivity.
        rewrite inv_r in K0.
        rewrite <- assoc in K0.
        apply inv_uniq_l in K0. (*why does apply work instead of rewrite here? why does rewrite require setoids?*)
        rewrite K0. symmetry. 
        assumption.
Qed.

Theorem ex_4_D_8 : forall a b c : G,
    a <+> b <+> c = i (a <+> b <+> c) 
 -> b <+> c <+> a = i (b <+> c <+> a) 
 /\ c <+> a <+> b = i (c <+> a <+> b).
    Proof. intros a b c H. split.
      - assert (J0: b <+> c <+> (a <+> b <+> c) <+> a = e).
          rewrite H. rewrite inv_distr. rewrite inv_distr.
          rewrite assoc. rewrite <- quatre. rewrite inv_l. rewrite id_r. rewrite quatre. rewrite inv_r. rewrite id_r. rewrite inv_r. reflexivity.
        rewrite <- assoc in J0. rewrite <- assoc in J0.
        rewrite assoc in J0. rewrite assoc in J0. apply inv_uniq_l in J0. rewrite <- assoc in J0. assumption. 
      - assert (K0: c <+> (a <+> b <+> c) <+> a <+> b = e).
          rewrite H. rewrite inv_distr. rewrite <- assoc. rewrite inv_r. rewrite id_l. rewrite assoc. rewrite inv_l. reflexivity.
        rewrite <- assoc in K0. rewrite <- assoc in K0.
        rewrite assoc in K0. rewrite assoc in K0. apply inv_uniq_l in K0. rewrite <- assoc in K0. assumption.
Qed. (*notice that both proofs are almost the same; could they be reworked to be isomorphic?*)

Theorem ex_4_D_9 : forall a b : G,
    a = i a /\ b = i b 
 -> b <+> a = i (a <+> b).  
    Proof. intros a b H. destruct H.
      rewrite inv_distr. rewrite <- H. rewrite <- H0. reflexivity.
Qed.

Theorem ex_4_E_1 : forall 

End Ch4.
