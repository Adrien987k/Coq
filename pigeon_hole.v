
Require Import List.

Inductive repeats : list Type -> Prop :=
| repeats_base : forall x l, In x l -> repeats (x :: l)
| repeats_recursive : forall x l, repeats (l) -> repeats (x :: l).


Axiom TE : forall (P : Prop), P \/ ~P.

Lemma aux : forall (x a : Type) l1 l2, x <> a -> In x (l1 ++ (a :: l2)) -> In x (l1 ++ l2).
Proof.

Admitted.

Definition pigeon_hole : forall (l1 l2 : list Type) (x : Type), 
           (In x l1 -> In x l2) /\ (length l2 < length l1) ->
           repeats l1. 
Proof.
  intro.
  induction l1.
  - easy. 
  - destruct (TE (In a l1)).
    + constructor 1.
      easy.
    + constructor 2.
      destruct H0.

      destruct (TE (x=a)).
      * subst.
        rewrite H2.
        intro.
        rewrite H2 in H.
        (* pose proof (H (List.in_eq a l1)). *)
        apply H.
        apply List.in_eq.
        (* assert (In a (a :: l1)).
        apply List.in_eq. *) (* Deux autres façons de faire *)
        subst.
      * 
Qed.





















