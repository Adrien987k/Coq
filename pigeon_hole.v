
Require Import List.

Inductive repeats : list Type -> Prop :=
| repeats_base : forall x l, In x l -> repeats (x :: l)
| repeats_recursive : forall x l, repeats (l) -> repeats (x :: l).


Axiom TE : forall (P : Prop), P \/ ~P.

Definition pigeon_hole : forall (l1 l2 : list Type) (x : Type), 
           (In x l1 -> In x l2) /\ (length l2 < length l1) ->
           repeats l1. 
Proof.
  intros.
  destruct H.
  induction l1.
  - easy. 
  - destruct (TE (In a l1)).
    + constructor 1.
      easy.
    + constructor 2.
      destruct (TE (x=a)).
      * apply IHl1.
        rewrite H2.
        intro.
        rewrite H2 in H.
        (* pose proof (H (List.in_eq a l1)). *)
        apply H.
        apply List.in_eq.
        (* assert (In a (a :: l1)).
        apply List.in_eq. *) (* Deux autres façons de faire *)
        
Qed.