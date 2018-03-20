
Require Import List.

Inductive repeats : list Type -> Prop :=
| repeats_base : forall x l, In x l -> repeats (x :: l)
| repeats_recursive : forall x l, repeats (l) -> repeats (x :: l).


Axiom TE : forall (P : Prop), P \/ ~P.

Definition pigeon_hole : forall (l1 l2 : list Type) (x : Type), 
           (In x l1 -> In x l2) /\ (length l1 < length l2) ->
           repeats l1.
Proof.
  intros.
  destruct H.
  
Qed.