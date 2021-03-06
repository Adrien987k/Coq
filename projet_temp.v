
Lemma NotnotP_andP : (forall (P : Prop), ~(~P /\ ~~P)).
Proof.
  intros.
  easy.
Qed.

Theorem modDeMorgan_imply_TE : (forall (P Q : Prop), ~(~P /\ ~Q) -> P \/ Q) 
                               -> (forall (P : Prop), P \/ ~ P).
Proof.
  intros.
  apply H.
  apply NotnotP_andP.
Qed.

Theorem TE_imply_modDN : (forall (P : Prop), P \/ ~P)
                         -> forall (P : Prop), (~P -> P) -> P.
Proof.
  intros.
  destruct (H P).
  + easy.
  + apply H0.
    apply H1.
Qed.

<<<<<<< HEAD
(* En coq, not P = p -> false *)
=======
Theorem modDN_imply_Pierce : (forall (P : Prop), (~P -> P) -> P)
                             -> (forall (P Q : Prop), ((P -> Q) -> P) -> P).
Proof.
  intros.
  
Qed.
>>>>>>> 00e85d079641e974cef87d45fe3b169c1e270f46
