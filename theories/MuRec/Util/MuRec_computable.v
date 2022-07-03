From Undecidability.MuRec Require Import MuRec.

From Coq Require Import List Vector Nat.
Import ListNotations Vector.VectorNotations.

Definition MuRec_computable {k} (R : Vector.t nat k -> nat -> Prop) := 
  exists f : recalg k, forall v : Vector.t nat k, 
        forall m, R v m <-> ra_bs f v m.

Definition functional {X Y} (R : X -> Y -> Prop) :=
  forall x y1 y2, R x y1 -> R x y2 -> y1 = y2.

Lemma MuRec_computable_functional_iff {k} (R : Vector.t nat k -> nat -> Prop) :
  functional R -> 
   MuRec_computable R <->
    exists f : recalg k, 
      (forall v m, ra_bs f v m -> R v m) /\
      (forall v m, R v m -> exists m, ra_bs f v m).
Proof.
  intros HR. split.
  - intros [f Hf]. exists f. split.
    + intros v m. eapply Hf.
    + intros. eexists. eapply Hf. eauto.
  - intros [f [Hf1 Hf2]]. exists f. intros v. split.
    + intros Hm. specialize (Hf2 _ _ Hm) as [m' Hm'].
      specialize (Hf1 _ _ Hm'). 
      enough (m = m') as -> by eauto.
      firstorder.
    + eauto.
Qed.