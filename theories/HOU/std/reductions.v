Set Implicit Arguments.
Require Import Lia List.
From Undecidability.HOU Require Import std.lists.basics std.misc std.decidable.
Import ListNotations.

Section Reductions.

  Variable (X Y Z: Type).
  Implicit Types (P: X -> Prop) (Q: Y -> Prop) (R: Z -> Prop).

  Definition reduction {X Y: Type} (P: X -> Prop) (Q: Y -> Prop) :=
    exists f, forall x, P x <-> Q (f x).
  
  Notation "P ⪯ Q" := (reduction P Q) (at level 60).
  
  Lemma reduction_transitive P Q R:
    P ⪯ Q -> Q ⪯ R -> P ⪯ R.
  Proof.
    intros [f H1] [g H2]; exists (f >> g).
    intros x; rewrite H1, H2. reflexivity.
  Qed.
  
  Lemma reduction_reflexive P: P ⪯ P.
  Proof.
    exists id; reflexivity.
  Qed.


End Reductions.

#[export] Hint Resolve reduction_reflexive reduction_transitive : core.
Notation "P ⪯ Q" := (reduction P Q) (at level 60).
