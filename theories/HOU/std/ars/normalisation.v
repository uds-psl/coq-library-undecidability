Set Implicit Arguments.
From Undecidability.HOU Require Import std.ars.basic.

(* Strong normalisation *)
Section StrongNormalisation.

  Variables (X : Type).
  Variables (R: X -> X -> Prop).

  Fact Normal_star_stops x:
    Normal R x -> forall y, star R x y -> x = y.
  Proof.
    destruct 2; firstorder.
  Qed.

End StrongNormalisation.
