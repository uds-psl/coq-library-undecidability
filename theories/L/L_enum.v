Require Import Undecidability.L.L Undecidability.L.Enumerators.HaltL_enum.
Require Import Undecidability.Synthetic.Definitions.

(* ** HaltL is enumerable *)

Lemma HaltL_enum :
  enumerable (HaltL).
Proof.
  exists HaltL_enumerator.
  exact HaltL_enumerator_spec.
Qed.
