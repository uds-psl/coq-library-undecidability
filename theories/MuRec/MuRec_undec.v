Require Import Undecidability.MuRec.MuRec Undecidability.H10.H10.
Require Import Undecidability.MuRec.Reductions.H10_to_MUREC_HALTING.
Require Import Undecidability.H10.H10_undec.
Require Import Undecidability.Synthetic.Undecidability.

(** ** Halt_murec is undecidable *)

Lemma Halt_murec_undec :
  undecidable Halt_murec.
Proof.
  apply (undecidability_from_reducibility H10_undec).
  eapply H10_MUREC_HALTING.
Qed.
