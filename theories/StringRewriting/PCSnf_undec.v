
Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.StringRewriting.PCSnf.
Require Import Undecidability.SR.SR_undec.

From Undecidability.StringRewriting.Reductions Require SR_to_PCSnf.

(** String rewriting for Post canonical systems in normal form is undecidable. *)
Lemma PCSnf_undec : undecidable PCSnf.
Proof.
  apply (undecidability_from_reducibility SR_undec).
  exact SR_to_PCSnf.
Qed.

Check PCSnf_undec.
