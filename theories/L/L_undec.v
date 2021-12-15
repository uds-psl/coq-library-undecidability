Require Import Undecidability.L.L.
Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.Synthetic Require Import
  DecidabilityFacts EnumerabilityFacts.
Require Import Undecidability.L.Enumerators.term_enum.

(** ** complement HaltL is undecidable *)

Lemma complement_HaltL_undec :
  undecidable (complement HaltL).
Proof.
  intros H.
  now eapply (dec_count_enum H), enumerator_enumerable, enumerator__T_term.
Qed.

(** ** HaltL is undecidable *)

Lemma HaltL_undec :
  undecidable (HaltL).
Proof.
  intros H. now apply complement_HaltL_undec, dec_compl.
Qed.
