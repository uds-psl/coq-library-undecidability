(* 
  Undecidability Result(s):
    Universal µ-recusive Algorithm Halting (RA_UNIV_HALT)
*)

Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.MuRec.RA_UNIV_HALT.

Require Import Undecidability.MuRec.Reductions.H10C_SAT_to_RA_UNIV_HALT.
Require Import Undecidability.DiophantineConstraints.H10C_undec.

(* Undecidability of Universal µ-recusive Algorithm Halting *)

Theorem PRIMEREC_UNIV_MEETS_ZERO_undec : undecidable PRIMEREC_UNIV_MEETS_ZERO.
Proof.
  apply (undecidability_from_reducibility H10C_SAT_undec).
  apply H10C_SAT_PRIMEREC_UNIV_MEETS_ZERO.
Qed.

Check PRIMEREC_UNIV_MEETS_ZERO_undec.

Theorem PRIMESEQ_MEETS_ZERO_undec : undecidable PRIMESEQ_MEETS_ZERO.
Proof.
  apply (undecidability_from_reducibility PRIMEREC_UNIV_MEETS_ZERO_undec).
  apply PRIMEREC_PRIMESEQ_MEETS_ZERO.
Qed.

Check PRIMESEQ_MEETS_ZERO_undec.

Theorem NATSEQ_MEETS_ZERO_undec : undecidable NATSEQ_MEETS_ZERO.
Proof.
  apply (undecidability_from_reducibility PRIMESEQ_MEETS_ZERO_undec).
  apply PRIMESEQ_NATSEQ_MEETS_ZERO.
Qed.

Check NATSEQ_MEETS_ZERO_undec.

Theorem BOOLSEQ_MEETS_TRUE_undec : undecidable BOOLSEQ_MEETS_TRUE.
Proof.
  apply (undecidability_from_reducibility NATSEQ_MEETS_ZERO_undec).
  apply reduces_dependent; exists.
  intros f.
  exists (fun n => match f n with 0 => true | _ => false end).
  split; intros (n & Hn); exists n.
  + now rewrite Hn.
  + now destruct (f n).
Qed.

Check BOOLSEQ_MEETS_TRUE_undec.

Theorem RA_UNIV_HALT_undec : undecidable RA_UNIV_HALT.
Proof.
  apply (undecidability_from_reducibility PRIMEREC_UNIV_MEETS_ZERO_undec).
  exact H10C_SAT_to_RA_UNIV_HALT.PRIMEREC_UNIV_MEETS_ZERO_RA_UNIV_HALT.
Qed.

Check RA_UNIV_HALT_undec.

Theorem RA_UNIV_AD_HALT_undec : undecidable RA_UNIV_AD_HALT.
Proof.
  apply (undecidability_from_reducibility H10UC_SAT_undec).
  exact H10C_SAT_to_RA_UNIV_HALT.H10UC_SAT_RA_UNIV_AD_HALT.
Qed.

Check RA_UNIV_AD_HALT_undec.