Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.PCP.PCP_undec.
From Undecidability.FOL.Undecidability Require Import binZF_undec FOL.
From Undecidability.FOL.Sets Require Import binZF.
Require Import Undecidability.FOL.Syntax.Core.
Require Import Undecidability.FOL.Syntax.BinSig.
Require Import Undecidability.FOL.Semantics.Tarski.FullFacts.
Require Import Undecidability.FOL.Deduction.FullNDFacts.

Lemma binZF_binFOL_valid :
  entailment_binZF ⪯ binFOL_valid.
Proof.
  exists (impl binZF). intros phi. unfold binFOL_valid, valid, entailment_binZF.
  setoid_rewrite impl_sat. reflexivity.
Qed.

Lemma binFOL_valid_undec :
  undecidable binFOL_valid.
Proof.
  apply (undecidability_from_reducibility undecidable_entailment_binZF), binZF_binFOL_valid.
Qed.

Lemma binZF_binFOL_prv_intu :
  deduction_binZF ⪯ binFOL_prv_intu.
Proof.
  exists (impl binZF). intros phi. unfold binFOL_prv_intu, deduction_binZF.
  setoid_rewrite <- impl_prv. rewrite List.app_nil_r.
  split; intros H; apply (Weak H); unfold List.incl; apply List.in_rev.
Qed.

Lemma binFOL_prv_intu_undec :
  undecidable binFOL_prv_intu.
Proof.
  apply (undecidability_from_reducibility undecidable_deduction_binZF), binZF_binFOL_prv_intu.
Qed.
