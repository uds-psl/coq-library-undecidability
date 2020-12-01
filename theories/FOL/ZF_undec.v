Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
From Undecidability.FOL Require Import ZF Util.FullTarski Util.Aczel Util.ZF_model Reductions.PCPb_to_ZF.
From Undecidability.PCP Require Import PCP PCP_undec Util.PCP_facts Reductions.PCPb_iff_dPCPb.

Lemma undecidable_entailment_ZF :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZF psi -> rho ⊨ psi) -> undecidable entailment_ZF.
Proof.
   intros H. apply (undecidability_from_reducibility PCPb_undec).
   exists solvable. intros B. apply PCP_ZF. apply H.
Qed.

Lemma undecidable_entailment_ZF' :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, In psi ZF' -> rho ⊨ psi) -> undecidable entailment_ZF'.
Proof.
   intros H. apply (undecidability_from_reducibility PCPb_undec).
   exists solvable. intros B. apply PCP_ZF'. apply H.
Qed.

Corollary undecidable_model_entailment_ZF :
  inhabited extensional_normaliser -> undecidable entailment_ZF.
Proof.
  intros [H]. apply undecidable_entailment_ZF.
  exists SET, SET_interp. split; try apply SET_ext.
  split; try apply SET_standard. intros rho psi [].
  - now apply SET_ZF'.
  - apply SET_sep.
  - apply SET_rep.
Qed.

Corollary undecidable_model_entailment_ZF' :
  inhabited extensional_normaliser -> undecidable entailment_ZF'.
Proof.
  intros [H]. apply undecidable_entailment_ZF'.
  exists SET, SET_interp. split; try apply SET_ext.
  split; try apply SET_standard. apply SET_ZF'.
Qed.


