Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.FOL.ZF.
Require Import Undecidability.FOL.ZF_undec.
Require Import Undecidability.FOL.binZF.
From Undecidability.FOL.Util Require Import FullTarski FullDeduction_facts Aczel_CE ZF_model.
From Undecidability.FOL.Reductions Require Import PCPb_to_ZF PCPb_to_ZFD PCPb_to_binZF.

From Undecidability.PCP Require Import PCP PCP_undec Util.PCP_facts Reductions.PCPb_iff_dPCPb.

Theorem PCPb_entailment_binZF :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, In psi ZF' -> rho ⊨ psi) -> PCPb ⪯ entailment_binZF.
Proof.
  intros (V & M & H1 & H2 & H3).
  exists (fun B => rm_const_fm (solvable B)). intros B. split; intros H.
  - intros V' M' rho' HM. apply (@PCP_ZFD intu), (@rm_const_prv intu nil), soundness in H.
    apply H; trivial. apply HM.
  - specialize (H V (@min_model V M) (fun _ => ∅)).
    rewrite <- min_correct in H; trivial. rewrite PCPb_iff_dPCPb.
    eapply PCP_ZF2 in H2 as [s Hs]; trivial; try apply H; trivial. now exists s.
    now apply min_axioms'.
Qed.

Theorem undecidable_entailment_binZF :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, In psi ZF' -> rho ⊨ psi) -> undecidable entailment_binZF.
Proof.
  intros H. now apply (undecidability_from_reducibility PCPb_undec), PCPb_entailment_binZF.
Qed.

Corollary undecidable_model_entailment_binZF :
  CE -> undecidable entailment_binZF.
Proof.
  intros H. now apply undecidable_entailment_binZF, extensionality_model.
Qed.

Theorem PCPb_deduction_binZF :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, In psi ZF' -> rho ⊨ psi) -> PCPb ⪯ deduction_binZF.
Proof.
  intros (V & M & H1 & H2 & H3).
  exists (fun B => rm_const_fm (solvable B)). intros B. split; intros H.
  - now apply (@PCP_ZFD intu), (@rm_const_prv intu nil) in H.
  - apply soundness in H. specialize (H V (@min_model V M) (fun _ => ∅)).
    rewrite <- min_correct in H; trivial. rewrite PCPb_iff_dPCPb.
    eapply PCP_ZF2 in H2 as [s Hs]; trivial; try apply H. now exists s.
    apply min_axioms'; auto.
Qed.

Theorem undecidable_deduction_binZF :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, In psi ZF' -> rho ⊨ psi) -> undecidable deduction_binZF.
Proof.
  intros H. now apply (undecidability_from_reducibility PCPb_undec), PCPb_deduction_binZF.
Qed.

Corollary undecidable_deduction_entailment_binZF :
  CE -> undecidable deduction_binZF.
Proof.
  intros H. now apply undecidable_deduction_binZF, extensionality_model.
Qed.
