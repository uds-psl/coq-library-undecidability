Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.FOL.ZF.
Require Import Undecidability.FOL.ZF_undec.
Require Import Undecidability.FOL.minZF.
From Undecidability.FOL.Util Require Import FullTarski FullDeduction_facts Aczel_CE Aczel_TD ZF_model.
From Undecidability.FOL.Reductions Require Import PCPb_to_ZF PCPb_to_ZFD PCPb_to_minZF.

From Undecidability.PCP Require Import PCP PCP_undec Util.PCP_facts Reductions.PCPb_iff_dPCPb.

Theorem PCPb_entailment_minZF :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZF psi -> rho ⊨ psi) -> PCPb ⪯ entailment_minZF.
Proof.
  intros (V & M & H1 & H2 & H3).
  exists (fun B => rm_const_fm (solvable B)). intros B. split; intros H.
  - intros V' M' rho' HM1 HM2. apply (@PCP_ZFD intu), (@rm_const_prv intu nil), soundness in H.
    apply H, extensional_eq_min'; trivial. eauto using minZF.
  - specialize (H V (@min_model V M) (fun _ => ∅)).
    rewrite <- min_correct in H; trivial; eauto using ZF. rewrite PCPb_iff_dPCPb.
    eapply PCP_ZF2 in H2 as [s Hs]; trivial; try apply H; eauto using ZF. now exists s.
    apply min_axioms; eauto using ZF.
Qed.

Theorem undecidable_entailment_minZF :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZF psi -> rho ⊨ psi) -> undecidable entailment_minZF.
Proof.
   intros H. now apply (undecidability_from_reducibility PCPb_undec), PCPb_entailment_minZF.
Qed.

Theorem PCPb_entailment_minZF' :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, In psi ZF' -> rho ⊨ psi) -> PCPb ⪯ entailment_minZF'.
Proof.
  intros (V & M & H1 & H2 & H3).
  exists (fun B => rm_const_fm (solvable B)). intros B. split; intros H.
  - intros V' M' rho' HM1 HM2. apply (@PCP_ZFD intu), (@rm_const_prv intu nil), soundness in H.
    apply H, extensional_eq_min'; trivial. apply HM2.
  - specialize (H V (@min_model V M) (fun _ => ∅)).
    rewrite <- min_correct in H; trivial. rewrite PCPb_iff_dPCPb.
    eapply PCP_ZF2 in H2 as [s Hs]; trivial; try apply H; trivial. now exists s.
    now apply min_axioms'.
Qed.

Theorem undecidable_entailment_minZF' :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, In psi ZF' -> rho ⊨ psi) -> undecidable entailment_minZF'.
Proof.
  intros H. now apply (undecidability_from_reducibility PCPb_undec), PCPb_entailment_minZF'.
Qed.

Corollary undecidable_model_entailment_minZF :
  CE -> TD -> undecidable entailment_minZF.
Proof.
  intros H1 H2. now apply undecidable_entailment_minZF, normaliser_model.
Qed.

Corollary undecidable_model_entailment_minZF' :
  CE -> undecidable entailment_minZF'.
Proof.
  intros H. now apply undecidable_entailment_minZF', extensionality_model.
Qed.

Theorem PCPb_deduction_minZF :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZF psi -> rho ⊨ psi) -> PCPb ⪯ deduction_minZF.
Proof.
  intros (V & M & H1 & H2 & H3).
  exists (fun B => rm_const_fm (solvable B)). intros B. split; intros H.
  - exists minZFeq'. split; auto using minZFeq. now apply (@PCP_ZFD intu), (@rm_const_prv intu nil) in H.
  - eapply tsoundness with (I := @min_model V M) (rho := fun _ => ∅) in H.
    rewrite <- min_correct in H; trivial; auto using ZF. rewrite PCPb_iff_dPCPb.
    eapply PCP_ZF2 in H2 as [s Hs]; trivial; try apply H; auto using ZF. now exists s.
    apply extensional_eq_min; auto. apply min_axioms; auto using ZF.
Qed.

Theorem undecidable_deduction_minZF :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZF psi -> rho ⊨ psi) -> undecidable deduction_minZF.
Proof.
  intros H. now apply (undecidability_from_reducibility PCPb_undec), PCPb_deduction_minZF.
Qed.

Theorem PCPb_deduction_minZF' :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, In psi ZF' -> rho ⊨ psi) -> PCPb ⪯ deduction_minZF'.
Proof.
  intros (V & M & H1 & H2 & H3).
  exists (fun B => rm_const_fm (solvable B)). intros B. split; intros H.
  - now apply (@PCP_ZFD intu), (@rm_const_prv intu nil) in H.
  - apply soundness in H. specialize (H V (@min_model V M) (fun _ => ∅)).
    rewrite <- min_correct in H; trivial. rewrite PCPb_iff_dPCPb.
    eapply PCP_ZF2 in H2 as [s Hs]; trivial; try apply H. now exists s.
    apply extensional_eq_min', min_axioms'; auto.
Qed.

Theorem undecidable_deduction_minZF' :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, In psi ZF' -> rho ⊨ psi) -> undecidable deduction_minZF'.
Proof.
  intros H. now apply (undecidability_from_reducibility PCPb_undec), PCPb_deduction_minZF'.
Qed.

Corollary undecidable_model_deduction_minZF :
  CE -> TD -> undecidable deduction_minZF.
Proof.
  intros H1 H2. now apply undecidable_deduction_minZF, normaliser_model.
Qed.

Corollary undecidable_deduction_entailment_minZF' :
  CE -> undecidable deduction_minZF'.
Proof.
  intros H. now apply undecidable_deduction_minZF', extensionality_model.
Qed.
