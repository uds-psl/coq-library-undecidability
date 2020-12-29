Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.FOL.ZF.
Require Import Undecidability.FOL.ZF_undec.
Require Import Undecidability.FOL.minZF.
From Undecidability.FOL.Util Require Import FullTarski FullDeduction Aczel ZF_model.
From Undecidability.FOL.Reductions Require Import PCPb_to_ZF PCPb_to_ZFD PCPb_to_minZF.

From Undecidability.PCP Require Import PCP PCP_undec Util.PCP_facts Reductions.PCPb_iff_dPCPb.

Lemma PCP_minZF_prv' { p : peirce } B :
  PCPb B -> minZFeq' ⊢ rm_const_fm (solvable B).
Proof.
  intros H. apply (@rm_const_prv p nil), PCP_ZFD, H.
Qed.

Lemma extensional_eq_min' V (M : @interp sig_empty _ V) rho :
  extensional M -> rho ⊫ minZF' -> rho ⊫ minZFeq'.
Proof.
  intros H1 H2 phi [<-|[<-|[<-|[<-|H]]]]; try now apply H2.
  all: cbn; intros; rewrite !H1 in *; congruence.
Qed.

Lemma extensional_eq_min V (M : @interp sig_empty _ V) rho :
  extensional M -> (forall phi, minZF phi -> rho ⊨ phi) -> (forall phi, minZFeq phi -> rho ⊨ phi).
Proof.
  intros H1 H2 phi []; try now apply H2; auto using minZF.
  apply extensional_eq_min'; auto using minZF.
Qed.

Theorem undecidable_entailment_minZF :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZF psi -> rho ⊨ psi) -> undecidable entailment_minZF.
Proof.
   intros (V & M & H1 & H2 & H3). apply (undecidability_from_reducibility PCPb_undec).
   exists (fun B => rm_const_fm (solvable B)). intros B. split; intros H.
   - intros V' M' rho' HM1 HM2. apply (@PCP_minZF_prv' intu), soundness in H.
     apply H, extensional_eq_min'; trivial. eauto using minZF.
  - specialize (H V (@min_model V M) (fun _ => ∅)).
    rewrite <- min_correct in H; trivial; eauto using ZF. rewrite PCPb_iff_dPCPb.
    eapply PCP_ZF2 in H2 as [s Hs]; trivial; try apply H; eauto using ZF. now exists s.
    apply min_axioms; eauto using ZF.
Qed.

Theorem undecidable_entailment_minZF' :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, In psi ZF' -> rho ⊨ psi) -> undecidable entailment_minZF'.
Proof.
  intros (V & M & H1 & H2 & H3). apply (undecidability_from_reducibility PCPb_undec).
  exists (fun B => rm_const_fm (solvable B)). intros B. split; intros H.
  - intros V' M' rho' HM1 HM2. apply (@PCP_minZF_prv' intu), soundness in H.
    apply H, extensional_eq_min'; trivial. apply HM2.
  - specialize (H V (@min_model V M) (fun _ => ∅)).
    rewrite <- min_correct in H; trivial. rewrite PCPb_iff_dPCPb.
    eapply PCP_ZF2 in H2 as [s Hs]; trivial; try apply H; trivial. now exists s.
    now apply min_axioms'.
Qed.

Corollary undecidable_model_entailment_minZF :
  inhabited extensional_normaliser -> undecidable entailment_minZF.
Proof.
  intros H. now apply undecidable_entailment_minZF, normaliser_model.
Qed.

Corollary undecidable_model_entailment_minZF' :
  inhabited extensional_normaliser -> undecidable entailment_minZF'.
Proof.
  intros (V & M & H1 & H2 & H3) % normaliser_model. apply undecidable_entailment_minZF'.
  exists V, M. split; trivial. split; trivial. eauto using ZF.
Qed.

Theorem undecidable_deduction_minZF :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZF psi -> rho ⊨ psi) -> undecidable deduction_minZF.
Proof.
  intros (V & M & H1 & H2 & H3).
  apply (undecidability_from_reducibility PCPb_undec).
  exists (fun B => rm_const_fm (solvable B)). intros B. split; intros H.
  - exists minZFeq'. split; auto using minZFeq. now apply PCP_minZF_prv'.
  - eapply tsoundness with (I := @min_model V M) (rho := fun _ => ∅) in H.
    rewrite <- min_correct in H; trivial; auto using ZF. rewrite PCPb_iff_dPCPb.
    eapply PCP_ZF2 in H2 as [s Hs]; trivial; try apply H; auto using ZF. now exists s.
    apply extensional_eq_min; auto. apply min_axioms; auto using ZF.
Qed.

Theorem undecidable_deduction_minZF' :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, In psi ZF' -> rho ⊨ psi) -> undecidable deduction_minZF'.
Proof.
  intros (V & M & H1 & H2 & H3).
  apply (undecidability_from_reducibility PCPb_undec).
  exists (fun B => rm_const_fm (solvable B)). intros B. split; intros H.
  - now apply PCP_minZF_prv'.
  - apply soundness in H. specialize (H V (@min_model V M) (fun _ => ∅)).
    rewrite <- min_correct in H; trivial. rewrite PCPb_iff_dPCPb.
    eapply PCP_ZF2 in H2 as [s Hs]; trivial; try apply H. now exists s.
    apply extensional_eq_min', min_axioms'; auto.
Qed.

Corollary undecidable_model_deduction_minZF :
  inhabited extensional_normaliser -> undecidable deduction_minZF.
Proof.
  intros H. now apply undecidable_deduction_minZF, normaliser_model.
Qed.

Corollary undecidable_deduction_entailment_minZF' :
  inhabited extensional_normaliser -> undecidable deduction_minZF'.
Proof.
  intros (V & M & H1 & H2 & H3) % normaliser_model. apply undecidable_deduction_minZF'.
  exists V, M. split; trivial. split; trivial. eauto using ZF.
Qed.

Print Assumptions undecidable_deduction_minZF.
