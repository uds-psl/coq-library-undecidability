Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.FOL.ZF.
Require Import Undecidability.FOL.ZF_undec.
Require Import Undecidability.FOL.binZF.
From Undecidability.FOL.Util Require Import FullTarski FullDeduction_facts ZF_model.
From Undecidability.FOL.Reductions Require Import PCPb_to_ZF PCPb_to_ZFeq PCPb_to_ZFD PCPb_to_binZF.

From Undecidability.PCP Require Import PCP PCP_undec Util.PCP_facts Reductions.PCPb_iff_dPCPb.

Theorem PCPb_entailment_binZF :
  reduction binsolvable PCPb entailment_binZF.
Proof.
  intros B. split; intros H.
  - intros V' M' rho' HM. apply (@PCP_ZFD intu), (@rm_const_prv intu nil), soundness in H. apply H; trivial.
  - apply PCP_ZFeq'; try apply intensional_model.
    intros V M rho HM. apply min_correct; trivial.
    apply H. now apply min_axioms'.
Qed.

Corollary undecidable_entailment_binZF :
  undecidable entailment_binZF.
Proof.
  apply (undecidability_from_reducibility PCPb_undec). exists binsolvable. apply PCPb_entailment_binZF.
Qed.

Theorem PCPb_deduction_binZF :
  reduction binsolvable PCPb deduction_binZF.
Proof.
  intros B. split; intros H.
  - now apply (@PCP_ZFD intu), (@rm_const_prv intu nil) in H.
  - apply PCP_ZFeq'; try apply intensional_model. apply soundness in H.
    intros V M rho HM. apply min_correct; trivial.
    apply H. now apply min_axioms'.
Qed.

Theorem undecidable_deduction_binZF :
  undecidable deduction_binZF.
Proof.
  apply (undecidability_from_reducibility PCPb_undec). exists binsolvable. apply PCPb_deduction_binZF.
Qed.
