Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.FOL.ZF.
From Undecidability.FOL.Util Require Import FullTarski FullDeduction Aczel ZF_model.
From Undecidability.FOL.Reductions Require Import PCPb_to_ZF PCPb_to_ZFD.

From Undecidability.PCP Require Import PCP PCP_undec Util.PCP_facts Reductions.PCPb_iff_dPCPb.

Theorem undecidable_entailment_ZF :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZF psi -> rho ⊨ psi) -> undecidable entailment_ZF.
Proof.
   intros H. apply (undecidability_from_reducibility PCPb_undec).
   exists solvable. intros B. apply PCP_ZF. apply H.
Qed.

Theorem undecidable_entailment_ZF' :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, In psi ZF' -> rho ⊨ psi) -> undecidable entailment_ZF'.
Proof.
   intros H. apply (undecidability_from_reducibility PCPb_undec).
   exists solvable. intros B. apply PCP_ZF'. apply H.
Qed.

Lemma normaliser_model :
  inhabited extensional_normaliser -> exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZF psi -> rho ⊨ psi.
Proof.
  intros [H]. exists SET, SET_interp. split; try apply SET_ext.
  split; try apply SET_standard. intros rho psi [].
  - now apply SET_ZF'.
  - apply SET_sep.
  - apply SET_rep.
Qed.

Corollary undecidable_model_entailment_ZF :
  inhabited extensional_normaliser -> undecidable entailment_ZF.
Proof.
  intros H. now apply undecidable_entailment_ZF, normaliser_model.
Qed.

Corollary undecidable_model_entailment_ZF' :
  inhabited extensional_normaliser -> undecidable entailment_ZF'.
Proof.
  intros (V & M & H1 & H2 & H3) % normaliser_model. apply undecidable_entailment_ZF'.
  exists V, M. split; trivial. split; trivial. eauto using ZF.
Qed.

Lemma extensional_eq V (M : interp V) rho :
  extensional M -> rho ⊫ ZF' -> rho ⊫ ZFeq'.
Proof.
  intros H1 H2 phi [<-|[<-|[<-|[<-|H]]]]; try now apply H2.
  all: cbn; intros; rewrite !H1 in *; congruence.
Qed.

Theorem undecidable_deduction_ZF :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZF psi -> rho ⊨ psi) -> undecidable deduction_ZF.
Proof.
   intros (V & M & H1 & H2 & H3).
   apply (undecidability_from_reducibility PCPb_undec).
   exists solvable. intros B. split.
   - intros H % (@PCP_ZFD intu). exists ZFeq'. split; eauto using ZFeq.
   - intros H'. specialize (tsoundness H'). clear H'. intros H'.
     apply PCPb_iff_dPCPb. eapply PCP_ZF2; eauto using ZF.
     apply (H' V M (fun _ => ∅)). intros psi [].
     + apply extensional_eq; eauto using ZF.
     + apply H3. constructor 2.
     + apply H3. constructor 3.
Qed.

Theorem undecidable_deduction_ZF' :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, In psi ZF' -> rho ⊨ psi) -> undecidable deduction_ZF'.
Proof.
   intros (V & M & H1 & H2 & H3).
   apply (undecidability_from_reducibility PCPb_undec).
   exists solvable. intros B. split; try apply PCP_ZFD.
   intros H' % soundness. apply PCPb_iff_dPCPb. eapply PCP_ZF2; trivial.
   apply (H' V M (fun _ => ∅)). apply extensional_eq; auto.
Qed.

Corollary undecidable_model_deduction_ZF :
  inhabited extensional_normaliser -> undecidable deduction_ZF.
Proof.
  intros H. now apply undecidable_deduction_ZF, normaliser_model.
Qed.

Corollary undecidable_deduction_entailment_ZF' :
  inhabited extensional_normaliser -> undecidable deduction_ZF'.
Proof.
  intros (V & M & H1 & H2 & H3) % normaliser_model. apply undecidable_deduction_ZF'.
  exists V, M. split; trivial. split; trivial. eauto using ZF.
Qed.


