Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.

From Undecidability.FOL
     Require Import Semantics.Tarski.FullFacts Semantics.Tarski.FullSoundness.
From Undecidability.FOL.Axiomatizations.Sets.Models
     Require Import Aczel_CE Aczel_TD ZF_model HF_model.

From Undecidability.FOL.Undecidability.Reductions
     Require Import ZF_to_HF PCPb_to_HF PCPb_to_HFD PCPb_to_ZFeq PCPb_to_ZF PCPb_to_ZFD.

Require Import Undecidability.FOL.Axiomatizations.Sets.ZF.

From Undecidability.PCP
     Require Import PCP PCP_undec Util.PCP_facts Reductions.PCPb_iff_dPCPb.
Open Scope sem.

(* Semantic entailment in full ZF restricted to extensional models *)

Theorem PCPb_entailment_ZF :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZF psi -> rho ⊨ psi) -> reduction solvable PCPb entailment_ZF.
Proof.
  intros H. intros B. apply PCP_ZF. apply H.
Qed.

Theorem undecidable_entailment_ZF :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZF psi -> rho ⊨ psi) -> undecidable entailment_ZF.
Proof.
  intros H. apply (undecidability_from_reducibility PCPb_undec). exists solvable. now apply PCPb_entailment_ZF.
Qed.

Corollary undecidable_model_entailment_ZF :
  Aczel_CE.CE -> TD -> undecidable entailment_ZF.
Proof.
  intros H1 H2. now apply undecidable_entailment_ZF, normaliser_model.
Qed.

(* Semantic entailment in Z restricted to extensional models *)

Theorem PCPb_entailment_Z :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, Z psi -> rho ⊨ psi) -> reduction solvable PCPb entailment_Z.
Proof.
  intros H. intros B. apply PCP_Z. apply H.
Qed.

Theorem undecidable_entailment_Z :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, Z psi -> rho ⊨ psi) -> undecidable entailment_Z.
Proof.
  intros H. apply (undecidability_from_reducibility PCPb_undec). exists solvable. now apply PCPb_entailment_Z.
Qed.

Corollary undecidable_model_entailment_Z :
  Aczel_CE.CE -> undecidable entailment_Z.
Proof.
  intros H. now apply undecidable_entailment_Z, extensionality_model.
Qed.

(* Semantic entailment in ZF' restricted to extensional models *)

Theorem PCPb_entailment_ZF' :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, In psi ZF' -> rho ⊨ psi) -> reduction solvable PCPb entailment_ZF'.
Proof.
  intros H. intros B. apply PCP_ZF'. apply H.
Qed.

Theorem undecidable_entailment_ZF' :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, In psi ZF' -> rho ⊨ psi) -> undecidable entailment_ZF'.
Proof.
  intros H. apply (undecidability_from_reducibility PCPb_undec). exists solvable. now apply PCPb_entailment_ZF'.
Qed.

Corollary undecidable_model_entailment_ZF' :
  Aczel_CE.CE -> undecidable entailment_ZF'.
Proof.
  intros H. apply undecidable_entailment_ZF'.
  destruct extensionality_model as (V & M & H1 & H2 & H3); trivial.
  exists V, M. eauto using Z.
Qed.

(* Semantic entailment in ZFeq' allowing intensional models *)

Theorem PCPb_entailment_ZFeq' :
  PCPb ⪯ entailment_ZFeq'.
Proof.
  exists solvable. intros B. split; intros H.
  - eapply PCP_ZFD, soundness in H. intros D M rho H'. apply H, H'.
  - now apply PCP_ZFeq'; try apply intensional_model.
Qed.

Theorem undecidable_entailment_ZFeq' :
  undecidable entailment_ZFeq'.
Proof.
  apply (undecidability_from_reducibility PCPb_undec), PCPb_entailment_ZFeq'.
Qed.

(* Semantic entailment in HF restricted to extensional models *)

Theorem undecidable_entailment_HF' :
  Aczel_CE.CE -> undecidable entailment_HF.
Proof.
  intros ce. apply (undecidability_from_reducibility (undecidable_model_entailment_ZF' ce)).
  exists add_om. intros phi. apply reduction_entailment.
Qed.

Theorem undecidable_entailment_HF :
  undecidable entailment_HF.
Proof.
  apply (undecidability_from_reducibility PCPb_undec).
  exists PCPb_to_HF.solvable. intros phi. apply PCP_HF. apply HF_model.
Qed.

Theorem undecidable_entailment_HFN :
  undecidable entailment_HFN.
Proof.
  apply (undecidability_from_reducibility PCPb_undec).
  exists PCPb_to_HF.solvable. intros phi. rewrite PCPb_iff_dPCPb. split; intros H.
  - destruct H as [s H]. intros M HM rho H1 H2. eapply PCP_HF1; eauto.
    intros sigma psi Hp. apply H2. now right.
  - destruct HFN_model as (M & H1 & H2 & H3 & H4).
    specialize (H M H1 (fun _ => @i_func _ _ _ _ eset Vector.nil) H2 H4).
    apply PCP_HF2 in H as [s Hs]; trivial. now exists s.
    intros sigma psi Hp. apply H4. now right.                                             
Qed.

(* Intuitionistic deduction in full ZFeq *)

Theorem PCPb_deduction_ZF :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZF psi -> rho ⊨ psi) -> reduction solvable PCPb deduction_ZF.
Proof.
  intros (V & M & H1 & H2 & H3).
  intros B. split.
  - intros H % (@PCP_ZFD intu). exists ZFeq'. split; eauto using ZFeq.
  - intros H'. specialize (tsoundness H'). clear H'. intros H'.
    apply PCPb_iff_dPCPb. eapply PCP_ZF2; eauto using ZF.
    apply (H' V M (fun _ => ∅)). intros psi [].
    + apply extensional_eq; eauto using ZF.
    + apply H3. constructor 2.
    + apply H3. constructor 3.
Qed.

Theorem undecidable_deduction_ZF :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZF psi -> rho ⊨ psi) -> undecidable deduction_ZF.
Proof.
   intros H. apply (undecidability_from_reducibility PCPb_undec). exists solvable. now apply PCPb_deduction_ZF.
Qed.

Corollary undecidable_model_deduction_ZF :
  Aczel_CE.CE -> TD -> undecidable deduction_ZF.
Proof.
  intros H1 H2. now apply undecidable_deduction_ZF, normaliser_model.
Qed.

(* Intuitionistic deduction in ZFeq *)

Theorem PCPb_deduction_Z :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, Z psi -> rho ⊨ psi) -> reduction solvable PCPb deduction_Z.
Proof.
  intros (V & M & H1 & H2 & H3).
  intros B. split.
  - intros H % (@PCP_ZFD intu). exists ZFeq'. split; eauto using Zeq.
  - intros H'. specialize (tsoundness H'). clear H'. intros H'.
    apply PCPb_iff_dPCPb. eapply PCP_ZF2; eauto using Z.
    apply (H' V M (fun _ => ∅)). intros psi [].
    + apply extensional_eq; eauto using Z.
    + apply H3. constructor 2.
Qed.

Theorem undecidable_deduction_Z :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, Z psi -> rho ⊨ psi) -> undecidable deduction_Z.
Proof.
   intros H. apply (undecidability_from_reducibility PCPb_undec). exists solvable. now apply PCPb_deduction_Z.
Qed.

Corollary undecidable_model_deduction_Z :
  Aczel_CE.CE -> undecidable deduction_Z.
Proof.
  intros H. now apply undecidable_deduction_Z, extensionality_model.
Qed.

(* Intuitionistic deduction in ZFeq' *)

Theorem PCPb_deduction_ZF' :
  PCPb ⪯ deduction_ZF'.
Proof.
  exists solvable. intros B. split; try apply PCP_ZFD.
  intros H' % soundness. apply PCP_ZFeq'; try apply intensional_model.
  intros D M rho H. apply H', H.
Qed.

Corollary undecidable_deduction_ZF' :
  undecidable deduction_ZF'.
Proof.
  apply (undecidability_from_reducibility PCPb_undec), PCPb_deduction_ZF'.
Qed.

(* Intuitionistic deduction in HFeq *)

Theorem undecidable_deduction_HF :
  undecidable deduction_HF.
Proof.
  apply (undecidability_from_reducibility undecidable_deduction_ZF').
  exists add_om. intros phi. apply reduction_deduction.
Qed.

Theorem undecidable_deduction_HFN :
  undecidable deduction_HFN.
Proof.
  apply (undecidability_from_reducibility PCPb_undec).
  exists PCPb_to_HF.solvable. intros B. split.
  - intros H. eapply Weak. try apply PCP_HFD; auto. intros phi Hp. firstorder.
  - intros H % soundness. destruct HFN_model as (M & H1 & H2 & H3 & H4).
    specialize (H M H1 (fun _ => @i_func _ _ _ _ eset Vector.nil)).
    eapply PCPb_iff_dPCPb, PCP_HF2; try apply H; trivial.
    + intros rho phi Hp. apply H4. now right.
    + intros phi [<-|[<-|[<-|[<-|Hp]]]]; try now apply H4.
      all: cbn; setoid_rewrite H2; congruence.
Qed.


