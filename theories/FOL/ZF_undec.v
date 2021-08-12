Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.

From Undecidability.FOL.Util
     Require Import FullTarski FullDeduction_facts Aczel_CE Aczel_TD ZF_model HF_model.

From Undecidability.FOL.Reductions
     Require Import PCPb_to_HF PCPb_to_HFD PCPb_to_ZFeq PCPb_to_ZF PCPb_to_ZFD.

Require Import Undecidability.FOL.ZF.

From Undecidability.PCP
     Require Import PCP PCP_undec Util.PCP_facts Reductions.PCPb_iff_dPCPb.

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
  CE -> TD -> undecidable entailment_ZF.
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
  CE -> undecidable entailment_Z.
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
  CE -> undecidable entailment_ZF'.
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

Theorem PCPb_entailment_HF :
  (exists V (M : interp V), extensional M /\ PCPb_to_HF.standard M /\ forall rho psi, In psi HF -> rho ⊨ psi)
  -> reduction PCPb_to_HF.solvable PCPb entailment_HF.
Proof.
  intros H. intros B. apply PCP_HF. apply H.
Qed.

Theorem undecidable_entailment_HF :
  (exists V (M : interp V), extensional M /\ PCPb_to_HF.standard M /\ forall rho psi, In psi HF -> rho ⊨ psi)
  -> undecidable entailment_HF.
Proof.
  intros H. apply (undecidability_from_reducibility PCPb_undec).
  exists PCPb_to_HF.solvable. now apply PCPb_entailment_HF.
Qed.

Corollary undecidable_model_entailment_HF :
  undecidable entailment_HF.
Proof.
  intros H. apply undecidable_entailment_HF; trivial. apply HF_model.
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
  CE -> TD -> undecidable deduction_ZF.
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
  CE -> undecidable deduction_Z.
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

Corollary undecidable_deduction_entailment_ZF' :
  undecidable deduction_ZF'.
Proof.
  apply (undecidability_from_reducibility PCPb_undec), PCPb_deduction_ZF'.
Qed.

(* Intuitionistic deduction in HFeq *)

Theorem PCPb_deduction_HF :
  PCPb ⪯ deduction_HF.
Proof.
  exists PCPb_to_HF.solvable. intros B. split; try apply PCP_HFD.
  intros H % soundness. apply PCP_HF; try apply HF_model.
  intros D M rho H1 H2. apply H. intros phi [<-|[<-|[<-|[<-|H']]]].
  1-4: cbn; setoid_rewrite H1; congruence. now apply H2.
Qed.

Corollary undecidable_deduction_entailment_HF :
  undecidable deduction_HF.
Proof.
  apply (undecidability_from_reducibility PCPb_undec), PCPb_deduction_HF.
Qed.


