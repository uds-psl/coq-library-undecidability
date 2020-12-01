Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.PCP.PCP_undec.
Require Import Undecidability.FOL.ZF.
From Undecidability.FOL.Reductions Require PCPb_to_ZF.

From Undecidability Require Export PCP.PCP PCP.Util.PCP_facts.
Require Import Undecidability.PCP.Reductions.PCPb_iff_dPCPb.

Theorem PCP_ZF B :
  (exists M : ZF_Model, extensional M /\ standard M) -> PCPb B <-> entailment_ZF (solvable B).
Proof.
  intros HZF. rewrite PCPb_iff_dPCPb. split; intros H.
  - destruct H as [s H]. intros M HM. eapply PCP_ZF1; eauto.
  - destruct HZF as [M[H1 H2]]. specialize (H M H1 (fun _ => @i_func _ _ _ _ eset Vector.nil)).
    apply PCP_ZF2 in H as [s Hs]; trivial. now exists s.
Qed.

Lemma extnorm_stanmod :
  inhabited extensional_normaliser -> exists M : ZF_Model, extensional M /\ standard M.
Proof.
  intros [H]. exists SET_ZF. split.
  - apply SET_ext.
  - apply SET_standard.
Qed.

Corollary PCP_ZF' B :
  inhabited extensional_normaliser -> BPCP' B <-> ZF_entails (solvable B).
Proof.
  intros H % extnorm_stanmod. now apply PCP_ZF.
Qed.

Lemma undecidable_ZF_entailment :
  undecidable ZF_entailment.
Proof.
   
Qed.

Lemma undecidable_FOLstar_valid : undecidable FOL*_valid.
Proof.
   apply (undecidability_from_reducibility PCPb_undec).
   apply PCPb_to_FOL.valid_star_red.
Qed.

Lemma undecidable_FOL_valid : undecidable FOL_valid.
Proof.
   apply (undecidability_from_reducibility PCPb_undec).
   apply PCPb_to_FOL.valid_red.
Qed.

(*Lemma undecidable_FOL_satis : undecidable FOL_satis.
Proof.
  apply (undecidability_from_reducibility PCPb_undec).
  
Qed.*)

Lemma undecidable_FOL_valid_intu : undecidable FOL_valid_intu.
Proof.
   apply (undecidability_from_reducibility PCPb_undec).
   apply PCPb_to_FOL_intu.kvalid_red.
Qed.

Lemma undecidable_FOL_prv_intu : undecidable FOL_prv_intu.
Proof.
   apply (undecidability_from_reducibility PCPb_undec).
   apply PCPb_to_FOL_intu.kprv_red.
Qed.

(* Lemma undecidable_FOL_satis_intu : undecidable FOL_satis_intu.
Proof.
   apply (undecidability_from_reducibility PCPb_undec).
   apply PCPb_to_FOL.ksatis_red.
Qed. *)

Lemma undecidable_FOL_prv_class : undecidable FOL_prv_class.
Proof.
   apply (undecidability_from_reducibility PCPb_undec).
   apply PCPb_to_FOL_class.cprv_red.
Qed.
