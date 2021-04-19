From Equations Require Import Equations DepElim.
From Undecidability.Shared Require Import Dec.
From Undecidability.FOL Require Import Util.Syntax Util.FullDeduction Util.FullTarski ZF.
From Undecidability.FOL Require Import Reductions.PCPb_to_ZF minZF Reductions.PCPb_to_minZF.
From Undecidability.FOL.Proofmode Require Import Theories ProofMode.
Require Import String List.

Import ListNotations.
Open Scope string_scope.


(** Some proofs from Reductions.PCPb_to_minZF done with the Proof Mode *)

Section MinZF.

Existing Instance falsity_on.
Variable p : peirce.

Existing Instance sig_empty.

Instance eqdec_sig_empty : EqDec sig_empty.
Proof. intros x y; decide equality. Qed.

Instance eqdec_preds' : EqDec ZF_pred_sig.
Proof. intros x y; decide equality. Qed.

Program Instance MinZF_Leibniz : Leibniz sig_empty ZF_pred_sig falsity_on.
Next Obligation. exact equal. Defined.
Next Obligation. exact minZFeq'. Defined.
Next Obligation. fintros. fapply ax_refl'. Qed.
Next Obligation. fintros. fapply ax_sym'. ctx. Qed.
Next Obligation. easy. Qed.
Next Obligation.
  unfold MinZF_Leibniz_obligation_1 in *. rename v1 into t; rename v2 into t0.
  destruct P.
  - change (ZF_pred_ar elem) with 2 in t, t0; repeat dependent elimination t0; repeat dependent elimination t.
    cbn in H1. split.
    + intros H2. feapply ax_eq_elem'. 3: apply H2. all: apply H1.
    + intros H2. feapply ax_eq_elem'. 3: apply H2. all: fapply ax_sym'; apply H1.
  - change (ZF_pred_ar equal) with 2 in t, t0; repeat dependent elimination t0; repeat dependent elimination t.
    cbn in H1. split.
    + intros H2. feapply ax_trans'. feapply ax_sym'. apply H1. feapply ax_trans'.
      apply H2. apply H1.
    + intros H2. feapply ax_trans'. apply H1. feapply ax_trans'. apply H2.
      fapply ax_sym'. apply H1.
Qed.




Lemma prv_to_min_inductive n :
  minZFeq' ⊢ rm_const_fm (inductive $n) ~> is_inductive $n.
Proof.
  cbn. unfold "↑". fstart. fintros "[[e [ [s [ ]]]] ]". fsplit.
  - fexists e. fsplit. fintros x; fapply "H". frewrite <- "H0"; ctx.
  - fintros. fdestruct ("H2" x) as "...".
    { fexists x. fsplit. fapply ax_refl'. fexists $n. fsplit. fapply ax_refl'. ctx. }
    fexists x0. fsplit.
    + fintros y. fsplit.
      * fintros "H11". fapply "H8" in "H11" as "[ [ ]]". fapply "H7" in "H11" as "[|]".
        -- fleft. frewrite <- "H2". frewrite <- "H11". ctx.
        -- fright. fdestruct ("H6" y). fdestruct "H6".
           frewrite <- "H11". ctx. all: frewrite "H6"; ctx.
      * fintros "[|]".
        -- fapply "H8". fexists x2. fsplit. fapply "H7". fleft. fapply ax_refl'.
           frewrite "H2". ctx.
        -- frewrite "H11". fapply "H8". fexists x3. fsplit. fapply "H7". 
           fright. fapply ax_refl'. fapply "H6". fleft. fapply ax_sym'. ctx.
    + frewrite <- "H9". ctx.
Qed.



End MinZF.

