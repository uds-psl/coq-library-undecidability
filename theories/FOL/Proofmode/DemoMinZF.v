From Equations Require Import Equations.
Require Equations.Type.DepElim.
From Undecidability.Shared Require Import Dec.
From Undecidability.FOL Require Import Syntax.Core Deduction.FullND Semantics.Tarski.FullCore Sets.minZF.
From Undecidability.FOL Require Import Sets.Signatures Undecidability.Reductions.PCPb_to_ZF Undecidability.Reductions.PCPb_to_minZF.
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



Lemma prv_to_min_refl :
  minZFeq' ⊢ rm_const_fm ax_refl.
Proof.
  cbn. fstart. fintros "x". repeat (fexists x; fsplit; try fapply ax_refl').
Qed.

Lemma prv_to_min_sym :
  minZFeq' ⊢ rm_const_fm ax_sym.
Proof.
  cbn. fstart. fintros "x" "y" "[x' [-> [y' [-> ->]]]]". fexists y. fsplit.
  fapply ax_refl'. fexists y. fsplit; fapply ax_refl'.
Qed.

Lemma prv_to_min_trans :
  minZFeq' ⊢ rm_const_fm ax_trans.
Proof.
  cbn. fstart. fintros "x" "y" "z" "[ [-> [ [-> ->]]]]" "[ [-> [ [-> ->]]]]". 
  fexists z. fsplit. fapply ax_refl'. fexists z. fsplit; fapply ax_refl'.
Qed.

Lemma prv_to_min_elem :
  minZFeq' ⊢ rm_const_fm ax_eq_elem.
Proof.
  cbn. fstart. fintros "a" "b" "c" "d".
  fintros "[ [-> [ [-> ->]]]]" "[ [-> [ [-> ->]]]]". fintros. ctx.
Qed.

Lemma prv_to_min_ext :
  minZFeq' ⊢ rm_const_fm ax_ext.
Proof.
  cbn. fstart. fintros "x" "y" "H1" "H2". fexists x. fsplit. fapply ax_refl'. 
  fexists y. fsplit. fapply ax_refl'. fapply ax_ext'; fintros "z" "H".
  - fdestruct ("H1" z) as "[ [-> [ [-> ]]]]". 2: ctx. fexists z. fsplit. 
    fapply ax_refl'. fexists x. fsplit. fapply ax_refl'. ctx.
  - fdestruct ("H2" z) as "[ [-> [ [-> ]]]]". 2: ctx. fexists z. fsplit. 
    fapply ax_refl'. fexists y. fsplit. fapply ax_refl'. ctx.
Qed.

Lemma prv_to_min_eset :
  minZFeq' ⊢ rm_const_fm ax_eset.
Proof.
  cbn. fstart. fintros "x" "...". feapply "H0". fapply "H1".
Qed.

Lemma prv_to_min_pair :
  minZFeq' ⊢ rm_const_fm ax_pair.
Proof.
  cbn. fstart. fintros "x" "y" "z". fsplit.
  - fintros "[ [-> [ [[ [-> [ [-> ]]]] ]]]]". fdestruct ("H2" z). 
    fdestruct "H2" as "[->|->]". ctx.
    + fleft. repeat (fexists y; fsplit; try fapply ax_refl').
    + fright. repeat (fexists x; fsplit; try fapply ax_refl').
  - fassert (ax_pair') as "HP". ctx. fdestruct ("HP" y x) as "[pair HP]".
    fintros "[[ [-> [ [-> ->]]]]|[ [-> [ [-> ->]]]]]". fexists y. 2: fexists x.
    all: fsplit; try fapply ax_refl'; fexists pair; fsplit.
    1,3: fexists y; fsplit; try fapply ax_refl'; fexists x; fsplit; try fapply ax_refl'; ctx.
    all: fapply "HP". fleft; fapply ax_refl'. fright; fapply ax_refl'.
Qed.

Lemma prv_to_min_union :
  minZFeq' ⊢ rm_const_fm ax_union.
Proof.
  cbn. fstart. fintros "x" "y". fsplit.
  - fintros "[ [-> [ [[ [-> ]] ]]]]". fdestruct ("H1" y). 
    fdestruct ("H1" "H2") as "[z [ ]]". fexists z. fsplit.
    + fexists z. fsplit. fapply ax_refl'. fexists x. fsplit. fapply ax_refl'. ctx.
    + fexists y. fsplit. fapply ax_refl'. fexists z. fsplit. fapply ax_refl'. ctx.
  - fintros "[ [[ [-> [ [-> ]]]] [ [-> [ [-> ]]]]]]". fexists y. fsplit. fapply ax_refl'.
    fassert ax_union' as "HU". ctx. fdestruct ("HU" x) as "[u HU]". fexists u. fsplit.
    + fexists x. fsplit. fapply ax_refl'. ctx.
    + fapply "HU". fexists x0. fsplit; ctx.
Qed.

Lemma prv_to_min_power :
  minZFeq' ⊢ rm_const_fm ax_power.
Proof.
  cbn. fstart. fintros "x" "y". fsplit.
  - fintros "[ [-> [ [[ [-> ]] ]]]]" "z" "[ [-> [ [-> ]]]]". fexists z.
    fsplit. fapply ax_refl'. fexists x. fsplit. fapply ax_refl'. fdestruct ("H1" y).
    fapply "H1"; ctx.
  - fintros. fassert ax_power' as "HP". ctx. fdestruct ("HP" x) as "[power HP]".
    fexists y. fsplit. fapply ax_refl'. fexists power. fsplit.
    + fexists x. fsplit. fapply ax_refl'. ctx.
    + fapply "HP". fintros "z" "H1". fdestruct ("H" z) as "[ [-> [ [-> ]]]]". 2: ctx.
    fexists z. fsplit. fapply ax_refl'. fexists y. fsplit. fapply ax_refl'. ctx.
Qed.

Lemma prv_to_min_inductive n :
  minZFeq' ⊢ rm_const_fm (inductive $n) → is_inductive $n.
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

Lemma prv_to_min_om1 :
  minZFeq' ⊢ rm_const_fm ax_om1.
Proof.
  cbn. unfold "↑". fstart. fsplit.
  - fassert ax_eset' as "[e HE]". ctx. fexists e. fsplit. ctx.
    fassert ax_om' as "[o HO]". ctx. fexists o. fsplit. ctx. 
    fdestruct "HO" as "...". feapply ax_eq_elem'. 3: fapply "H0". 2: fapply ax_refl'. 
    fapply ax_ext'; fintros; fexfalso. feapply "H"; ctx. feapply "HE"; ctx.
  - fintros x "...".
    (* TODO: fdestruct clears the original *)
    fassert (∀ $0 ∈' x1`[↑] → (∃ (∀ $0 ∈' $1 ↔ $0 ∈' $2 ∨ $0 ≡' $2) ∧ $0 ∈' x1`[↑]`[↑])) as "H2'". ctx.
    fdestruct ("H2" x) as "[y [ ]]". frewrite <- "H"; ctx.
    fexists y. fsplit.
    + fassert ax_pair' as "HP". ctx. fdestruct ("HP" x x) as "[s Hs]".
      fassert ax_pair' as "HP". ctx. fdestruct ("HP" x s) as "[t Ht]".
      fexists t. fsplit.
      * fexists x. fsplit. fapply ax_refl'. fexists s. fsplit. 2: ctx.
        fexists x. fsplit. fapply ax_refl'. fexists x. fsplit. fapply ax_refl'. ctx.
      * fintros z. fsplit.
        -- fintros. fapply "H2" in "H6" as "[|->]". 
           ++ fexists x. fsplit. fapply "Ht". fleft. fapply ax_refl'. ctx.
           ++ fexists s. fsplit. fapply "Ht". fright. fapply ax_refl'.
              fapply "Hs". fleft. fapply ax_refl'.
        -- fintros "[ [ ]]". fapply "H2". fapply "Ht" in "H6" as "[<-|]".
           ++ fleft. ctx.
           ++ fright. fassert (z ∈' s). frewrite <- "H6"; ctx. 
              fapply "Hs" in "H8" as "[|]"; ctx.
    + fexists x1. fsplit. 2: ctx. fsplit. fsplit. fexists x2; fsplit; ctx.
      fintros. fapply "H2'". ctx. ctx.
Qed.

Local Arguments inductive : simpl never.
Local Arguments is_inductive : simpl never.
Local Arguments is_om : simpl nomatch.

Lemma prv_to_min_om2 :
  minZFeq' ⊢ rm_const_fm ax_om2.
Proof.
  cbn. fstart. fintros "x". destruct x as [n|[]]. 
  rewrite rm_const_fm_subst, inductive_subst, !is_inductive_subst. cbn.
  fintros "H" "y" "[ [-> [z [[ ] ]]]]". fexists y. fsplit. fapply ax_refl'.
  rewrite !is_inductive_subst. cbn. fexists $n. fsplit. fapply ax_refl'.
  fapply "H2". fapply prv_to_min_inductive. ctx. ctx.
Qed.

Lemma prv_to_min phi :
  In phi ZFeq' -> minZFeq' ⊢ rm_const_fm phi.
Proof.
  intros [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]].
  - apply prv_to_min_refl.
  - apply prv_to_min_sym.
  - apply prv_to_min_trans.
  - apply prv_to_min_elem.
  - apply prv_to_min_ext.
  - apply prv_to_min_eset.
  - apply prv_to_min_pair.
  - apply prv_to_min_union.
  - apply prv_to_min_power.
  - apply prv_to_min_om1.
  - apply prv_to_min_om2.
Qed.


End MinZF.

