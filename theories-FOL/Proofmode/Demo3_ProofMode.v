From Equations Require Import Equations DepElim.
From Undecidability.FOL Require Import Util.Syntax Util.FullDeduction Util.FullTarski PA.
From Undecidability.FOL.Proofmode Require Import Theories ProofMode.
Require Import String List.

Import ListNotations.
Open Scope string_scope.


Section FullLogic.

Existing Instance falsity_on.
Variable p : peirce.


(* Setup *)

Instance eqdec_funcs : EqDec PA_funcs_signature.
Proof. intros x y; decide equality. Qed.

Instance eqdec_preds : EqDec PA_preds_signature.
Proof. intros x y. destruct x, y. now left. Qed.

Program Instance PA_Leibniz : Leibniz PA_funcs_signature PA_preds_signature falsity_on.
Next Obligation. exact Eq. Defined.
Next Obligation. exact FAeq. Defined.
Next Obligation. fintros. fapply ax_refl. Qed.
Next Obligation. fintros. fapply ax_sym. ctx. Qed.
Next Obligation.
  unfold PA_Leibniz_obligation_1 in *. rename v1 into t; rename v2 into t0.
  destruct F; repeat dependent elimination t0; repeat dependent elimination t.
  - fapply ax_refl.
  - fapply ax_succ_congr. apply H1.
  - fapply ax_add_congr; apply H1.
  - fapply ax_mult_congr; apply H1.
Qed.
Next Obligation.
  unfold PA_Leibniz_obligation_1 in *. rename v1 into t; rename v2 into t0.
  destruct P; repeat dependent elimination t0; repeat dependent elimination t.
  - cbn in H1. split.
    + intros H2. feapply ax_trans. feapply ax_sym. apply H1. feapply ax_trans.
      apply H2. apply H1.
    + intros H2. feapply ax_trans. apply H1. feapply ax_trans. apply H2.
      fapply ax_sym. apply H1.
Qed.


Require Import Undecidability.FOL.Proofmode.Hoas.

Notation "'σ' x" := (bFunc Succ (Vector.cons bterm x 0 (Vector.nil bterm))) (at level 37) : hoas_scope.
Notation "x '⊕' y" := (bFunc Plus (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 39) : hoas_scope.
Notation "x '⊗' y" := (bFunc Mult (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 38) : hoas_scope. 
Notation "x '==' y" := (bAtom Eq (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 40) : hoas_scope.

Ltac custom_fold ::= fold ax_induction in *.
Ltac custom_unfold ::= unfold ax_induction in *.

Definition PA :=
  ax_induction (<< Free x, ∀' y, x ⊕ σ y == σ (x ⊕ y)) ::
  ax_induction (<< Free x, ∀' y, x ⊕ y == y ⊕ x) ::
  ax_induction (<< Free x, x ⊕ zero == x) ::
  ax_zero_succ ::
  ax_succ_inj ::
  FAeq.


(* For didactic reasons, we don't print substitutions in this demo.
   We also plan on implementing this as an optional flag for the proof mode. *)
Notation "t" := (subst_term _ t) (at level 1, only printing) : subst_scope.
Notation "phi" := (subst_form _ phi) (at level 1, only printing) : subst_scope.




Lemma add_zero_r :
  PA ⊢ << ∀' x, x ⊕ zero == x.
Proof.
  fstart. fapply ((ax_induction (<< Free x, x ⊕ zero == x))).
  - frewrite (ax_add_zero zero). fapply ax_refl.
  - fintros "x" "IH". frewrite (ax_add_rec zero x). frewrite "IH". fapply ax_refl.
Qed.

Lemma add_succ_r :
  PA ⊢ << ∀' x y, x ⊕ σ y == σ (x ⊕ y).
Proof.
  fstart. fapply ((ax_induction (<< Free x, ∀' y, x ⊕ σ y == σ (x ⊕ y)))).
  - fintros "y". frewrite (ax_add_zero (σ y)). frewrite (ax_add_zero y). fapply ax_refl.
  - fintros "x" "IH" "y". frewrite (ax_add_rec (σ y) x). frewrite ("IH" y). 
    frewrite (ax_add_rec y x). fapply ax_refl.
Qed.

Lemma add_comm :
  PA ⊢ << ∀' x y, x ⊕ y == y ⊕ x.
Proof.
  fstart.
  fapply ((ax_induction (<< Free x, ∀' y, x ⊕ y == y ⊕ x))).
  - fintros "x".
    Check add_zero_r.
    frewrite (add_zero_r x).
    fapply ax_add_zero.
  - fintros "x" "IH" "y".
    frewrite (add_succ_r y x).
    frewrite <- ("IH" y).
    fapply ax_add_rec.
Qed.



































