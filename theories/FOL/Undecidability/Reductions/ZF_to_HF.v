(** ** Reduction from ZF' to finite ZF *)

From Undecidability.FOL
     Require Import Syntax.Facts Semantics.Tarski.FullFacts Deduction.FullFacts.

From Undecidability.FOL.Sets
     Require Import ZF.

Require Import Lia.

From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Definition add_om phi :=
  ax_om1 → ax_om2 → phi.

Theorem reduction_entailment phi :
  entailment_ZF' phi <-> entailment_HF (add_om phi).
Proof.
  split; intros Hp D I rho HE HI.
  - intros H1 H2. apply Hp; trivial.
    intros sigma psi [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; trivial.
    all: apply HI; unfold HF; intuition.
  - apply Hp; fold sat; trivial. 2,3: apply HI; unfold ZF'; intuition eauto 7.
    intros sigma psi [<-|[<-|[<-|[<-|[<-|[]]]]]]. all: apply HI; unfold ZF'; intuition.
Qed.

Theorem reduction_deduction phi :
  deduction_ZF' phi <-> deduction_HF (add_om phi).
Proof.
  unfold deduction_ZF', deduction_HF, add_om. rewrite !imps.
  split; intros H; apply (Weak H); unfold ZFeq', HFeq, ZF', HF; firstorder.
Qed.
