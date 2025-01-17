(* * Natural Deduction *)

From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability.FOL Require Import Syntax.Facts Syntax.Theories.
From Undecidability.FOL Require Export Deduction.FullNDFacts.
From Undecidability.FOL.Semantics.Tarski Require Export FullFacts FullSoundness.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
From Stdlib Require Import Lia.
Import FullSyntax.



Local Set Implicit Arguments.
Local Unset Strict Implicit.


Section Consistency.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Context {p : peirce}.

  #[local] Existing Instance TM.

  Lemma consistent : ~ ([] ⊢ ⊥).
  Proof.
    intros H. unshelve eapply (sound_for_classical_model _ H).
    - exact (fun _ => tt).
    - apply TM_sat_decidable.
    - easy.
  Qed.

End Consistency.
