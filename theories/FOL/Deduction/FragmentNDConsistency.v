(* * Natural Deduction *)

From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability.FOL Require Import Syntax.Facts Syntax.Theories.
From Undecidability.FOL Require Export Deduction.FragmentNDFacts.
From Undecidability.FOL.Semantics.Tarski Require Export FragmentFacts FragmentSoundness.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Require Import Lia.
Import FragmentSyntax.


Set Default Proof Using "Type".

Local Set Implicit Arguments.
Local Unset Strict Implicit.


Section Consistency.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Context {p : peirce}.

  #[local] Existing Instance TM.

  Lemma consistent_ND : ~ ([] ⊢ ⊥).
  Proof.
    intros H. unshelve eapply (sound_for_classical_model _ H).
    - exact (fun _ => tt).
    - intros rho phi psi. cbn.
      destruct (TM_sat_decidable rho phi) as [Hl1|Hr1],
               (TM_sat_decidable rho psi) as [Hl2|Hr2]; tauto.
    - easy.
  Qed.

End Consistency.
