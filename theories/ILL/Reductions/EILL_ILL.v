(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.

Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts.

From Undecidability.ILL
  Require Import EILL ILL ill eill. 

Theorem EILL_rILL_cf_PROVABILITY : EILL_PROVABILITY ⪯ rILL_cf_PROVABILITY.
Proof.
  exists (fun p => match p with (Σ,Γ,p) => (map (fun c => !⦑c⦒) Σ ++ map £ Γ,£ p) end).
  intros ((?&?)&?); apply G_eill_S_ill_restr.
Qed.

Theorem EILL_rILL_PROVABILITY : EILL_PROVABILITY ⪯ rILL_PROVABILITY.
Proof.
  exists (fun p => match p with (Σ,Γ,p) => (map (fun c => !⦑c⦒) Σ ++ map £ Γ,£ p) end).
  intros ((?&?)&?); apply G_eill_S_ill_restr_wc.
Qed.

Theorem EILL_ILL_cf_PROVABILITY : EILL_PROVABILITY ⪯ ILL_cf_PROVABILITY.
Proof.
  exists (fun p => match p with (Σ,Γ,p) => (map (fun c => !⦑c⦒) Σ ++ map £ Γ,£ p) end).
  intros ((?&?)&?); apply G_eill_S_ill.
Qed.

Theorem EILL_ILL_PROVABILITY : EILL_PROVABILITY ⪯ ILL_PROVABILITY.
Proof.
  exists (fun p => match p with (Σ,Γ,p) => (map (fun c => !⦑c⦒) Σ ++ map £ Γ,£ p) end).
  intros ((?&?)&?); apply G_eill_S_ill_wc.
Qed.
