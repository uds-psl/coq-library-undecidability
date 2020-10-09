(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.

Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.ILL
  Require Import EILL ILL CLL ill eill ill_cll schellinx.

Theorem EILL_CLL_cf_PROVABILITY : EILL_PROVABILITY ⪯ CLL_cf_PROVABILITY.
Proof.
  exists (fun p => match p with (Σ,Γ,p) => (map (fun c => !⦑c⦒) Σ ++ map £ Γ,£ p::nil) end).
  intros ((?&?)&?); apply G_eill_S_cll.
Qed.
