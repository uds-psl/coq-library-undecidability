(*************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(*************************************************************)

Require Import List.

Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.Synthetic.ReducibilityFacts.

From Undecidability.ILL
  Require Import EILL ILL CLL ill eill ill_cll.

Theorem EILL_CLL_cf_PROVABILITY : EILL_PROVABILITY ⪯ CLL_cf_PROVABILITY.
Proof.
  apply reduces_dependent; exists.
  intros ((Σ,Γ),u).
  exists ( map (fun c => cll_una cll_bang [⦑c⦒]) Σ 
        ++ map cll_var Γ, cll_var u::nil).
  apply G_eill_S_cll.
Qed.
