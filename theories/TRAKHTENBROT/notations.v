(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* Unicode DB for cut/paste 
  -> ⇡ ↑ 
  -> ⟬  ⟭ ⟦ ⟧ ⟪ ⟫ ⦃ ⦄
  -> φ ψ σ ρ 𝕋 𝔽 
*)

(** Lifting a term substitution *)
Reserved Notation "⇡ sig" (at level 1, format "⇡ sig").

(** Lifting a DeBruijn subtitution *)
Reserved Notation "phi ↑ k" (at level 1, format "phi ↑ k", left associativity).

(** Term substitution and semantics *)
Reserved Notation "t '⟬' σ '⟭'" (at level 1, format "t ⟬ σ ⟭").
Reserved Notation "'⟦' t '⟧'" (at level 1, format "⟦ t ⟧").

(** Formula subsitution and semantics*)
Reserved Notation "f '⦃' σ '⦄'" (at level 1, format "f ⦃ σ ⦄").
Reserved Notation "'⟪' f '⟫'" (at level 1, format "⟪ f ⟫").

(* A non-recursive fixpoint to get correct unfolding *)

Fixpoint env_lift {X} (φ : nat -> X) k n { struct n } :=
  match n with
    | 0   => k
    | S n => φ n
  end.

Notation "phi ↑ k" := (env_lift phi k).
