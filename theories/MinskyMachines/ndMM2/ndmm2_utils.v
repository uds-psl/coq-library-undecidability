(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.

From Undecidability.MinskyMachines 
  Require Import ndMM2.

Section ndMM2_monotonicity.

  Variables loc : Set.

  Notation "Σ // a ⊕ b ⊦ u" := (@ndmm2_accept loc Σ a b u) (at level 70, no associativity).

  Infix "⊆" := incl (at level 70).

  Tactic Notation "by" "constr" int(i) "with" hyp(H) := econstructor i; [ apply H | ]; eassumption.

  Fact ndmm2_accept_mono Σ Θ a b u : Σ ⊆ Θ -> Σ // a ⊕ b ⊦ u -> Θ // a ⊕ b ⊦ u.
  Proof.
    intros H.
    induction 1.
    + constructor; auto.
    + by constr 2 with H.
    + by constr 3 with H.
    + by constr 4 with H.
    + by constr 5 with H.
    + by constr 6 with H.
    + by constr 7 with H.
  Qed.

End ndMM2_monotonicity.
