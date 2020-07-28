(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation.

From Undecidability.ILL Require Import ILL.

Set Implicit Arguments.

Local Infix "~p" := (@Permutation _) (at level 70).

Definition ll_vars := nat.

Inductive eill_cmd : Set :=
  | in_ll_cmd_inc  : ll_vars -> ll_vars -> ll_vars -> eill_cmd
  | in_ll_cmd_dec  : ll_vars -> ll_vars -> ll_vars -> eill_cmd
  | in_ll_cmd_fork : ll_vars -> ll_vars -> ll_vars -> eill_cmd.

Notation LL_INC  := in_ll_cmd_inc.
Notation LL_DEC  := in_ll_cmd_dec.
Notation LL_FORK := in_ll_cmd_fork.

Definition eill_cmd_vars c := 
  match c with
    | LL_INC  a p q => a::p::q::nil
    | LL_DEC  a p q => a::p::q::nil
    | LL_FORK p q r => p::q::r::nil
  end.

(* The embedding of eill commands into ill 
   or its (!,&,-o) fragment *) 

Definition eill_cmd_map c :=
  match c with
    | LL_INC  a p q => (£a ⊸ £p) -o £ q
    | LL_DEC  a p q => £a ⊸ £p -o £ q
    | LL_FORK p q r => (£p ﹠ £q) -o £ r
  end. 

(* Symbols for cut&paste ⟙   ⟘   𝝐  ﹠ ⊗  ⊕  ⊸  ❗   ‼  ∅  ⊢ ⟦ ⟧ Γ Δ Σ *)

Reserved Notation "Si ; Ga '⊦' x" (at level 70, no associativity).

Inductive G_eill (Σ : list eill_cmd) : list ll_vars -> ll_vars -> Prop :=
  | in_eill_ax  : forall u,                                    Σ; u::∅ ⊦ u
  | in_eill_perm : forall Γ Δ p,    Γ ~p Δ                 ->  Σ; Γ     ⊦ p
                                                           ->  Σ; Δ     ⊦ p
  | in_eill_inc : forall Γ a p q,   In (LL_INC a p q) Σ    ->  Σ; a::Γ  ⊦ p
                                                           ->  Σ; Γ     ⊦ q
  | in_eill_dec : forall Γ Δ p q r, In (LL_DEC p q r) Σ    ->  Σ; Γ     ⊦ p
                                                           ->  Σ; Δ     ⊦ q
                                                           ->  Σ; Γ++Δ  ⊦ r
  | in_eill_fork : forall Γ p q r,  In (LL_FORK p q r) Σ   ->  Σ; Γ     ⊦ p
                                                           ->  Σ; Γ     ⊦ q
                                                           ->  Σ; Γ     ⊦ r
where "Si ; Ga ⊦ u" := (G_eill Si Ga u).

Definition EILL_SEQUENT := (list eill_cmd * list ll_vars * ll_vars)%type.

Definition EILL_PROVABILITY (c : EILL_SEQUENT) := match c with (Σ,Γ,A) => Σ; Γ ⊦ A end. 
