(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation.

Set Implicit Arguments.

(** * Intuionistic Linear Logic *)

Local Infix "~p" := (@Permutation _) (at level 70).

Definition ll_vars := nat.

(** We only consider the fragment of ILL which
   contains !, -o and & ... 
 
   ILL can be faithfully embedded into that fragment 
   but this does not matter for undecidability 
*)

Inductive ll_conn := ll_with | ll_limp | ll_times | ll_plus.
Inductive ll_cst := ll_one | ll_bot | ll_top.

Inductive ll_form : Set :=
  | ll_var  : ll_vars -> ll_form
  | ll_zero : ll_cst  -> ll_form
  | ll_ban  : ll_form -> ll_form
  | ll_bin  : ll_conn -> ll_form -> ll_form -> ll_form.

(* Symbols for cut&paste ⟙   ⟘   𝝐  ﹠ ⊗  ⊕  ⊸  ❗   ‼  ∅  ⊢ *)

Notation "⟙" := (ll_zero ll_top).
Notation "⟘" := (ll_zero ll_bot).
Notation 𝝐 := (ll_zero ll_one).

Infix "&" := (ll_bin ll_with) (at level 50, only parsing).
Infix "﹠" := (ll_bin ll_with) (at level 50).
Infix "⊗" := (ll_bin ll_times) (at level 50).
Infix "⊕" := (ll_bin ll_plus) (at level 50).
Infix "-o" := (ll_bin ll_limp) (at level 51, only parsing, right associativity).
Infix "⊸" := (ll_bin ll_limp) (at level 51, right associativity).

Notation "'!' x" := (ll_ban x) (at level 52, only parsing).
Notation "❗ x" := (ll_ban x) (at level 52).

Notation "£" := ll_var.

Definition ll_lbang := map (fun x => !x).

Notation "'!l' x" := (ll_lbang x) (at level 60, only parsing).
Notation "‼ x" := (ll_lbang x) (at level 60).

Notation "∅" := nil (only parsing).

Reserved Notation "l '⊢' x" (at level 70, no associativity).

Inductive S_ill : list ll_form -> ll_form -> Prop :=

  (* These are the SILL rules in the paper *)

  | in_llp_ax     : forall A,                         A::∅ ⊢ A

  | in_llp_perm   : forall Γ Δ A,              Γ ~p Δ     ->   Γ ⊢ A 
                                           (*-----------------------------*)
                                      ->                 Δ ⊢ A

  | in_llp_limp_l : forall Γ Δ A B C,          Γ ⊢ A      ->   B::Δ ⊢ C
                                           (*-----------------------------*)    
                                      ->           A ⊸ B::Γ++Δ ⊢ C

  | in_llp_limp_r : forall Γ A B,                    A::Γ ⊢ B
                                           (*-----------------------------*)
                                      ->            Γ ⊢ A ⊸ B

  | in_llp_with_l1 : forall Γ A B C,                  A::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->           A﹠B::Γ ⊢ C

  | in_llp_with_l2 : forall Γ A B C,                  B::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->           A﹠B::Γ ⊢ C
 
  | in_llp_with_r : forall Γ A B,               Γ ⊢ A     ->   Γ ⊢ B
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A﹠B

  | in_llp_bang_l : forall Γ A B,                    A::Γ ⊢ B
                                           (*-----------------------------*)
                                      ->            ❗ A::Γ ⊢ B

  | in_llp_bang_r : forall Γ A,                       ‼Γ ⊢ A
                                           (*-----------------------------*)
                                      ->              ‼Γ ⊢ ❗ A

  | in_llp_weak : forall Γ A B,                        Γ ⊢ B
                                           (*-----------------------------*)
                                      ->           ❗ A::Γ ⊢ B

  | in_llp_cntr : forall Γ A B,                    ❗ A::❗ A::Γ ⊢ B
                                           (*-----------------------------*)
                                      ->             ❗ A::Γ ⊢ B

  (* These are the other rule for a complete sequent calculus for the whole ILL *)

  | in_llp_cut : forall Γ Δ A B,                 Γ ⊢ A    ->   A::Δ ⊢ B
                                           (*-----------------------------*)    
                                      ->              Γ++Δ ⊢ B

  | in_llp_times_l : forall Γ A B C,               A::B::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->            A⊗B::Γ ⊢ C
 
  | in_llp_times_r : forall Γ Δ A B,             Γ ⊢ A    ->   Δ ⊢ B
                                           (*-----------------------------*)
                                      ->              Γ++Δ ⊢ A⊗B

  | in_llp_plus_l :  forall Γ A B C,            A::Γ ⊢ C  ->  B::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->            A⊕B::Γ ⊢ C

  | in_llp_plus_r1 : forall Γ A B,                    Γ ⊢ A  
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A⊕B

  | in_llp_plus_r2 : forall Γ A B,                    Γ ⊢ B  
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A⊕B

  | in_llp_bot_l : forall Γ A,                     ⟘::Γ ⊢ A

  | in_llp_top_r : forall Γ,                          Γ ⊢ ⟙

  | in_llp_unit_l : forall Γ A,                       Γ ⊢ A  
                                           (*-----------------------------*)
                                      ->           𝝐 ::Γ ⊢ A

  | in_llp_unit_r :                                   ∅ ⊢ 𝝐

where "l ⊢ x" := (S_ill l x).

Definition ILL_PROVABILITY (c : (list ll_form) * ll_form) := let (Ga,A) := c in Ga ⊢ A. 
