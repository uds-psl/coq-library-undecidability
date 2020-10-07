(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation Arith.

From Undecidability.ILL Require Import ILL.

Set Implicit Arguments.

Local Infix "~p" := (@Permutation _) (at level 70).

(* Symbols for cut&paste ⟙   ⟘   𝝐  ﹠ ⊗  ⊕  ⊸  ❗   ‼  ∅  ⊢ ⟦ ⟧ Γ Δ Σ *)

Section S_cll_restr_without_cut.

  (** CLL rules restricted to the (!,&,-o) fragment without cut *)

  Inductive S_cll_restr : list ll_form -> list ll_form -> Prop :=

    | in_cll1_ax     : forall A,                        A::∅ ⊢ A::∅

    | in_cll1_perm  : forall Γ Δ Γ' Δ',      Γ ~p Γ' -> Δ ~p Δ' ->   Γ ⊢ Δ 
                                           (*-----------------------------*)
                                      ->                 Γ' ⊢ Δ'

    | in_cll1_limp_l : forall Γ Δ Γ' Δ' A B,  Γ ⊢ A::Δ      ->   B::Γ' ⊢ Δ'
                                           (*-----------------------------*)    
                                      ->           A ⊸ B::Γ++Γ' ⊢ Δ++Δ'

    | in_cll1_limp_r : forall Γ Δ A B,               A::Γ ⊢ B::Δ
                                           (*-----------------------------*)
                                      ->            Γ ⊢ A ⊸ B::Δ

    | in_cll1_with_l1 : forall Γ Δ A B,               A::Γ ⊢ Δ 
                                           (*-----------------------------*)
                                      ->           A﹠B::Γ ⊢ Δ

    | in_cll1_with_l2 : forall Γ Δ A B,              B::Γ ⊢ Δ 
                                           (*-----------------------------*)
                                      ->           A﹠B::Γ ⊢ Δ
 
    | in_cll1_with_r : forall Γ Δ A B,        Γ ⊢ A::Δ     ->   Γ ⊢ B::Δ
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A﹠B::Δ

    | in_cll1_bang_l : forall Γ A Δ,                 A::Γ ⊢ Δ
                                           (*-----------------------------*)
                                      ->            !A::Γ ⊢ Δ

    | in_cll1_bang_r : forall Γ A,                    ‼Γ ⊢ A::nil               (* since ? is absent, only ??Δ = nil works *)
                                           (*-----------------------------*)
                                      ->              ‼Γ ⊢ !A::nil

    | in_cll1_weak_l : forall Γ A Δ,                   Γ ⊢ Δ
                                           (*-----------------------------*)
                                      ->           !A::Γ ⊢ Δ

    | in_cll1_cntr_l : forall Γ A Δ,             !A::!A::Γ ⊢ Δ
                                           (*-----------------------------*)
                                      ->             !A::Γ ⊢ Δ

  where "l ⊢ m" := (S_cll_restr l m).

End S_cll_restr_without_cut.

Section S_cll_without_cut.

  (** CLL rules restricted to the (𝟘,?,⅋) free fragment without cut 
      which shares the same formula language as ILL, but of course 
      not the same rules *)

  Inductive S_cll : list ll_form -> list ll_form -> Prop :=

    | in_cll2_ax     : forall A,                        A::∅ ⊢ A::∅

    | in_cll2_perm  : forall Γ Δ Γ' Δ',      Γ ~p Γ' -> Δ ~p Δ' ->   Γ ⊢ Δ 
                                           (*-----------------------------*)
                                      ->                 Γ' ⊢ Δ'

    | in_cll2_limp_l : forall Γ Δ Γ' Δ' A B,  Γ ⊢ A::Δ      ->   B::Γ' ⊢ Δ'
                                           (*-----------------------------*)    
                                      ->           A ⊸ B::Γ++Γ' ⊢ Δ++Δ'

    | in_cll2_limp_r : forall Γ Δ A B,               A::Γ ⊢ B::Δ
                                           (*-----------------------------*)
                                      ->            Γ ⊢ A ⊸ B::Δ

    | in_cll2_with_l1 : forall Γ Δ A B,               A::Γ ⊢ Δ 
                                           (*-----------------------------*)
                                      ->           A﹠B::Γ ⊢ Δ

    | in_cll2_with_l2 : forall Γ Δ A B,              B::Γ ⊢ Δ 
                                           (*-----------------------------*)
                                      ->           A﹠B::Γ ⊢ Δ
 
    | in_cll2_with_r : forall Γ Δ A B,        Γ ⊢ A::Δ     ->   Γ ⊢ B::Δ
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A﹠B::Δ

    | in_cll2_times_l : forall Γ A B Δ,            A::B::Γ ⊢ Δ 
                                           (*-----------------------------*)
                                      ->            A⊗B::Γ ⊢ Δ
 
    | in_cll2_times_r : forall Γ Δ Γ' Δ' A B,  Γ ⊢ A::Δ    ->   Γ' ⊢ B::Δ'
                                           (*-----------------------------*)
                                      ->          Γ++Γ' ⊢ A⊗B::Δ++Δ'

    | in_cll2_plus_l :  forall Γ A B Δ,         A::Γ ⊢ Δ  ->  B::Γ ⊢ Δ 
                                           (*-----------------------------*)
                                      ->            A⊕B::Γ ⊢ Δ

    | in_cll2_plus_r1 : forall Γ A B Δ,               Γ ⊢ A::Δ  
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A⊕B::Δ

    | in_cll2_plus_r2 : forall Γ A B Δ,               Γ ⊢ B::Δ  
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A⊕B::Δ

    | in_cll2_bot_l : forall Γ Δ,                     ⟘::Γ ⊢ Δ

    | in_cll2_top_r : forall Γ Δ,                      Γ ⊢ ⟙::Δ

    | in_cll2_unit_l : forall Γ Δ,                       Γ ⊢ Δ  
                                           (*-----------------------------*)
                                        ->           𝟙::Γ ⊢ Δ

    | in_cll2_unit_r :                                  ∅ ⊢ 𝟙::∅


    | in_cll2_bang_l : forall Γ A Δ,                 A::Γ ⊢ Δ
                                           (*-----------------------------*)
                                      ->            !A::Γ ⊢ Δ

    | in_cll2_bang_r : forall Γ A,                    ‼Γ ⊢ A::nil               (* since ? is absent, only ??Δ = nil works *)
                                           (*-----------------------------*)
                                      ->              ‼Γ ⊢ !A::nil

    | in_cll2_weak_l : forall Γ A Δ,                   Γ ⊢ Δ
                                           (*-----------------------------*)
                                      ->           !A::Γ ⊢ Δ

    | in_cll2_cntr_l : forall Γ A Δ,             !A::!A::Γ ⊢ Δ
                                           (*-----------------------------*)
                                      ->             !A::Γ ⊢ Δ

  where "l ⊢ m" := (S_cll l m).

End S_cll_without_cut.

Definition rCLL_cf_PROVABILITY (S : (list ll_form) * (list ll_form)) := let (Γ,Δ) := S in S_cll_restr Γ Δ.
Definition CLL_cf_PROVABILITY (S : (list ll_form) * (list ll_form)) := let (Γ,Δ) := S in S_cll Γ Δ.
