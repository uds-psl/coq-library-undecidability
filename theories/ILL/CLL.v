(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Permutation Arith.

From Undecidability.ILL Require Import ILL.

Set Implicit Arguments.

Local Infix "~p" := (@Permutation _) (at level 70).

Inductive cll_connective := cll_with | cll_plus | cll_limp | cll_times | cll_par.
Inductive cll_constant := cll_1 | cll_0 | cll_bot | cll_top.
Inductive cll_modality := cll_bang | cll_qmrk | cll_neg.

Abbreviation cll_vars := nat.

Inductive cll_form : Set :=
  | cll_var  : cll_vars -> cll_form
  | cll_cst  : cll_constant  -> cll_form
  | cll_una  : cll_modality -> cll_form -> cll_form
  | cll_bin  : cll_connective -> cll_form -> cll_form -> cll_form.

(* Symbols for cut&paste ⟙   ⟘  𝟙 ﹠ ⊗  ⊕  ⊸ ! ‼ ‽ ⁇ ∅  ⊢ *)

(* These notations replace the ILL notations *)

Module CLL_notations.

  (* Variables *)

  Notation "£" := cll_var.

  (* Constants *)

  Notation "⟙" := (cll_cst cll_top).
  Notation "⟘" := (cll_cst cll_bot).
  Notation "𝟙" := (cll_cst cll_1).
  Notation "𝟘" := (cll_cst cll_0).

  (* Unary connectives: linear negation and modalities *)
  (* ? cannot be used because it is reserved by Coq so we use ‽ instead *)

  Notation "'⊖' x" := (cll_una cll_neg x) (at level 50, format "⊖ x").
  Notation "'!' x" := (cll_una cll_bang x) (at level 52).
  Notation "'‽' x" := (cll_una cll_qmrk x) (at level 52).

  (* Binary connectives *)

  Infix "&" := (cll_bin cll_with) (at level 50).
  Infix "⅋" := (cll_bin cll_par) (at level 50).
  Infix "⊗" := (cll_bin cll_times) (at level 50).
  Infix "⊕" := (cll_bin cll_plus) (at level 50).
  Infix "⊸" := (cll_bin cll_limp) (at level 51, right associativity).

  (* Modalities iterated over lists *)

  Notation "‼ x" := (map (cll_una cll_bang) x) (at level 60).
  Notation "⁇ x" := (map (cll_una cll_qmrk) x) (at level 60).

End CLL_notations.

Import CLL_notations.

(* The empty list *)

#[local] Notation "∅" := nil.
#[local] Reserved Notation "Γ ⊢ Δ" (at level 70, no associativity).

Section S_cll_restr_without_cut.

  (* CLL rules restricted to the (!,&,-o) fragment without cut *)

  Inductive S_cll_restr : list cll_form -> list cll_form -> Prop :=

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
                                      ->           A&B::Γ ⊢ Δ

    | in_cll1_with_l2 : forall Γ Δ A B,              B::Γ ⊢ Δ 
                                           (*-----------------------------*)
                                      ->           A&B::Γ ⊢ Δ
 
    | in_cll1_with_r : forall Γ Δ A B,        Γ ⊢ A::Δ     ->   Γ ⊢ B::Δ
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A&B::Δ

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

Section S_cll_without_cut_on_ill_syntax.

  (* CLL rules restricted to the (𝟘,?,⅋) free fragment without cut 
      which shares the same formula language as ILL, but of course 
      not the same rules *)

  Inductive S_cll_2 : list cll_form -> list cll_form -> Prop :=

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
                                      ->           A&B::Γ ⊢ Δ

    | in_cll2_with_l2 : forall Γ Δ A B,              B::Γ ⊢ Δ 
                                           (*-----------------------------*)
                                      ->           A&B::Γ ⊢ Δ
 
    | in_cll2_with_r : forall Γ Δ A B,        Γ ⊢ A::Δ     ->   Γ ⊢ B::Δ
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A&B::Δ

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

  where "l ⊢ m" := (S_cll_2 l m).

End S_cll_without_cut_on_ill_syntax.

Section cut_free_cll.

  (* All the rules of Cut-free CLL *)

  Reserved Notation "Γ ⊢ Δ" (at level 70, no associativity).

  Inductive S_cll : list cll_form -> list cll_form -> Prop :=

    | in_cll_ax    : forall A,                         A::∅ ⊢ A::∅

(*
    | in_cll_cut   : forall Γ Δ Γ' Δ' A,        Γ ⊢ A::Δ    ->   A::Γ' ⊢ Δ'
                                             (*-----------------------------*)
                                        ->           Γ++Γ' ⊢ Δ++Δ'
*)

    | in_cll_perm  : forall Γ Δ Γ' Δ',        Γ ~p Γ'  ->  Δ ~p Δ'  ->  Γ ⊢ Δ 
                                             (*-----------------------------*)
                                        ->              Γ' ⊢ Δ'

    | in_cll_neg_l :   forall Γ Δ A,                    Γ ⊢ A::Δ
                                             (*-----------------------------*)
                                        ->          ⊖A::Γ ⊢ Δ

    | in_cll_neg_r :   forall Γ Δ A,                 A::Γ ⊢ Δ
                                             (*-----------------------------*)
                                        ->              Γ ⊢ ⊖A::Δ


    | in_cll_limp_l : forall Γ Δ Γ' Δ' A B,   Γ ⊢ A::Δ      ->   B::Γ' ⊢ Δ'
                                             (*-----------------------------*)
                                        ->         A ⊸ B::Γ++Γ' ⊢ Δ++Δ'

    | in_cll_limp_r : forall Γ Δ A B,                 A::Γ ⊢ B::Δ
                                             (*-----------------------------*)
                                        ->            Γ ⊢ A ⊸ B::Δ

    | in_cll_with_l1 : forall Γ Δ A B,                  A::Γ ⊢ Δ 
                                             (*-----------------------------*)
                                        ->           A&B::Γ ⊢ Δ

    | in_cll_with_l2 : forall Γ Δ A B,                  B::Γ ⊢ Δ 
                                             (*-----------------------------*)
                                        ->           A&B::Γ ⊢ Δ
 
    | in_cll_with_r : forall Γ Δ A B,          Γ ⊢ A::Δ     ->   Γ ⊢ B::Δ
                                             (*-----------------------------*)
                                        ->              Γ ⊢ A&B::Δ

    | in_cll_times_l : forall Γ A B Δ,               A::B::Γ ⊢ Δ 
                                             (*-----------------------------*)
                                        ->            A⊗B::Γ ⊢ Δ
 
    | in_cll_times_r : forall Γ Δ Γ' Δ' A B,   Γ ⊢ A::Δ    ->   Γ' ⊢ B::Δ'
                                             (*-----------------------------*)
                                        ->         Γ++Γ' ⊢ A⊗B::Δ++Δ'

    | in_cll_par_l : forall Γ Δ Γ' Δ' A B,     A::Γ ⊢ Δ    ->   B::Γ' ⊢ Δ'
                                             (*-----------------------------*)
                                        ->         A⅋B::Γ++Γ' ⊢ Δ++Δ'

    | in_cll_par_r : forall Γ A B Δ,                   Γ ⊢ A::B::Δ 
                                             (*-----------------------------*)
                                        ->             Γ ⊢ A⅋B::Δ

    | in_cll_plus_l :  forall Γ A B Δ,          A::Γ ⊢ Δ  ->  B::Γ ⊢ Δ 
                                             (*-----------------------------*)
                                        ->          A⊕B::Γ ⊢ Δ

    | in_cll_plus_r1 : forall Γ A B Δ,                  Γ ⊢ A::Δ  
                                             (*-----------------------------*)
                                        ->              Γ ⊢ A⊕B::Δ

    | in_cll_plus_r2 : forall Γ A B Δ,                  Γ ⊢ B::Δ  
                                             (*-----------------------------*)
                                        ->              Γ ⊢ A⊕B::Δ

    | in_cll_bot_l : forall Γ Δ,                     ⟘::Γ ⊢ Δ

    | in_cll_top_r : forall Γ Δ,                        Γ ⊢ ⟙::Δ

    | in_cll_unit_l : forall Γ Δ,                       Γ ⊢ Δ  
                                             (*-----------------------------*)
                                        ->           𝟙::Γ ⊢ Δ

    | in_cll_unit_r :                                   ∅ ⊢ 𝟙::∅

    | in_cll_zero_l :                        (*-----------------------------*)
                                             (* *)      𝟘::∅ ⊢ ∅

    | in_cll_zero_r : forall Γ Δ,                       Γ ⊢ Δ  
                                             (*-----------------------------*)
                                        ->              Γ ⊢ 𝟘::Δ


    | in_cll_bang_l : forall Γ A Δ,                    A::Γ ⊢ Δ
                                             (*-----------------------------*)
                                        ->            !A::Γ ⊢ Δ

    | in_cll_bang_r : forall Γ A Δ,                     ‼Γ ⊢ A::⁇Δ
                                             (*-----------------------------*)
                                        ->              ‼Γ ⊢ !A::⁇Δ

    | in_cll_qmrk_l : forall Γ A Δ,                     A::‼Γ ⊢ ⁇Δ
                                             (*-----------------------------*)
                                        ->              ‽A::‼Γ ⊢ ⁇Δ

    | in_cll_qmrk_r : forall Γ A Δ,                    Γ ⊢ A::Δ
                                             (*-----------------------------*)
                                        ->             Γ ⊢ ‽A::Δ

    | in_cll_weak_l : forall Γ A Δ,                      Γ ⊢ Δ
                                             (*-----------------------------*)
                                        ->           !A::Γ ⊢ Δ

    | in_cll_weak_r : forall Γ A Δ,                      Γ ⊢ Δ
                                             (*-----------------------------*)
                                        ->               Γ ⊢ ‽A::Δ

    | in_cll_cntr_l : forall Γ A Δ,                !A::!A::Γ ⊢ Δ
                                             (*-----------------------------*)
                                        ->             !A::Γ ⊢ Δ

    | in_cll_cntr_r : forall Γ A Δ,                    Γ ⊢ ‽A::‽A::Δ
                                             (*-----------------------------*)
                                        ->             Γ ⊢ ‽A::Δ

  where "Γ ⊢ Δ" := (S_cll Γ Δ).

End cut_free_cll.

Definition rCLL_cf_PROVABILITY (S : _*_) := let (Γ,Δ) := S in S_cll_restr Γ Δ.
Definition CLL_cf_PROVABILITY (S : _*_) := let (Γ,Δ) := S in S_cll Γ Δ.
