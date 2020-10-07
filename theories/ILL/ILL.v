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
Notation "𝟙" := (ll_zero ll_one).

Infix "&" := (ll_bin ll_with) (at level 50, only parsing).
Infix "﹠" := (ll_bin ll_with) (at level 50).
Infix "⊗" := (ll_bin ll_times) (at level 50).
Infix "⊕" := (ll_bin ll_plus) (at level 50).
(* Infix "-o" := (ll_bin ll_limp) (at level 51, only parsing, right associativity). *)
Infix "⊸" := (ll_bin ll_limp) (at level 51, right associativity).

Notation "'!' x" := (ll_ban x) (at level 52).
(* Notation "❗ x" := (ll_ban x) (at level 52). *)

Notation "£" := ll_var.

Definition ll_lbang := map (fun x => !x).

(* Notation "'!l' x" := (ll_lbang x) (at level 60, only parsing). *)
Notation "‼ x" := (ll_lbang x) (at level 60).

Notation "∅" := nil (only parsing).

Reserved Notation "l '⊢' x" (at level 70, no associativity).

Section S_ill_restr_without_cut.

  (** These are the SILL rules in the CPP'19 paper w/o the cut *)

  Inductive S_ill_restr : list ll_form -> ll_form -> Prop :=

    | in_ill1_ax     : forall A,                        A::∅ ⊢ A

    | in_ill1_perm   : forall Γ Δ A,              Γ ~p Δ     ->   Γ ⊢ A 
                                           (*-----------------------------*)
                                        ->                 Δ ⊢ A

    | in_ill1_limp_l : forall Γ Δ A B C,         Γ ⊢ A      ->   B::Δ ⊢ C
                                           (*-----------------------------*)    
                                      ->           A ⊸ B::Γ++Δ ⊢ C

    | in_ill1_limp_r : forall Γ A B,                  A::Γ ⊢ B
                                           (*-----------------------------*)
                                        ->            Γ ⊢ A ⊸ B

    | in_ill1_with_l1 : forall Γ A B C,               A::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->           A﹠B::Γ ⊢ C

    | in_ill1_with_l2 : forall Γ A B C,               B::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->           A﹠B::Γ ⊢ C
 
    | in_ill1_with_r : forall Γ A B,            Γ ⊢ A     ->   Γ ⊢ B
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A﹠B

    | in_ill1_bang_l : forall Γ A B,                   A::Γ ⊢ B
                                           (*-----------------------------*)
                                      ->              !A::Γ ⊢ B

    | in_ill1_bang_r : forall Γ A,                    ‼Γ ⊢ A
                                           (*-----------------------------*)
                                      ->              ‼Γ ⊢ !A

    | in_ill1_weak : forall Γ A B,                       Γ ⊢ B
                                           (*-----------------------------*)
                                      ->             !A::Γ ⊢ B

    | in_ill1_cntr : forall Γ A B,                 !A::!A::Γ ⊢ B
                                           (*-----------------------------*)
                                      ->               !A::Γ ⊢ B

  where "l ⊢ x" := (S_ill_restr l x).

End S_ill_restr_without_cut.

Section S_ill_restr_with_cut.

  (** These are the SILL rules in the CPP'19 paper including the cut rule *)

  Inductive S_ill_restr_wc : list ll_form -> ll_form -> Prop :=

    | in_ill2_ax     : forall A,                        A::∅ ⊢ A

    | in_ill2_cut : forall Γ Δ A B,              Γ ⊢ A    ->   A::Δ ⊢ B
                                           (*-----------------------------*)    
                                      ->              Γ++Δ ⊢ B

    | in_ill2_perm   : forall Γ Δ A,              Γ ~p Δ     ->   Γ ⊢ A 
                                           (*-----------------------------*)
                                        ->                 Δ ⊢ A

    | in_ill2_limp_l : forall Γ Δ A B C,         Γ ⊢ A      ->   B::Δ ⊢ C
                                           (*-----------------------------*)    
                                      ->           A ⊸ B::Γ++Δ ⊢ C

    | in_ill2_limp_r : forall Γ A B,                  A::Γ ⊢ B
                                           (*-----------------------------*)
                                        ->            Γ ⊢ A ⊸ B

    | in_ill2_with_l1 : forall Γ A B C,               A::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->           A﹠B::Γ ⊢ C

    | in_ill2_with_l2 : forall Γ A B C,               B::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->           A﹠B::Γ ⊢ C
 
    | in_ill2_with_r : forall Γ A B,            Γ ⊢ A     ->   Γ ⊢ B
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A﹠B

    | in_ill2_bang_l : forall Γ A B,                   A::Γ ⊢ B
                                           (*-----------------------------*)
                                      ->              !A::Γ ⊢ B

    | in_ill2_bang_r : forall Γ A,                    ‼Γ ⊢ A
                                           (*-----------------------------*)
                                      ->              ‼Γ ⊢ !A

    | in_ill2_weak : forall Γ A B,                       Γ ⊢ B
                                           (*-----------------------------*)
                                      ->             !A::Γ ⊢ B

    | in_ill2_cntr : forall Γ A B,                 !A::!A::Γ ⊢ B
                                           (*-----------------------------*)
                                      ->               !A::Γ ⊢ B

  where "l ⊢ x" := (S_ill_restr_wc l x).

End S_ill_restr_with_cut.

Section S_ill_without_cut.

  (** These are the rules for the whole ILL, without cut *)

  Inductive S_ill : list ll_form -> ll_form -> Prop :=

    | in_ill3_ax     : forall A,                        A::∅ ⊢ A

    | in_ill3_perm   : forall Γ Δ A,              Γ ~p Δ     ->   Γ ⊢ A 
                                           (*-----------------------------*)
                                        ->                 Δ ⊢ A

    | in_ill3_limp_l : forall Γ Δ A B C,         Γ ⊢ A      ->   B::Δ ⊢ C
                                           (*-----------------------------*)    
                                      ->           A ⊸ B::Γ++Δ ⊢ C

    | in_ill3_limp_r : forall Γ A B,                  A::Γ ⊢ B
                                           (*-----------------------------*)
                                        ->            Γ ⊢ A ⊸ B

    | in_ill3_with_l1 : forall Γ A B C,               A::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->           A﹠B::Γ ⊢ C

    | in_ill3_with_l2 : forall Γ A B C,               B::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->           A﹠B::Γ ⊢ C
 
    | in_ill3_with_r : forall Γ A B,            Γ ⊢ A     ->   Γ ⊢ B
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A﹠B

    | in_ill3_bang_l : forall Γ A B,                   A::Γ ⊢ B
                                           (*-----------------------------*)
                                      ->              !A::Γ ⊢ B

    | in_ill3_bang_r : forall Γ A,                    ‼Γ ⊢ A
                                           (*-----------------------------*)
                                      ->              ‼Γ ⊢ !A

    | in_ill3_weak : forall Γ A B,                       Γ ⊢ B
                                           (*-----------------------------*)
                                      ->             !A::Γ ⊢ B

    | in_ill3_cntr : forall Γ A B,                 !A::!A::Γ ⊢ B
                                           (*-----------------------------*)
                                      ->               !A::Γ ⊢ B

    | in_ill3_times_l : forall Γ A B C,            A::B::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->            A⊗B::Γ ⊢ C
 
    | in_ill3_times_r : forall Γ Δ A B,          Γ ⊢ A    ->   Δ ⊢ B
                                           (*-----------------------------*)
                                      ->              Γ++Δ ⊢ A⊗B

    | in_ill3_plus_l :  forall Γ A B C,         A::Γ ⊢ C  ->  B::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->            A⊕B::Γ ⊢ C

    | in_ill3_plus_r1 : forall Γ A B,                 Γ ⊢ A  
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A⊕B

    | in_ill3_plus_r2 : forall Γ A B,                 Γ ⊢ B  
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A⊕B

    | in_ill3_bot_l : forall Γ A,                  ⟘::Γ ⊢ A

    | in_ill3_top_r : forall Γ,                       Γ ⊢ ⟙

    | in_ill3_unit_l : forall Γ A,                    Γ ⊢ A  
                                           (*-----------------------------*)
                                      ->           𝟙::Γ ⊢ A

    | in_ill3_unit_r :                                ∅ ⊢ 𝟙

  where "l ⊢ x" := (S_ill l x).

End S_ill_without_cut.

Section S_ill_with_cut.

  (** These are the rules for the whole ILL, without cut *)

  Inductive S_ill_wc : list ll_form -> ll_form -> Prop :=

    | in_ill4_ax     : forall A,                        A::∅ ⊢ A

    | in_ill4_cut : forall Γ Δ A B,              Γ ⊢ A    ->   A::Δ ⊢ B
                                           (*-----------------------------*)    
                                      ->              Γ++Δ ⊢ B

    | in_ill4_perm   : forall Γ Δ A,              Γ ~p Δ     ->   Γ ⊢ A 
                                           (*-----------------------------*)
                                        ->                 Δ ⊢ A

    | in_ill4_limp_l : forall Γ Δ A B C,         Γ ⊢ A      ->   B::Δ ⊢ C
                                           (*-----------------------------*)    
                                      ->           A ⊸ B::Γ++Δ ⊢ C

    | in_ill4_limp_r : forall Γ A B,                  A::Γ ⊢ B
                                           (*-----------------------------*)
                                        ->            Γ ⊢ A ⊸ B

    | in_ill4_with_l1 : forall Γ A B C,               A::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->           A﹠B::Γ ⊢ C

    | in_ill4_with_l2 : forall Γ A B C,               B::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->           A﹠B::Γ ⊢ C
 
    | in_ill4_with_r : forall Γ A B,            Γ ⊢ A     ->   Γ ⊢ B
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A﹠B

    | in_ill4_bang_l : forall Γ A B,                   A::Γ ⊢ B
                                           (*-----------------------------*)
                                      ->              !A::Γ ⊢ B

    | in_ill4_bang_r : forall Γ A,                    ‼Γ ⊢ A
                                           (*-----------------------------*)
                                      ->              ‼Γ ⊢ !A

    | in_ill4_weak : forall Γ A B,                       Γ ⊢ B
                                           (*-----------------------------*)
                                      ->             !A::Γ ⊢ B

    | in_ill4_cntr : forall Γ A B,                 !A::!A::Γ ⊢ B
                                           (*-----------------------------*)
                                      ->               !A::Γ ⊢ B

    | in_ill4_times_l : forall Γ A B C,            A::B::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->            A⊗B::Γ ⊢ C
 
    | in_ill4_times_r : forall Γ Δ A B,          Γ ⊢ A    ->   Δ ⊢ B
                                           (*-----------------------------*)
                                      ->              Γ++Δ ⊢ A⊗B

    | in_ill4_plus_l :  forall Γ A B C,         A::Γ ⊢ C  ->  B::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->            A⊕B::Γ ⊢ C

    | in_ill4_plus_r1 : forall Γ A B,                 Γ ⊢ A  
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A⊕B

    | in_ill4_plus_r2 : forall Γ A B,                 Γ ⊢ B  
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A⊕B

    | in_ill4_bot_l : forall Γ A,                  ⟘::Γ ⊢ A

    | in_ill4_top_r : forall Γ,                       Γ ⊢ ⟙

    | in_ill4_unit_l : forall Γ A,                    Γ ⊢ A  
                                           (*-----------------------------*)
                                      ->           𝟙::Γ ⊢ A

    | in_ill4_unit_r :                                ∅ ⊢ 𝟙

  where "l ⊢ x" := (S_ill_wc l x).

End S_ill_with_cut.

Definition rILL_cf_PROVABILITY (c : (list ll_form) * ll_form) := let (Ga,A) := c in S_ill_restr Ga A.
Definition rILL_PROVABILITY (c : (list ll_form) * ll_form) := let (Ga,A) := c in S_ill_restr_wc Ga A. 

Definition ILL_cf_PROVABILITY (c : (list ll_form) * ll_form) := let (Ga,A) := c in S_ill Ga A.
Definition ILL_PROVABILITY (c : (list ll_form) * ll_form) := let (Ga,A) := c in S_ill_wc Ga A. 
