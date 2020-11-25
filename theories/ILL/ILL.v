(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* Certified Undecidability of Intuitionistic Linear Logic via Binary Stack Machines and Minsky Machines. Yannick Forster and Dominique Larchey-Wendling. CPP '19. http://uds-psl.github.io/ill-undecidability/ *)

Require Import List Permutation.

Set Implicit Arguments.

(* * Intuionistic Linear Logic *)

Local Infix "~p" := (@Permutation _) (at level 70).

(* We consider four fragments of ILL:
    - the (!,-o,&) fragment with or without cut
    - full fragment with or without cut
*)

Notation ill_vars := nat.

Inductive ill_connective := ill_with | ill_limp | ill_times | ill_plus.
Inductive ill_constant := ill_1 | ill_bot | ill_top.

Inductive ill_form : Set :=
  | ill_var  : ill_vars -> ill_form
  | ill_cst  : ill_constant -> ill_form
  | ill_ban  : ill_form -> ill_form
  | ill_bin  : ill_connective -> ill_form -> ill_form -> ill_form.

(* Symbols for cut&paste ⟙   ⟘   𝝐  ﹠ ⊗  ⊕  ⊸  !   ‼  ∅  ⊢ *)

Notation "⟙" := (ill_cst ill_top).
Notation "⟘" := (ill_cst ill_bot).
Notation "𝟙" := (ill_cst ill_1).

Infix "&" := (ill_bin ill_with) (at level 50).
Infix "⊗" := (ill_bin ill_times) (at level 50).
Infix "⊕" := (ill_bin ill_plus) (at level 50).
Infix "⊸" := (ill_bin ill_limp) (at level 51, right associativity).

Notation "'!' x" := (ill_ban x) (at level 52).

Notation "£" := ill_var.

Notation "‼ x" := (map ill_ban x) (at level 60).

Notation "∅" := nil (only parsing).

Reserved Notation "l '⊢' x" (at level 70, no associativity).

Section S_ill_restr_without_cut.

  (* These are the SILL rules in the CPP'19 paper w/o the cut *)

  Inductive S_ill_restr : list ill_form -> ill_form -> Prop :=

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
                                      ->           A&B::Γ ⊢ C

    | in_ill1_with_l2 : forall Γ A B C,               B::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->           A&B::Γ ⊢ C
 
    | in_ill1_with_r : forall Γ A B,            Γ ⊢ A     ->   Γ ⊢ B
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A&B

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

  (* These are the SILL rules in the CPP'19 paper including the cut rule *)

  Inductive S_ill_restr_wc : list ill_form -> ill_form -> Prop :=

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
                                      ->           A&B::Γ ⊢ C

    | in_ill2_with_l2 : forall Γ A B C,               B::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->           A&B::Γ ⊢ C
 
    | in_ill2_with_r : forall Γ A B,            Γ ⊢ A     ->   Γ ⊢ B
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A&B

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

  (* These are the rules for the whole ILL, without cut *)

  Inductive S_ill : list ill_form -> ill_form -> Prop :=

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
                                      ->           A&B::Γ ⊢ C

    | in_ill3_with_l2 : forall Γ A B C,               B::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->           A&B::Γ ⊢ C
 
    | in_ill3_with_r : forall Γ A B,            Γ ⊢ A     ->   Γ ⊢ B
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A&B

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

  (* These are the rules for the whole ILL, without cut *)

  Inductive S_ill_wc : list ill_form -> ill_form -> Prop :=

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
                                      ->           A&B::Γ ⊢ C

    | in_ill4_with_l2 : forall Γ A B C,               B::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->           A&B::Γ ⊢ C
 
    | in_ill4_with_r : forall Γ A B,            Γ ⊢ A     ->   Γ ⊢ B
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A&B

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

Definition rILL_cf_PROVABILITY (S : _*_) := let (Γ,A) := S in S_ill_restr Γ A.
Definition rILL_PROVABILITY (S : _*_) := let (Γ,A) := S in S_ill_restr_wc Γ A. 

Definition ILL_cf_PROVABILITY (S : _*_) := let (Γ,A) := S in S_ill Γ A.
Definition ILL_PROVABILITY (S : _*_) := let (Γ,A) := S in S_ill_wc Γ A. 
