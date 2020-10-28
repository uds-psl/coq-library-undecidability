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

(** * Intuionistic Multiplicative Linear Logic with several exponentials and modabilities *)

Local Infix "~p" := (@Permutation _) (at level 70).

(** We consider  IMSELL:
    - the (!^,-o) fragment without cut
*)

Reserved Notation "A ⊸ B" (at level 51, right associativity).
Reserved Notation "'![' m ']' x" (at level 52, format "![ m ] x").
Reserved Notation "‼ x" (at level 60, format "‼ x").

Section IMSELL.

  Variables (var bang : Type)
            (bang_le : bang -> bang -> Prop)   (* a pre-order on modalities *)
            (bang_U : bang -> Prop)            (* universal modalities have structural rules *)
            . 

  Inductive imsell_form : Type :=
    | imsell_var  : var -> imsell_form
    | imsell_ban  : bang -> imsell_form -> imsell_form
    | imsell_imp  : imsell_form -> imsell_form -> imsell_form.

  Infix "⊸" := imsell_imp.
  Notation "![ m ] x" := (imsell_ban m x).
  Notation "£" := imsell_var.

  Definition imsell_lban := map (fun '(m,A) => ![m]A).

  Notation "‼ Γ" := (imsell_lban Γ).
  Notation "u ≼ l" := (forall '(v,A), In (v,A) l -> bang_le u v) (at level 70).
  Notation U := bang_U.

  Reserved Notation "l ⊢ x" (at level 70, no associativity).

  Inductive S_imsell : _ -> _ -> Prop :=

    | in_imsell_ax     : forall A,                        A::nil ⊢ A

    | in_imsell_perm   : forall Γ Δ A,              Γ ~p Δ     ->   Γ ⊢ A 
                                           (*-----------------------------*)
                                        ->                 Δ ⊢ A

    | in_imsell_limp_l : forall Γ Δ A B C,         Γ ⊢ A      ->   B::Δ ⊢ C
                                           (*-----------------------------*)    
                                      ->           A ⊸ B::Γ++Δ ⊢ C

    | in_imsell_limp_r : forall Γ A B,                  A::Γ ⊢ B
                                           (*-----------------------------*)
                                        ->            Γ ⊢ A ⊸ B

    | in_imsell_bang_l : forall m Γ A B,                 A::Γ ⊢ B
                                           (*-----------------------------*)
                                      ->           ![m]A::Γ ⊢ B

    | in_imsell_bang_r : forall m Γ A,            m ≼ Γ    ->     ‼Γ ⊢ A
                                           (*-----------------------------*)
                                      ->              ‼Γ ⊢ ![m]A

    | in_imsell_weak : forall u Γ A B,              U u    ->   Γ ⊢ B
                                           (*-----------------------------*)
                                      ->             ![u]A::Γ ⊢ B

    | in_imsell_cntr : forall u Γ A B,         U u  -> ![u]A::![u]A::Γ ⊢ B
                                           (*-----------------------------*)
                                      ->               ![u]A::Γ ⊢ B

  where "Γ ⊢ A" := (S_imsell Γ A).

End IMSELL.

Record IMSELL_sig : Type :=
  { IMSELL_Λ : Type; 
    IMSELL_le : IMSELL_Λ -> IMSELL_Λ -> Prop;
    IMSELL_refl : forall m, IMSELL_le m m;
    IMSELL_trans : forall u v w, IMSELL_le u v -> IMSELL_le v w -> IMSELL_le u w;
    IMSELL_U : IMSELL_Λ -> Prop;
    IMSELL_clos : forall u v, IMSELL_U u -> IMSELL_le u v -> IMSELL_U v
  }.

Definition IMSELL_problem (S : IMSELL_sig) := 
  let F := imsell_form nat (IMSELL_Λ S) 
  in (list F * F)%type.

(* Cut-free provability over an IMSELL signature *)

Definition IMSELL_cf_provable S (P : IMSELL_problem S) := 
  let (Γ,A) := P 
  in S_imsell (IMSELL_le S) (IMSELL_U S) Γ A.
 

