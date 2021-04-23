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

(* * Intuitionistic Multiplicative Sub-Exponential Linear Logic 

      derived from  https://doi.org/10.1017/S0960129516000293 *)

Local Infix "~p" := (@Permutation _) (at level 70).

Reserved Notation "A ⊸ B" (at level 51, right associativity, format "A ⊸ B").
Reserved Notation "'![' m ']' x" (at level 52, format "![ m ] x").
Reserved Notation "‼ x" (at level 60, format "‼ x").

Section IMSELL.

  Variables (var bang : Type)
            (bang_le : bang -> bang -> Prop)   (* a pre-order on modalities *)
            (bang_U : bang -> Prop)            (* universal modalities have structural rules *)
            .

  Notation Λ := bang.

  Inductive imsell_form : Type :=
    | imsell_var  : var -> imsell_form
    | imsell_ban  : Λ -> imsell_form -> imsell_form
    | imsell_imp  : imsell_form -> imsell_form -> imsell_form.

  Infix "⊸" := imsell_imp.
  Notation "![ m ] x" := (imsell_ban m x).
  Notation "£" := imsell_var.

  Definition imsell_lban := map (fun '(m,A) => ![m]A).

  Notation "‼ Γ" := (imsell_lban Γ).
  Notation "u ≼ l" := (forall '(v,A), In (v,A) l -> bang_le u v) (at level 70).
  Notation U := bang_U.

  Reserved Notation "l ⊢ x" (at level 70, no associativity).

  (* We consider the (![.],-o) fragment of IMSELL without cut *)

  Inductive S_imsell : list imsell_form -> imsell_form -> Prop :=

    | in_imsell_ax A :                        A::nil ⊢ A          (* [identity] *)

    | in_imsell_perm Γ Δ A :  Γ ~p Δ ->            Γ ⊢ A 
                                    (*-----------------------------  [permutation] *)
                                ->                 Δ ⊢ A

    | in_imsell_limp_l Γ Δ A B C :      Γ ⊢ A      ->   B::Δ ⊢ C
                                    (*-----------------------------  [⊸L] *)
                                ->          A⊸B::Γ++Δ ⊢ C

    | in_imsell_limp_r Γ A B :                   A::Γ ⊢ B
                                    (*-----------------------------  [⊸R] *)
                                ->                  Γ ⊢ A⊸B

    | in_imsell_bang_l Γ m A B :                 A::Γ ⊢ B
                                    (*-----------------------------  [!L] *)
                                ->           ![m]A::Γ ⊢ B

    | in_imsell_bang_r Γ m A : m ≼ Γ ->            ‼Γ ⊢ A
                                    (*-----------------------------  [!R] *)
                                ->                 ‼Γ ⊢ ![m]A

    | in_imsell_weak Γ u A B : U u ->               Γ ⊢ B
                                    (*-----------------------------  [weakening] *)
                                ->           ![u]A::Γ ⊢ B

    | in_imsell_cntr Γ u A B : U u -> ![u]A::![u]A::Γ ⊢ B
                                    (*-----------------------------  [contraction] *)
                                ->           ![u]A::Γ ⊢ B

  where "Γ ⊢ A" := (S_imsell Γ A).

End IMSELL.

Infix "⊸" := imsell_imp.
Notation "![ m ] x" := (imsell_ban m x).
Notation "£" := imsell_var.
Notation "‼ Γ" := (imsell_lban Γ).

(* An IMSELL signature is a type of modalities pre-ordered
    and an upper-closed subset of exponentials *)

Record IMSELL_sig : Type :=
  { IMSELL_Λ :> Type; 
    IMSELL_le : IMSELL_Λ -> IMSELL_Λ -> Prop;
    IMSELL_refl : forall m, IMSELL_le m m;
    IMSELL_trans : forall u v w, IMSELL_le u v -> IMSELL_le v w -> IMSELL_le u w;
    IMSELL_U : IMSELL_Λ -> Prop;
    IMSELL_clos : forall u v, IMSELL_U u -> IMSELL_le u v -> IMSELL_U v
  }.

Section imsell3.

  (* The minimal signature for this undecidability proof 

     3 modalities {a,b,∞} with a,b < ∞ and ∞ is the only 
     universal modality *)

  Let bang := option bool.

  Let bang_le (u v : bang) :=
    match v with
      | None   => True
      | Some _ => u = v
    end.

  Let bang_U := @eq bang None.

  Definition imsell3 : IMSELL_sig.
  Proof.
    exists bang bang_le bang_U; trivial.
    all: repeat intros [[]|]; now simpl.
  Defined.

End imsell3.

Local Infix "≤" := (@IMSELL_le _) (at level 70).
Local Notation "u ≰ v" := (~ u ≤ v) (at level 70).
Local Notation U := (@IMSELL_U _).

Definition IMSELL_sig3 := 
  { S : IMSELL_sig | exists a b i : S, a ≤ i /\ b ≤ i /\ a ≰ b /\ b ≰ a 
                                    /\ ~ U a /\ ~ U b /\ U i }.

Definition IMSELL_problem (S : IMSELL_sig) := 
  let F := imsell_form nat (IMSELL_Λ S) in (list F * F)%type.

Definition IMSELL_problem3 (S : IMSELL_sig3) := IMSELL_problem (proj1_sig S). 

(* Cut-free provability over an IMSELL signature *)

Definition IMSELL_cf_PROVABILITY S (P : IMSELL_problem S) := 
  let (Γ,A) := P in S_imsell (IMSELL_le S) (IMSELL_U S) Γ A.

Definition IMSELL_cf_PROVABILITY3 S (P : IMSELL_problem3 S) := IMSELL_cf_PROVABILITY P.
