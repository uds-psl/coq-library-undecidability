(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia.

Set Implicit Arguments.

Section Non_deterministic_Minsky_Machines.

  Variables loc : Set.

  Inductive ndmm_instr : Set :=
    | ndmm_stop    : loc  -> ndmm_instr
    | ndmm_inc     : bool -> loc -> loc -> ndmm_instr
    | ndmm_dec     : bool -> loc -> loc -> ndmm_instr
    | ndmm_zero    : bool -> loc -> loc -> ndmm_instr.

  Notation STOP := ndmm_stop.
  Notation INC  := ndmm_inc.
  Notation DEC  := ndmm_dec.
  Notation ZERO := ndmm_zero.

  Variable P : list ndmm_instr.

  Reserved Notation "a ⊕ b ⊦ u" (at level 70, no associativity).

  Inductive ndmm_accept : nat -> nat -> loc -> Prop :=
    | in_ndmma_stop  : forall p,         In (STOP p) P         ->    0 ⊕   0 ⊦ p

    | in_ndmma_inc_1 : forall a b p q,   In (INC true p q) P   ->  1+a ⊕   b ⊦ p
                                                               ->    a ⊕   b ⊦ q
    | in_ndmma_inc_0 : forall a b p q,   In (INC false p q) P  ->    a ⊕ 1+b ⊦ p
                                                               ->    a ⊕   b ⊦ q

    | in_ndmma_dec_1 : forall a b p q,   In (DEC true p q) P   ->    a ⊕   b  ⊦ p
                                                               ->  1+a ⊕   b  ⊦ q
    | in_ndmma_dec_0 : forall a b p q,   In (DEC false p q) P  ->    a ⊕   b  ⊦ p
                                                               ->    a ⊕ 1+b  ⊦ q

    | in_ndmma_zero_1 : forall b p q,    In (ZERO true p q) P  ->    0 ⊕   b  ⊦ p
                                                               ->    0 ⊕   b  ⊦ q
    | in_ndmma_zero_0 : forall a p q,    In (ZERO false p q) P ->    a ⊕   0  ⊦ p
                                                               ->    a ⊕   0  ⊦ q

  where "a ⊕ b ⊦ p" := (ndmm_accept a b p).

End Non_deterministic_Minsky_Machines.

Definition ndMM2_problem loc := { P : list (ndmm_instr loc) & loc * (nat * nat) }%type.

Definition ndMM2_ACCEPT loc : ndMM2_problem loc -> Prop := 
  fun H => match H with existT _ P (p,(a,b)) => ndmm_accept P a b p end.



