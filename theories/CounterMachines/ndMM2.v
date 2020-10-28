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

  Inductive ndmm2_instr : Set :=
    | ndmm2_stop    : loc  -> ndmm2_instr
    | ndmm2_inc     : bool -> loc -> loc -> ndmm2_instr
    | ndmm2_dec     : bool -> loc -> loc -> ndmm2_instr
    | ndmm2_zero    : bool -> loc -> loc -> ndmm2_instr.

  Notation STOP := ndmm2_stop.
  Notation INC  := ndmm2_inc.
  Notation DEC  := ndmm2_dec.
  Notation ZERO := ndmm2_zero.

  Variable P : list ndmm2_instr.

  Reserved Notation "a ⊕ b ⊦ u" (at level 70, no associativity).

  Inductive ndmm2_accept : nat -> nat -> loc -> Prop :=
    | in_ndmm2a_stop  : forall p,         In (STOP p) P         ->    0 ⊕   0 ⊦ p

    | in_ndmm2a_inc_1 : forall a b p q,   In (INC true p q) P   ->  1+a ⊕   b ⊦ p
                                                                ->    a ⊕   b ⊦ q
    | in_ndmm2a_inc_0 : forall a b p q,   In (INC false p q) P  ->    a ⊕ 1+b ⊦ p
                                                                ->    a ⊕   b ⊦ q

    | in_ndmm2a_dec_1 : forall a b p q,   In (DEC true p q) P   ->    a ⊕   b  ⊦ p
                                                                ->  1+a ⊕   b  ⊦ q
    | in_ndmm2a_dec_0 : forall a b p q,   In (DEC false p q) P  ->    a ⊕   b  ⊦ p
                                                                ->    a ⊕ 1+b  ⊦ q

    | in_ndmm2a_zero_1 : forall b p q,    In (ZERO true p q) P  ->    0 ⊕   b  ⊦ p
                                                                ->    0 ⊕   b  ⊦ q
    | in_ndmm2a_zero_0 : forall a p q,    In (ZERO false p q) P ->    a ⊕   0  ⊦ p
                                                                ->    a ⊕   0  ⊦ q

  where "a ⊕ b ⊦ p" := (ndmm2_accept a b p).

End Non_deterministic_Minsky_Machines.

Definition ndMM2_problem loc := { P : list (ndmm2_instr loc) & loc * (nat * nat) }%type.

Definition ndMM2_ACCEPT loc : ndMM2_problem loc -> Prop := 
  fun H => match H with existT _ P (p,(a,b)) => ndmm2_accept P a b p end.



