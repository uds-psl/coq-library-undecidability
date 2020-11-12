(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.

Set Implicit Arguments.

Section Non_deterministic_Minsky_Machines.

  (* locations: index type for instructions, normally is nat *)

  Variables loc : Set.

  (* four instructions: STOP, INC, DEC and ZERO (test) 

     only two nat valued registers, indexed with bool
     ie true/α of which the values are denoted "a" below
     and false/β of which the values are denoted "b" below 

     In any of the cases above, several instructions can 
     co-exist at a given location, hence, no instruction
     can stop the computation by itself. This model is
     inherently no-deterministic.

     STOP p:     accepts location p when α = β = 0
     INC x p q:  at location p, x += 1 and jumps to location q
     DEC x p q:  at location p, x -= 1 (if possible) and jumps to location q
                 if x is already 0 then this instruction cannot compute
     ZERO x p q: at location p, jumps to location q when x = 0 

     *)

  Inductive ndmm2_instr : Set :=
    | ndmm2_stop    : loc  -> ndmm2_instr
    | ndmm2_inc     : bool -> loc -> loc -> ndmm2_instr
    | ndmm2_dec     : bool -> loc -> loc -> ndmm2_instr
    | ndmm2_zero    : bool -> loc -> loc -> ndmm2_instr.

  Notation α := true. 
  Notation β := false.

  Notation STOP := ndmm2_stop.
  Notation INC  := ndmm2_inc.
  Notation DEC  := ndmm2_dec.
  Notation ZERO := ndmm2_zero.

  Infix "∊" := In (at level 70).

  (* Programs are non-deterministic and described by 
     a (finite) list of instructions 

     Notice that eg 

          [ STOP 0 ; INC α 0 4 ; DEC β 0 2 ]

     can both accept location 0 (if α = β = 0)
     or increment α and jump to location 4
     or decrement β (if not zero already) and jump to location 2

     Also repetitions and order do not matter hence these
     lists are viewed as finite sets, see ndmm2_accept_mono 
     in ndMM2/ndmm2_utils.v
  *)

  Reserved Notation "Σ // a ⊕ b ⊦ u" (at level 70, no associativity).

  (* Σ // a ⊕ b ⊦ u denotes 

         "Σ accepts the initial location u with values α:=a and β:=b"

    This big step semantics only describes the overall accepts predicate
    and does not capture output values.

   *)

  Inductive ndmm2_accept (Σ : list ndmm2_instr) : nat -> nat -> loc -> Prop :=

    | in_ndmm2a_stop  : forall p,         STOP p ∊ Σ      ->  Σ //   0 ⊕   0 ⊦ p

    | in_ndmm2a_inc_1 : forall a b p q,   INC α p q ∊ Σ   ->  Σ // 1+a ⊕   b ⊦ q
                                                          ->  Σ //   a ⊕   b ⊦ p

    | in_ndmm2a_inc_0 : forall a b p q,   INC β p q ∊ Σ   ->  Σ //   a ⊕ 1+b ⊦ q
                                                          ->  Σ //   a ⊕   b ⊦ p

    | in_ndmm2a_dec_1 : forall a b p q,   DEC α p q ∊ Σ   ->  Σ //   a ⊕   b ⊦ q
                                                          ->  Σ // 1+a ⊕   b ⊦ p

    | in_ndmm2a_dec_0 : forall a b p q,   DEC β p q ∊ Σ   ->  Σ //   a ⊕   b ⊦ q
                                                          ->  Σ //   a ⊕ 1+b ⊦ p

    | in_ndmm2a_zero_1 : forall b p q,    ZERO α p q ∊ Σ  ->  Σ //   0 ⊕   b ⊦ q
                                                          ->  Σ //   0 ⊕   b ⊦ p

    | in_ndmm2a_zero_0 : forall a p q,    ZERO β p q ∊ Σ  ->  Σ //   a ⊕   0 ⊦ q
                                                          ->  Σ //   a ⊕   0 ⊦ p

  where "Σ // a ⊕ b ⊦ u" := (ndmm2_accept Σ a b u).

  (* A problem is a program, a start location and initial values for α/β *)

  Definition ndMM2_problem := { Σ : list ndmm2_instr & loc * (nat * nat) }%type.

  Definition ndMM2_ACCEPT (i : ndMM2_problem) : Prop := 
    match i with existT _ Σ (u,(a,b)) => Σ // a ⊕ b ⊦ u end.

End Non_deterministic_Minsky_Machines.




