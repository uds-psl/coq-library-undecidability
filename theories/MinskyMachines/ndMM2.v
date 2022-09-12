(*************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(*************************************************************)

Require Import List.

Set Implicit Arguments.

Section Non_deterministic_Minsky_Machines.

  (* locations: index type for instructions, normally is nat *)

  Variables loc : Set.

  (* four instructions: STOPₙ, INCₙ, DECₙ and ZEROₙ (test) 

     only two nat valued registers, indexed with bool
     ie true/α of which the values are denoted "a" below
     and false/β of which the values are denoted "b" below 

     In any of the cases above, several instructions can 
     co-exist at a given location, hence, no instruction
     can stop the computation by itself. This model is
     inherently no-deterministic.

     STOPₙ p:     accepts location p when α = β = 0
     INCₙ x p q:  at location p, x += 1 and jumps to location q
     DECₙ x p q:  at location p, x -= 1 (if possible) and jumps to location q
                  if x is already 0 then this instruction cannot compute
     ZEROₙ x p q: at location p, jumps to location q when x = 0 

     *)

  Inductive ndmm2_instr : Set :=
    | ndmm2_stop    : loc  -> ndmm2_instr
    | ndmm2_inc     : bool -> loc -> loc -> ndmm2_instr
    | ndmm2_dec     : bool -> loc -> loc -> ndmm2_instr
    | ndmm2_zero    : bool -> loc -> loc -> ndmm2_instr.

  Notation α := true. 
  Notation β := false.

  Notation STOPₙ := ndmm2_stop.
  Notation INCₙ  := ndmm2_inc.
  Notation DECₙ  := ndmm2_dec.
  Notation ZEROₙ := ndmm2_zero.

  Infix "∊" := In (at level 70).

  (* Programs are non-deterministic and described by 
     a (finite) list of instructions 

     Notice that eg 

          [ STOPₙ 0 ; INCₙ α 0 4 ; DECₙ β 0 2 ]

     can both accept location 0 (if α = β = 0)
     or increment α and jump to location 4
     or decrement β (if not zero already) and jump to location 2

     Also repetitions and order do not matter hence these
     lists are viewed as finite sets, see ndmm2_accept_mono 
     in ndMM2/ndmm2_utils.v
  *)

  Reserved Notation "Σ //ₙ a ⊕ b ⊦ u" (at level 70, no associativity).

  (* Σ //ₙ a ⊕ b ⊦ u denotes 

         "Σ accepts the initial location u with values α:=a and β:=b"

    This big step semantics only describes the overall accepts predicate
    and does not capture output values.

   *)

  Inductive ndmm2_accept (Σ : list ndmm2_instr) : nat -> nat -> loc -> Prop :=

    | in_ndmm2a_stop  : forall p,         STOPₙ p ∊ Σ      ->  Σ //ₙ   0 ⊕   0 ⊦ p

    | in_ndmm2a_inc_a : forall a b p q,   INCₙ α p q ∊ Σ   ->  Σ //ₙ 1+a ⊕   b ⊦ q
                                                           ->  Σ //ₙ   a ⊕   b ⊦ p

    | in_ndmm2a_inc_b : forall a b p q,   INCₙ β p q ∊ Σ   ->  Σ //ₙ   a ⊕ 1+b ⊦ q
                                                           ->  Σ //ₙ   a ⊕   b ⊦ p

    | in_ndmm2a_dec_a : forall a b p q,   DECₙ α p q ∊ Σ   ->  Σ //ₙ   a ⊕   b ⊦ q
                                                           ->  Σ //ₙ 1+a ⊕   b ⊦ p

    | in_ndmm2a_dec_b : forall a b p q,   DECₙ β p q ∊ Σ   ->  Σ //ₙ   a ⊕   b ⊦ q
                                                           ->  Σ //ₙ   a ⊕ 1+b ⊦ p

    | in_ndmm2a_zero_a : forall b p q,    ZEROₙ α p q ∊ Σ  ->  Σ //ₙ   0 ⊕   b ⊦ q
                                                           ->  Σ //ₙ   0 ⊕   b ⊦ p

    | in_ndmm2a_zero_b : forall a p q,    ZEROₙ β p q ∊ Σ  ->  Σ //ₙ   a ⊕   0 ⊦ q
                                                           ->  Σ //ₙ   a ⊕   0 ⊦ p

  where "Σ //ₙ a ⊕ b ⊦ u" := (ndmm2_accept Σ a b u).

  (* A problem is a program, a start location and initial values for α/β *)

  Definition ndMM2_problem := { Σ : list ndmm2_instr & loc * (nat * nat) }%type.

  Definition ndMM2_ACCEPT (i : ndMM2_problem) : Prop := 
    match i with existT _ Σ (u,(a,b)) => Σ //ₙ a ⊕ b ⊦ u end.

End Non_deterministic_Minsky_Machines.




