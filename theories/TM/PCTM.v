(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import List Bool.

From Undecidability.Shared.Libs.DLW 
  Require Import sss.

From Undecidability.TM
  Require Import SBTM.

Import SBTMNotations (tape).

Set Implicit Arguments.

(** * Halting problem for (micro-programmed) Turing machines with a PC counter *)

(* Three instructions: MV d | WR b | BR i j *)
Inductive pctm_instr : Set :=
  | pctm_mv  : direction -> pctm_instr
  | pctm_wr  : bool -> pctm_instr
  | pctm_br  : nat -> nat -> pctm_instr
  .

Module PCTMNotations.

  Notation MV  := pctm_mv.
  Notation WR  := pctm_wr.
  Notation BR  := pctm_br.

  Notation JMP j := (BR j j).

  Definition rd (t : tape) : bool   := let '(_,b,_) := t in b.
  Definition wr (t : tape) b : tape := let '(l,_,r) := t in (l,b,r).

End PCTMNotations.

Import PCTMNotations SBTMNotations.

(* ** Small-step semantics for PC based TM *)

(* state is a value for the PC value and a tape *) 
Definition pctm_state := (nat * tape)%type.

(**    ρ // (i,t₁) -1> (j,t₂) 
    means instruction ρ at PC i transforms 
    the state (i,t₁) into the state (j,t₂) *)

Inductive pctm_sss : pctm_instr -> pctm_state -> pctm_state -> Prop :=
  | pctm_sss_mv d i t :      MV d // (i,t) -1> (1+i,mv d t)       (* mv is from the TM/SBTM.v *)
  | pctm_sss_wr b i t :      WR b // (i,t) -1> (1+i,wr t b)
  | pctm_sss_br i j p t :  BR j p // (i,t) -1> (if rd t then j else p,t)
where "ρ // s -1> t" := (pctm_sss ρ s t).

(** when P = (i,l) with (i = start PC value for instructions in l) 
                  and  (l = list of instructions)
   P // s ↓ means repeating steps as above in P, starting from s,
   eventually leads to a PC value outside of P

   Notice that this is equivalent to termination because the PCTM
   small steps semantics is total, ie if there is an instruction at
   the current PC, then a computation step can occur: no instruction
   is blocking *)

#[local] Notation "P // s ↓" := (sss_terminates pctm_sss P s).

(* ** The Halting problem for PCTM *)
  
Definition PCTM_PROBLEM := (list pctm_instr * tape)%type.

Definition PCTM_HALT (Q : PCTM_PROBLEM) :=
  let (P,t) := Q in (1,P) // (1,t) ↓.
