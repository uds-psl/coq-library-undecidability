(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* Certified Undecidability of Intuitionistic Linear Logic via Binary Stack Machines and Minsky Machines. Yannick Forster and Dominique Larchey-Wendling. CPP '19. http://uds-psl.github.io/ill-undecidability/ *)

From Undecidability.Shared.Libs.DLW
  Require Import Vec.pos Vec.vec Code.sss.

Set Implicit Arguments.

(** * Halting problem for Minsky machines MM_HALTING  *)

(* * Minsky Machines (MM)

    A Minsky machine has n registers and there are just two instructions
 
    1/ INC x   : increment register x by 1
    2/ DEC x k : decrement register x by 1 if x > 0
                 or jump to k if x = 0

  *)

(* * Alternate Minsky Machines (MMA) such that two counters are enough for undec

    Minsky machine has n registers and there are just two instructions
 
    1/ INC x   : increment register x by 1
    2/ DEC x k : if x > 0 then decrement register x by 1 and jump to k

    If no jump occurs, then implicitly, the jump is to the next instruction

    We show that they simulated FRACTRAN
  *)

Inductive mm_instr (X : Set) : Set :=
  | mm_inc : X -> mm_instr X
  | mm_dec : X -> nat -> mm_instr X
  .

Notation INC := mm_inc.
Notation DEC := mm_dec.

Notation INCₐ := mm_inc.
Notation DECₐ := mm_dec.


(* ** Semantics for MM, restricted to X = pos n for some n *)

Section Minsky_Machine.

  Variable (n : nat).

  Definition mm_state := (nat*vec nat n)%type.

  Local Notation "e #> x" := (vec_pos e x).
  Local Notation "e [ v / x ]" := (vec_change e x v).

  (* Minsky machine small step semantics *)

  Inductive mm_sss : mm_instr (pos n) -> mm_state -> mm_state -> Prop :=
    | in_mm_sss_inc   : forall i x v,                   INC x   // (i,v) -1> (1+i,v[(S (v#>x))/x])
    | in_mm_sss_dec_0 : forall i x k v,   v#>x = O   -> DEC x k // (i,v) -1> (k,v)
    | in_mm_sss_dec_1 : forall i x k v u, v#>x = S u -> DEC x k // (i,v) -1> (1+i,v[u/x])
  where "i // s -1> t" := (mm_sss i s t).

  (* Minsky machine alternate small step semantics *)

  Inductive mma_sss : mm_instr (pos n) -> mm_state -> mm_state -> Prop :=
    | in_mma_sss_inc   : forall i x v,                   INCₐ x   // (i,v) -1> (1+i,v[(S (v#>x))/x])
    | in_mma_sss_dec_0 : forall i x k v,   v#>x = O   -> DECₐ x k // (i,v) -1> (1+i,v)
    | in_mma_sss_dec_1 : forall i x k v u, v#>x = S u -> DECₐ x k // (i,v) -1> (k,v[u/x])
  where "i // s -1> t" := (mma_sss i s t).

End Minsky_Machine.

Section MM_problems.

  Notation "P // s ~~> t" := (sss_output (@mm_sss _) P s t).
  Notation "P // s ↓" := (sss_terminates (@mm_sss _) P s). 

  Definition MM_PROBLEM := { n : nat & { P : list (mm_instr (pos n)) & vec nat n } }.

  Definition MM_HALTS_ON_ZERO (P : MM_PROBLEM) := 
    match P with existT _ n (existT _ P v) => (1,P) // (1,v) ~~> (0,vec_zero) end.

  Definition MM_HALTING (P : MM_PROBLEM) :=
    match P with existT _ n (existT _ P v) => (1, P) // (1, v) ↓ end.

End MM_problems.

Section MMA_problems.

  Notation "P // s ~~> t" := (sss_output (@mma_sss _) P s t).
  Notation "P // s ↓" := (sss_terminates (@mma_sss _) P s). 

  Definition MMA2_PROBLEM := (list (mm_instr (pos 2)) * vec nat 2)%type.

  Definition MMA2_HALTS_ON_ZERO (P : MMA2_PROBLEM) := (1,fst P) // (1,snd P) ~~> (0,vec_zero).
  Definition MMA2_HALTING (P : MMA2_PROBLEM) := (1,fst P) // (1,snd P) ↓.

End MMA_problems.
