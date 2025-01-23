(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Certified Undecidability of Intuitionistic Linear Logic via Binary Stack Machines and Minsky Machines. Yannick Forster and Dominique Larchey-Wendling. CPP '19. http://uds-psl.github.io/ill-undecidability/ *)

From Undecidability.Shared.Libs.DLW
  Require Import Vec.pos Vec.vec Code.sss.

Require Import Undecidability.MinskyMachines.MM.

Set Implicit Arguments.

(** * Halting problem for Minsky machines  *)

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
(* 
Inductive mm_instr (X : Set) : Set :=
  | mm_inc : X -> mm_instr X
  | mm_dec : X -> nat -> mm_instr X
  . *)

Notation INCₐ := mm_inc.
Notation DECₐ := mm_dec.


(* ** Semantics for MM, restricted to X = pos n for some n *)

Section Minsky_Machine.

  Variable (n : nat).

  Definition mm_state := (nat*vec nat n)%type.

  Notation "e '#>' x" := (vec_pos e x) (at level 58, format "e #> x").
  Notation "e [ x := v ]" := (vec_change e x v) (no associativity, at level 1).

  (* Minsky machine alternate small step semantics *)

  Inductive mma_sss : mm_instr (pos n) -> mm_state -> mm_state -> Prop :=
    | in_mma_sss_inc   : forall i x v,                   INCₐ x   // (i,v) -1> (1+i,v[x:=S (v#>x)])
    | in_mma_sss_dec_0 : forall i x k v,   v#>x = O   -> DECₐ x k // (i,v) -1> (1+i,v)
    | in_mma_sss_dec_1 : forall i x k v u, v#>x = S u -> DECₐ x k // (i,v) -1> (k,v[x:=u])
  where "i // s -1> t" := (mma_sss i s t).

End Minsky_Machine.

From Stdlib Require Import Vector.
Import VectorNotations.

Section MMA_problems.

  Notation "P // s ~~> t" := (sss_output (@mma_sss _) P s t).
  Notation "P // s ↓" := (sss_terminates (@mma_sss _) P s). 

  Definition MMA_PROBLEM n := (list (mm_instr (pos n)) * vec nat n)%type.

  Definition MMA_HALTS_ON_ZERO {n} (P : MMA_PROBLEM n) := (1,fst P) // (1,snd P) ~~> (0,vec_zero).
  Definition MMA_HALTING {n} (P : MMA_PROBLEM n) := (1,fst P) // (1,snd P) ↓.

  Definition MMA2_PROBLEM := MMA_PROBLEM 2.

  Definition MMA2_HALTS_ON_ZERO := @MMA_HALTS_ON_ZERO 2.
  Definition MMA2_HALTING := @MMA_HALTING 2.

  Definition MMA_computable {k} (R : Vector.t nat k -> nat -> Prop) :=
  exists n : nat, exists P : list (mm_instr (Fin.t (1 + k + n))),
    forall v : Vector.t nat k,
      (forall m, R v m <->
         exists c (v' : Vector.t nat (k + n)), (1, P) // (1, (0 :: v) ++ (Vector.const 0 n)) ~~> (c, m :: v')).
End MMA_problems.
