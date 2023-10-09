(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Certified Undecidability of Intuitionistic Linear Logic via Binary Stack Machines and Minsky Machines. Yannick Forster and Dominique Larchey-Wendling. CPP '19. http://uds-psl.github.io/ill-undecidability/ *)

Require Import List.

From Undecidability.Shared.Libs.DLW
  Require Import Vec.pos Vec.vec Code.sss.

Set Implicit Arguments.

(** * Halting problem for Minsky machines  *)

(* * Minsky Machines (MM)

    A Minsky machine has n registers and there are just two instructions
 
    1/ INC x   : increment register x by 1
    2/ DEC x k : decrement register x by 1 if x > 0
                 or jump to k if x = 0

  *)

Inductive mm_instr (X : Set) : Set :=
  | mm_inc : X -> mm_instr X
  | mm_dec : X -> nat -> mm_instr X
  .

Arguments mm_inc {_}.
Arguments mm_dec {_}.

Notation INC := mm_inc.
Notation DEC := mm_dec.

Notation INCₐ := mm_inc.
Notation DECₐ := mm_dec.

(* ** Semantics for MM, restricted to X = pos n for some n *)

Section Minsky_Machine.

  Variable (n : nat).

  Definition mm_state := (nat*vec nat n)%type.

  Local Notation "e #> x" := (vec_pos e x).
  Local Notation "e [ x := v ]" := (vec_change e x v) (no associativity, at level 50).

  Local Reserved Notation "P // e ▷ v" (at level 50, no associativity).

  (* Minsky machine small step semantics *)

  Inductive eval : nat * list (mm_instr (pos n)) -> mm_state -> mm_state -> Prop := 
  | eval_mm_out  i P c v :
      c < i \/ i + length P <= c ->
  (* ---------------------------- *)
      (i,P) // (c, v) ▷ (c, v)
  | eval_mm_inc  i P c v j c' v' :
      c >= i -> nth_error P (c - i) = Some (INC j) ->
      (i, P) // (c + 1, v[j := (v #> j) + 1]) ▷ (c', v') ->    
  (* -------------------------------------------------- *)
     (i,P) // (c, v) ▷ (c', v')
  | eval_mm_dec_S i P c v j c1 c' v' l :
     c >= i -> nth_error P (c - i) = Some (DEC j c1) ->
     v #> j = S l -> (i, P) // (c +1, v [j := l]) ▷ (c',v') ->
 (* -------------------------------------------------- *)
     (i,P) // (c, v) ▷ (c', v')

  | eval_mm_dec_empty i P c v j c1 c' v' :
      c >= i -> nth_error P (c - i) = Some (DEC j c1) ->
      v #> j = 0 -> (i, P) // (c1, v) ▷ (c',v') ->
  (* -------------------------------------------------- *)
      (i,P) // (c, v) ▷ (c', v')
     where "P // e ▷ v" := (eval P e v).

End Minsky_Machine.

Definition MM_PROBLEM := { n : nat & { P : list (mm_instr (pos n)) & vec nat n } }.

Definition Halt_MM (P : MM_PROBLEM) :=
  match P with existT _ n (existT _ P v) => exists c v', eval (1, P) (1, v) (c, v') end.

Import ListNotations Vector.VectorNotations.

Definition MM_computable {k} (R : Vector.t nat k -> nat -> Prop) := 
  exists n : nat, exists P : list (mm_instr (Fin.t (1 + k + n))),
    forall v : Vector.t nat k,
      (forall m, R v m <->
         exists c v', @MM.eval (1 + k + n) (1, P) (1, (0 :: v) ++ Vector.const 0 n) (c, m :: v')).
