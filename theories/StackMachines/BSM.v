(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* Certified Undecidability of Intuitionistic Linear Logic via Binary Stack Machines and Minsky Machines. Yannick Forster and Dominique Larchey-Wendling. CPP '19. http://uds-psl.github.io/ill-undecidability/ *)

From Stdlib Require Import List Bool.

From Undecidability.Shared.Libs.DLW 
  Require Import list_bool pos vec.

(** * Halting problem for binary stack machines BSM_HALTING  *)

(* * Binary Stack Machines
   Binary stack machines have n stacks and there are just two instructions
  
   1/ POP s p q : pops the value on stack s and
                  if Empty then jumps to q 
                  if Zero then jumps to p
                  if One then jumps to next instruction,
   2/ PUSH s b : pushes the value b on stack s and jumps to next instructions 

 *)

Inductive bsm_instr n : Set :=
  | bsm_pop  : pos n -> nat -> nat -> bsm_instr n
  | bsm_push : pos n -> bool -> bsm_instr n
  .

(* ** Semantics for BSM *)

Section Binary_Stack_Machine.

  Variable (n : nat).

  Notation POP  := (bsm_pop n).
  Notation PUSH := (bsm_push n).

  Notation "e '#>' x" := (vec_pos e x) (at level 58, format "e #> x").
  Notation "e [ x := v ]" := (vec_change e x v) (no associativity, at level 1).

  Reserved Notation "P // e ▷ v" (at level 50, no associativity).

  Inductive eval : nat * list (bsm_instr n) -> (nat*vec (list bool) n) -> (nat*vec (list bool) n) -> Prop :=
  | eval_bsm_out i P c v :
      c < i \/ i + length P <= c ->
  (* ---------------------------- *)
      (i,P) // (c, v) ▷ (c, v)
  | eval_bsm_push i P c v j b c' v' :
      c >= i -> nth_error P (c - i) = Some (PUSH j b) ->
      (i, P) // (c + 1, v[j := b :: v #> j]) ▷ (c', v') ->
  (* -------------------------------------------------- *)
     (i,P) // (c, v) ▷ (c', v')
  | eval_bsm_pop_true i P c v j c1 c2 c' v' l :
      c >= i -> nth_error P (c - i) = Some (POP j c1 c2) ->
      v #> j = true :: l -> (i, P) // (c +1, v [j := l]) ▷ (c',v') ->
  (* -------------------------------------------------- *)
      (i,P) // (c, v) ▷ (c', v')

  | eval_bsm_pop_false i P c v j c1 c2 c' v' l :
      c >= i -> nth_error P (c - i) = Some (POP j c1 c2) ->
      v #> j = false :: l -> (i, P) // (c1, v [j := l]) ▷ (c',v') ->
  (* -------------------------------------------------- *)
      (i,P) // (c, v) ▷ (c', v')
  | eval_bsm_pop_empty i P c v j c1 c2 c' v' :
      c >= i -> nth_error P (c - i) = Some (POP j c1 c2) ->
      v #> j = nil -> (i, P) // (c2, v) ▷ (c',v') ->
  (* -------------------------------------------------- *)
      (i,P) // (c, v) ▷ (c', v')

  where "P // e ▷ v" := (eval P e v).

End Binary_Stack_Machine.

(* The Halting problem for BSM *)

Definition BSMn_PROBLEM n := { i : nat & { P : list (bsm_instr n) & vec (list bool) n } }.
Definition BSM_PROBLEM := { n : nat & BSMn_PROBLEM n }.

Definition Halt_BSM :
  { n : nat & { i : nat & { P : list (bsm_instr n) & vec (list bool) n } } } -> Prop:=
  fun '(existT _ n (existT _ i (existT _ P v))) => exists c' v', eval n (i,P) (i,v) (c', v').

Import ListNotations Vector.VectorNotations.

Definition BSM_computable {k} (R : Vector.t nat k -> nat -> Prop) := 
  exists n : nat, exists i : nat, exists P : list (bsm_instr (1 + k + n)),
    forall v : Vector.t nat k,
      (forall m, R v m <->
         exists c v', BSM.eval (1 + k + n) (i, P) (i, (@List.nil bool :: Vector.map (fun n => List.repeat true n) v) ++ Vector.const (@List.nil bool) n) (c, List.repeat true m :: v'))
    /\ (forall c v', BSM.eval (1 + k + n) (i, P) (i, (@List.nil bool :: Vector.map (fun n => List.repeat true n) v) ++ Vector.const (@List.nil bool) n) (c, v') -> exists m v'', v' = List.repeat true m :: v'').    
