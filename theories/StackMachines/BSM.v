(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* Certified Undecidability of Intuitionistic Linear Logic via Binary Stack Machines and Minsky Machines. Yannick Forster and Dominique Larchey-Wendling. CPP '19. http://uds-psl.github.io/ill-undecidability/ *)

Require Import List Bool.

From Undecidability.Shared.Libs.DLW 
  Require Import list_bool pos vec sss.

Set Implicit Arguments.

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

Notation POP  := bsm_pop.
Notation PUSH := bsm_push.

(* ** Semantics for BSM *)

Section Binary_Stack_Machine.

  Variable (n : nat).

  Definition bsm_state := (nat*vec (list bool) n)%type.

  Local Notation "e #> x" := (vec_pos e x).
  Local Notation "e [ v / x ]" := (vec_change e x v).

  Inductive bsm_sss : bsm_instr n -> bsm_state -> bsm_state -> Prop :=
    | in_bsm_sss_pop_E : forall i x p q v,    v#>x = nil      -> POP x p q // (i,v) -1> (  q,v)
    | in_bsm_sss_pop_0 : forall i x p q v ll, v#>x = Zero::ll -> POP x p q // (i,v) -1> (  p,v[ll/x])
    | in_bsm_sss_pop_1 : forall i x p q v ll, v#>x = One ::ll -> POP x p q // (i,v) -1> (1+i,v[ll/x])
    | in_bsm_sss_push  : forall i x b v,                         PUSH x b  // (i,v) -1> (1+i,v[(b::v#>x)/x])
  where "i // s -1> t" := (bsm_sss i s t).

End Binary_Stack_Machine.

(* The Halting problem for BSM *)
  
Definition BSM_PROBLEM := { n : nat & { i : nat & { P : list (bsm_instr n) & vec (list bool) n } } }.

Local Notation "P // s ↓" := (sss_terminates (@bsm_sss _) P s).

Definition BSM_HALTING (P : BSM_PROBLEM) := 
  match P with existT _ n (existT _ i (existT _ P v)) => (i,P) // (i,v) ↓ end.


     
