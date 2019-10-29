(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** Elementary Diophantine constraints w/o parameters
    and with only the constant 1 i.e. constraints 
    are of three shapes:

      x = 1 | x+y = z | x*y = z  with x,y,z in nat 

  *)

Set Implicit Arguments.

Inductive h10c : Set :=
  | h10c_one : nat -> h10c
  | h10c_plus : nat -> nat -> nat -> h10c
  | h10c_mult : nat -> nat -> nat -> h10c.

Definition h10c_sem c φ :=
  match c with
    | h10c_one x      => φ x = 1
    | h10c_plus x y z => φ x + φ y = φ z
    | h10c_mult x y z => φ x * φ y = φ z
  end.

