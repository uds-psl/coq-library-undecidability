(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import vec.

From Undecidability.MuRec 
  Require Import recalg ra_univ ra_univ_andrej.

Set Implicit Arguments.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

(** We build a universal µ-recusive algorithm of size 8708

      ra_univ : recalg 1

    which is just a particular µ-recursive algorithm. It is
    universal w.r.t. elementary Diophantine constraints 
    as established in Reductions/H10C_RA_UNIV.v

    Basically, its termination predicate RA_UNIV_HALT 
    can simulate the solvability of any list of elementary 
    Diophantine constraints, making it undecidable *)

(* Check ra_size ra_univ. *)
(* Eval compute in ra_size ra_univ. *)
(* Check ra_size ra_univ_ad. *)
(* Eval compute in ra_size ra_univ_ad. *)

Definition RA_UNIV_PROBLEM := nat.
Definition RA_UNIV_HALT (n : RA_UNIV_PROBLEM) : Prop := ex (⟦ra_univ⟧ (n##vec_nil)).
Definition RA_UNIV_AD_HALT (n : RA_UNIV_PROBLEM) : Prop := ex (⟦ra_univ_ad⟧ (n##vec_nil)).
