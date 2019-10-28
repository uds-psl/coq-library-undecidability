(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Eqdep_dec Omega.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac.

From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.

From Undecidability.MuRec Require Import recalg ra_bounded.

From Undecidability.Problems Require Import H10C.

From Undecidability.ILL Require Import Definitions.

Set Implicit Arguments.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

(** There exists a universal µ-recusive algorithm of size 8708

      ra_univ : recalg 1

    such that ra_univ stops on <lc> iff lc is H10C-satisfiable
    <lc> is a Coq-computable encoding of lc
    lc is an instance of the H10C problem, ie a list of h10c constraints *)

Check ra_univ.
Eval compute in ra_size ra_univ.

Definition RA_UNIV_PROBLEM := nat.

Definition RA_UNIV_HALT (n : RA_UNIV_PROBLEM) : Prop := ex (⟦ra_univ⟧ (n##vec_nil)).

Definition H10C_RA_UNIV : H10C_PROBLEM -> RA_UNIV_PROBLEM.
Proof.
  intros lc.
  destruct (nat_h10lc_surj lc) as (k & Hk).
  exact k.
Defined.

Theorem H10C_SAT_RA_UNIV_HALT : H10C_SAT ⪯  RA_UNIV_HALT.
Proof.
  exists H10C_RA_UNIV; intros lc.
  unfold H10C_RA_UNIV.
  destruct (nat_h10lc_surj lc) as (k & Hk).
  symmetry; apply ra_univ_prop; auto.
Qed.

 
