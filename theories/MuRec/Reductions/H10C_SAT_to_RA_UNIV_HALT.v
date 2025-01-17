(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List.

From Undecidability.MuRec.Util 
  Require Import recalg ra_univ ra_univ_andrej.

Require Import Undecidability.MuRec.Util.RA_UNIV_HALT.

Require Import Undecidability.DiophantineConstraints.H10C.

Require Import Undecidability.Synthetic.Definitions.

Set Implicit Arguments.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

(* We build a universal µ-recusive algorithm of size 8708
    (a shorter one is certainly possible)

      ra_univ : recalg 1

    such that 

      ra_univ stops on <lc> iff lc is H10C-satisfiable

    and where
    
     * <lc> is a Coq-computable encoding of lc, the encoding
       being performed by Gödel Beta function
     * lc is an instance of the H10C problem, ie a list of 
       h10c constraints *)

Definition H10C_RA_UNIV : list h10c -> RA_UNIV_PROBLEM.
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
  symmetry; apply ra_univ_spec; auto.
Qed.

Check H10C_SAT_RA_UNIV_HALT.


(* We build a similar one based on Andrej Dudenhefner
    type of H10 constraints, ie 1+x+y*y = z *)

Definition H10UC_RA_UNIV_AD : list h10uc -> RA_UNIV_PROBLEM.
Proof.
  intros lc.
  destruct (nat_h10luc_surj lc) as (k & Hk).
  exact k.
Defined.

Theorem H10UC_SAT_RA_UNIV_AD_HALT : H10UC_SAT ⪯  RA_UNIV_AD_HALT.
Proof.
  exists H10UC_RA_UNIV_AD; intros lc.
  unfold H10UC_RA_UNIV_AD.
  destruct (nat_h10luc_surj lc) as (k & Hk).
  symmetry; apply ra_univ_ad_spec; auto.
Qed.

Check H10UC_SAT_RA_UNIV_AD_HALT.


