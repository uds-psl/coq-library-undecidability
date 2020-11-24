(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Lia.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_nat gcd crt sums.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.MuRec 
  Require Import recomp.

Set Implicit Arguments.

(* beta can enumerate ANY vector of ANY length by wisely choosing
    the parameter a *)

Definition beta a n := godel_beta (decomp_l a) (decomp_r a) n.

Lemma beta_inv n (v : vec _ n) : { a | forall p, beta a (pos2nat p) = vec_pos v p }.
Proof.
  destruct (godel_beta_inv v) as (a & b & H).
  exists (recomp a b); intro p; unfold beta.
  rewrite decomp_l_recomp, decomp_r_recomp; auto.
Qed.

Lemma beta_fun_inv n f : { a | forall p, p < n -> f p = beta a p }.
Proof.
  destruct beta_inv 
    with (v := vec_set_pos (fun p : pos n => f (pos2nat p)))
    as (a & Ha).
  exists a; intros p Hp.
  specialize (Ha (nat2pos Hp)).
  rewrite vec_pos_set, pos2nat_nat2pos in Ha.
  auto.
Qed.
