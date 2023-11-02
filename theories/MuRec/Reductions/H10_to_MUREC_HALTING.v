(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import List.

Require Import Undecidability.Synthetic.Definitions.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_nat.

From Undecidability.Shared.Libs.DLW.Vec
  Require Import pos vec.

From Undecidability.H10 
  Require Import Dio.dio_single H10.

From Undecidability.MuRec.Util 
  Require Import recalg ra_dio_poly ra_sem_eq.

Section H10_MUREC_HALTING.

  Let f : H10_PROBLEM -> MUREC_PROBLEM.
  Proof.
    intros (n & p & q).
    exact (ra_dio_poly_find p q).
  Defined.

  Theorem H10_MUREC_HALTING : H10 ⪯ Halt_murec.
  Proof. 
    unshelve eexists.
    { intros (n & p & q). exists 0. 2: exact vec_nil. exact (ra_dio_poly_find p q). }
    intros (n & p & q); simpl; unfold Halt_murec.
    setoid_rewrite <- ra_bs_correct.
    rewrite ra_dio_poly_find_spec; unfold dio_single_pred.
    split.
    + intros (phi & Hphi); exists (vec_set_pos phi).
      simpl in Hphi; eq goal Hphi; f_equal; apply dp_eval_ext; auto;
        try (intros; rewrite vec_pos_set; auto; fail);
        intros j; analyse pos j.
    + intros (v & Hw); exists (vec_pos v).
      eq goal Hw; f_equal; apply dp_eval_ext; auto;
        intros j; analyse pos j.
  Qed.

End H10_MUREC_HALTING.

Check H10_MUREC_HALTING.
