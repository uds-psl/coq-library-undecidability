(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.

From Undecidability.ILL Require Import Definitions.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_nat.

From Undecidability.Shared.Libs.DLW.Vec
  Require Import pos vec.

From Undecidability.H10.Dio 
  Require Import dio_single.

From Undecidability.MuRec 
  Require Import recalg ra_dio_poly.

Definition DIO_SINGLE_PROBLEM := { n : nat & dio_polynomial (pos n) (pos 0) 
                                           * dio_polynomial (pos n) (pos 0) }%type.

Definition DIO_SINGLE_SAT : DIO_SINGLE_PROBLEM -> Prop.
Proof.
  intros (n & p & q).
  apply (dio_single_pred (p,q)), pos_O_any.
Defined.

Section DIO_SINGLE_SAT_MUREC_HALTING.

  Let f : DIO_SINGLE_PROBLEM -> MUREC_PROBLEM.
  Proof.
    intros (n & p & q).
    exact (ra_dio_poly_find p q).
  Defined.

  Theorem DIO_SINGLE_SAT_MUREC_HALTING : DIO_SINGLE_SAT ⪯ MUREC_HALTING.
  Proof.
    exists f.
    intros (n & p & q); simpl; unfold MUREC_HALTING.
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

End DIO_SINGLE_SAT_MUREC_HALTING.

Check DIO_SINGLE_SAT_MUREC_HALTING.
Print Assumptions DIO_SINGLE_SAT_MUREC_HALTING.
