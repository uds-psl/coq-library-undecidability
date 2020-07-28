(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** Hilbert's tenth problem is undecidable *)

From Undecidability.ILL 
  Require Import Definitions UNDEC.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.ILL.Mm
  Require Import mm_defs.

From Undecidability.H10 
  Require Import FRACTRAN_DIO MM_FRACTRAN Fractran.fractran_defs.

From Undecidability.H10.Dio 
  Require Import dio_logic dio_elem dio_single.

Set Implicit Arguments.

(** Hilbert's Tenth problem: given a diophantine equation with n
    variable and no parameters, does it have a solution *)

Definition H10_PROBLEM := { n : nat & dio_polynomial (pos n) (pos 0) 
                                    * dio_polynomial (pos n) (pos 0) }%type.

Definition H10 : H10_PROBLEM -> Prop.
Proof.
  intros (n & p & q).
  apply (dio_single_pred (p,q)), (fun _ => 0).
Defined.

(* Print dio_single_pred. *)

Theorem DIO_SINGLE_SAT_H10 : DIO_SINGLE_SAT ⪯ H10.
Proof.
  apply reduction_dependent; exists.
  intros (E,v).
  destruct (dio_poly_eq_pos E) as (n & p & q & H).
  exists (existT _ n (dp_inst_par _ v p, dp_inst_par _ v q)).
  unfold DIO_SINGLE_SAT, H10.
  rewrite H.
  unfold dio_single_pred.
  split; intros (phi & H1); exists phi; revert H1; cbn;
    rewrite !dp_inst_par_eval; auto.
Qed.
