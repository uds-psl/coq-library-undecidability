(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** Hilbert's tenth problem is undecidable *)

From Undecidability.Synthetic Require Import Undecidability.

Require Import Undecidability.TM.Halting.
From Undecidability.PCP Require Import PCP HALT_TM1_to_PCPb.

From Undecidability.Shared.Libs.DLW
  Require Import utils_tac pos vec.

From Undecidability.MinskyMachines
  Require Import MM PCPb_to_MM.

From Undecidability.FRACTRAN
  Require Import FRACTRAN FRACTRAN_undec MM_FRACTRAN.

From Undecidability.H10 
  Require Import FRACTRAN_DIO.

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

Check FRACTRAN_undec.

Theorem Hilberts_Tenth : HaltTM 1 ⪯ PCPb
                      /\ PCPb ⪯ MM_HALTING
                      /\ MM_HALTING ⪯ FRACTRAN_HALTING
                      /\ FRACTRAN_HALTING ⪯ DIO_LOGIC_SAT
                      /\ DIO_LOGIC_SAT ⪯ DIO_ELEM_SAT
                      /\ DIO_ELEM_SAT ⪯ DIO_SINGLE_SAT
                      /\ DIO_SINGLE_SAT ⪯ H10.
Proof.
  msplit 6.
  + apply HALT_TM1_to_PCPb.
  + apply PCPb_MM_HALTING.
  + apply MM_FRACTRAN_HALTING.
  + apply FRACTRAN_HALTING_DIO_LOGIC_SAT.
  + apply DIO_LOGIC_ELEM_SAT.
  + apply DIO_ELEM_SINGLE_SAT.
  + apply DIO_SINGLE_SAT_H10.
Qed.

Theorem H10_undec : HaltTM 1 ⪯ H10.
Proof.
  repeat (eapply reduces_transitive; [ apply Hilberts_Tenth | ]).
  apply reduces_reflexive.
Qed.

Check H10_undec.
