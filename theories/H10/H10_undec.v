(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* ** Hilbert's tenth problem is undecidable *)

From Undecidability.Shared.Libs.DLW
  Require Import utils_tac.

From Undecidability.Synthetic Require Import Undecidability.
Require Import Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.TM.TM.

Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Reductions.HaltTM_1_to_PCPb.

From Undecidability.MinskyMachines
  Require Import MM PCPb_to_MM.

From Undecidability.FRACTRAN
  Require Import FRACTRAN FRACTRAN_undec MM_FRACTRAN.

From Undecidability.H10 
  Require Import H10 FRACTRAN_DIO.

From Undecidability.H10.Dio 
  Require Import dio_logic dio_elem dio_single.

Import ReductionChainNotations UndecidabilityNotations.

Require Import Undecidability.TM.TM_undec.

Set Implicit Arguments.

Theorem DIO_SINGLE_SAT_H10 : DIO_SINGLE_SAT ⪯ H10.
Proof.
  apply reduces_dependent; exists.
  intros (E,v).
  destruct (dio_poly_eq_pos E) as (n & p & q & H).
  exists (existT _ n (dp_inst_par _ v p, dp_inst_par _ v q)).
  unfold DIO_SINGLE_SAT, H10.
  rewrite H.
  unfold dio_single_pred.
  split; intros (phi & H1); exists phi; revert H1; cbn;
    rewrite !dp_inst_par_eval; auto.
Qed.

(* 
  reduction chain as described in
    Dominique Larchey-Wendling, Yannick Forster:
    Hilbert's Tenth Problem in Coq. FSCD 2019: 27:1-27:20 
*)

Theorem Hilberts_Tenth : HaltTM 1 ⪯ PCPb
                      /\ PCPb ⪯ Halt_MM
                      /\ Halt_MM ⪯ Halt_FRACTRAN
                      /\ Halt_FRACTRAN ⪯ DIO_LOGIC_SAT
                      /\ DIO_LOGIC_SAT ⪯ DIO_ELEM_SAT
                      /\ DIO_ELEM_SAT ⪯ DIO_SINGLE_SAT
                      /\ DIO_SINGLE_SAT ⪯ H10.
Proof.
  msplit 6.
  + apply HaltTM_1_to_PCPb.
  + apply PCPb_MM_HALTING.
  + apply MM_FRACTRAN_HALTING.
  + apply FRACTRAN_HALTING_DIO_LOGIC_SAT.
  + apply DIO_LOGIC_ELEM_SAT.
  + apply DIO_ELEM_SINGLE_SAT.
  + apply DIO_SINGLE_SAT_H10.
Qed. 

Check Hilberts_Tenth.

Theorem H10_undec : undecidable H10.
Proof.
  apply (undecidability_from_reducibility HaltTM_1_undec).
  reduce with chain Hilberts_Tenth.
Qed.

Check H10_undec.
