(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Bool Lia Eqdep_dec.

From Undecidability.Problems
  Require Import PCP.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import wf_finite.

From Undecidability.TRAKHTENBROT
  Require Import notations bpcp 
                 fo_sig fo_terms fo_logic fo_sat 
                 decidable

                 red_utils red_dec red_undec
                 .

Set Implicit Arguments.

Check FULL_TRAKHTENBROT.
Print Assumptions FULL_TRAKHTENBROT.

(** @DK Any idea for a NAME on the next one ;-) *)

Check ALHTENBROT.
Print Assumptions ALHTENBROT.

Check FSAT_FULL_MONADIC_DEC.
Print Assumptions FSAT_FULL_MONADIC_DEC.

Check FSAT_PROP_ONLY_DEC.
Print Assumptions FSAT_PROP_ONLY_DEC.

Print rec_enum_t.

Check FSAT_rec_enum_t.
Print Assumptions FSAT_rec_enum_t.

Print opt_enum_t.

Check FSAT_opt_enum_t.
Print Assumptions FSAT_opt_enum_t.



