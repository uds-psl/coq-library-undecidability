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
  Require Import Reduction.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import wf_finite.

From Undecidability.TRAKHTENBROT
  Require Import notations bpcp 
                 fo_sig fo_terms fo_logic fo_sat 
                 decidable enumerable

                 red_utils red_enum red_dec red_undec
                 .

Set Implicit Arguments.

Print type_enum_t.
Print opt_enum_t.
Print rec_enum_t.

Check FSAT_rec_enum_t.
Print Assumptions FSAT_rec_enum_t.

Check FSAT_opt_enum_t.
Print Assumptions FSAT_opt_enum_t.

Check FULL_TRAKHTENBROT.
Print Assumptions FULL_TRAKHTENBROT.

Check FULL_MONADIC.
Print Assumptions FULL_MONADIC.



