(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Yannick Forster            [+]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [+] Affiliation Saarland Univ. *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

From Undecidability.Shared.Libs.DLW
  Require Import utils_tac.

Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.ILL 
  Require Import EILL ILL CLL ILL_undec EILL_CLL ILL_CLL.

(** Undecidability results *)

Local Hint Resolve rILL_rCLL_cf_PROVABILITY
                   EILL_CLL_cf_PROVABILITY
                 : core.

(* (!,&,-o) only fragment of CLL without cut *)

Theorem rCLL_cf_undec : undecidable rCLL_cf_PROVABILITY.
Proof. undec from rILL_cf_undec; auto. Qed.

(* full CLL without cut *)

Theorem CLL_cf_undec : undecidable CLL_cf_PROVABILITY.
Proof. undec from EILL_undec; auto. Qed.
