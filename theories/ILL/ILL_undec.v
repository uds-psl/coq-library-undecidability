(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Yannick Forster            [+]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [+] Affiliation Saarland Univ. *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Undecidability.Shared.Libs.DLW
  Require Import utils_tac.

Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.Synthetic.ReducibilityFacts.

From Undecidability.PCP              Require Import PCP PCP_undec.
From Undecidability.StackMachines    Require Import BSM.
From Undecidability.MinskyMachines   Require Import MM MM_sss.

From Undecidability.ILL 
  Require Import EILL ILL iBPCP_MM MM_EILL EILL_ILL.

Require Import Undecidability.PCP.Reductions.HaltTM_1_to_PCPb.

Import ReductionChainNotations UndecidabilityNotations.

(* The reduction chain from the CPP 2019, Y. Forster & D. Larchey-Wendling *)

Theorem PCP_chain_ILL : 
  PCP ⪯ PCPb /\
  PCPb ⪯ iPCPb /\
  iPCPb ⪯ Halt_BSM /\
  Halt_BSM ⪯ MM_HALTS_ON_ZERO /\
  MM_HALTS_ON_ZERO ⪯ EILL_PROVABILITY /\
  EILL_PROVABILITY ⪯ ILL_PROVABILITY.
Proof.
  msplit 5.
  + apply PCP_to_PCPb.reduction.
  + apply PCPb_iff_iPCPb.reductionLR.
  + apply iBPCP_chain_MM.
  + apply iBPCP_chain_MM.
  + apply MM_HALTS_ON_ZERO_EILL_PROVABILITY.
  + apply EILL_ILL_PROVABILITY.
Qed.

Check PCP_chain_ILL.

(* Undecidability results *)

Local Hint Resolve EILL_rILL_cf_PROVABILITY 
                   EILL_rILL_PROVABILITY
                   EILL_ILL_cf_PROVABILITY
                 : core.

(* EILL provability using G_eill *)

Theorem EILL_undec : undecidable EILL_PROVABILITY.
Proof. undec from PCP_undec using chain PCP_chain_ILL. Qed.

(* whole ILL with cut *)

Theorem ILL_undec : undecidable ILL_PROVABILITY.
Proof. undec from PCP_undec using chain PCP_chain_ILL. Qed.

(* whole ILL without cut *)

Theorem ILL_cf_undec : undecidable ILL_cf_PROVABILITY.
Proof. undec from EILL_undec; auto. Qed.

(* (!,&,-o) fragment of ILL without cut *)

Theorem rILL_cf_undec : undecidable rILL_cf_PROVABILITY.
Proof. undec from EILL_undec; auto. Qed.

(* (!,&,-o) fragment of ILL with cut *)

Theorem rILL_undec : undecidable rILL_PROVABILITY.
Proof. undec from EILL_undec; auto. Qed.
