(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Bool Lia Eqdep_dec.

From Undecidability Require Import ILL.Definitions.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import wf_finite.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops fo_terms fo_logic fo_sat discrete Sig3_Sig2 
                 bpcp fol_bpcp.

Set Implicit Arguments.

Section BPCP_fo_fin_dec_SAT.

  Definition BPCP_input := list (list bool * list bool).
  Definition FIN_SAT_input := fol_form Σbpcp.

  Definition BPCP_problem (lc : BPCP_input) := exists l, pcp_hand lc l l.
 
  Theorem BPCP_FIN_DEC_SAT : BPCP_problem ⪯ @fo_form_fin_dec_SAT Σbpcp.
  Proof.
    exists phi_R; intros lc; split.
    + intros (l & Hl); revert Hl.
      apply BPCP_sat.
    + intros; apply fin_sat_BPCP, fo_form_fin_dec_SAT_fin, H.
  Qed.

End BPCP_fo_fin_dec_SAT.

Check BPCP_FIN_DEC_SAT.
Print Assumptions BPCP_FIN_DEC_SAT.

(** The reduction is the identity here !! *)

Theorem fo_form_fin_dec_SAT_discr_equiv Σ A : 
    @fo_form_fin_dec_SAT Σ A <-> @fo_form_fin_discr_dec_SAT Σ A.
Proof.
  split.
  + apply fo_form_fin_dec_SAT_fin_discr_dec.
  + apply fo_form_fin_discr_dec_SAT_fin_dec.
Qed.

Check fo_form_fin_dec_SAT_discr_equiv.

Corollary FIN_DEC_SAT_FIN_DISCR_DEC_SAT Σ : @fo_form_fin_dec_SAT Σ ⪯ @fo_form_fin_discr_dec_SAT Σ.
Proof. exists (fun A => A); apply fo_form_fin_dec_SAT_discr_equiv. Qed.

Check FIN_DEC_SAT_FIN_DISCR_DEC_SAT.
Print Assumptions FIN_DEC_SAT_FIN_DISCR_DEC_SAT.

Print Σrel.

Theorem FIN_DISCR_DEC_3SAT_FIN_DEC_SAT : @fo_form_fin_discr_dec_SAT (Σrel 3)
                                                                        ⪯ @fo_form_fin_dec_SAT (Σrel 2).
Proof.
  exists Σ3_Σ2_enc; intros A; split.
  + apply SAT3_SAT2.
  + intros H; apply fo_form_fin_dec_SAT_fin_discr_dec, SAT2_SAT3, H.
Qed.

Check FIN_DISCR_DEC_3SAT_FIN_DEC_SAT.
Print Assumptions FIN_DISCR_DEC_3SAT_FIN_DEC_SAT.