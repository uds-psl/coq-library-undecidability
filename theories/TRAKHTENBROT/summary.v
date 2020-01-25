(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Bool Lia Relations.

From Undecidability.Problems
  Require Import Reduction PCP.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite php.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import wf_finite.

From Undecidability.TRAKHTENBROT
  Require Import notations bpcp 
                 fo_sig fol_ops fo_terms fo_logic fo_sat fo_sat_dec
                 decidable enumerable discrete reln_hfs membership

                 BPCP_SigBPCP Sig_Sig_fin Sig_rem_syms Sig_uniform 
                 Sig_one_rel Sig_rem_cst Sig2_SigSSn1 Sig1_1
                 Sig_rem_constants Sig_rem_props

                 red_utils red_enum red_dec red_undec
                 .

Set Implicit Arguments.

(** * Summary of the definitions and results of the IJCAR submission, with output *)

(* Definition 1 *)

About decidable. Print decidable.
Check decidable_bool_eq.
About opt_enum_t. Print opt_enum_t.
About type_enum_t. Print type_enum_t.
About discrete. Print discrete.

(* Definition 2 *)

About reduces. Print reduces.

(* Fact 3 *)

About reduction_decidable.
About reduction_rec_enum_t.
About reduction_opt_enum_t.

(* Definition 4 *)

About pcp_hand. Print pcp_hand.
About BPCP_problem. Print BPCP_problem.

(* Fact 5, for the reduction for TM halting, you need much more code from the
   undec. library and that one is not trivial at all *)

About bpcp_hand_dec.
Print Assumptions bpcp_hand_dec.

About BPCP_BPCP_problem_eq.
About BPCP_BPCP_problem.

(* Definition 6 *)

About finite_t. Print finite_t.

(* Theorem 7 *)

About PHP_rel.
Print Assumptions PHP_rel.

(* Fact 8 *)

About wf_strict_order_finite.
Print Assumptions wf_strict_order_finite.

(* Theorem 9 *)

About decidable_EQUIV_fin_quotient.
Print Assumptions decidable_EQUIV_fin_quotient.

(* Corollary 10 *)

Print bij_t.
About finite_t_discrete_bij_t_pos.
Print Assumptions finite_t_discrete_bij_t_pos.

(* Definition FOL *)

About fo_term. Print fo_term.
Print fo_signature.
Print fol_bop.
Print fol_qop.
About fol_form. Print fol_form.

(* Definition 11 *)

About fo_model. Print fo_model.
About fo_term_sem. Print fo_term_sem.
About fol_sem. Print fol_sem.

(* Fact 12 *)

About fol_sem_dec.
Print Assumptions fol_sem_dec.

(* Definition 13 *)

About fo_form_fin_dec_SAT_in.
Print fo_form_fin_dec_SAT_in.
Print fo_form_fin_dec_SAT.

About fo_form_fin_dec_eq_SAT_in.
Print fo_form_fin_dec_eq_SAT_in.
Print fo_form_fin_dec_eq_SAT.

(* Theorem 14 *)

About BPCP_FIN_DEC_EQ_SAT.
Print Assumptions BPCP_FIN_DEC_EQ_SAT.

(* Lemma 15 *)

About Σbpcp_encode_sound.

(* Lemma 16 *)

About Σbpcp_encode_complete.

(* Definition 17 *)

About fo_form_fin_discr_dec_SAT_in.
Print fo_form_fin_discr_dec_SAT_in.
Print fo_form_fin_discr_dec_SAT.

(* Definition 18 *)

About fo_bisimilar.
Print fo_bisimilar.

(* Theorem 19 *)

Print fo_congruence_upto.
About fo_bisimilar_dec_congr.
Print Assumptions fo_bisimilar_dec_congr.

(* Theorem 20 *)

About fo_form_fin_dec_SAT_discr_equiv.
Check FIN_DEC_SAT_FIN_DISCR_DEC_SAT.

(* Theorem 21 *)

About FIN_DEC_EQ_SAT_FIN_DEC_SAT.
Print Assumptions FIN_DEC_EQ_SAT_FIN_DEC_SAT.

(* Lemma 22 *)

About Sig_discrete_to_pos.
Print Assumptions Sig_discrete_to_pos.

(* Lemma 23 *)

Print Σnosyms.
About FSAT_Σnosyms.

(* Lemma 24 *)

Print Σrel.
About FSAT_REL_BOUNDED_ONE_REL.
Print Assumptions FSAT_REL_BOUNDED_ONE_REL.

(* Fact 25 *)

Print Σunif.
About FSAT_UNIFORM.

Print Σone_rel.
About FSAT_ONE_REL.

Print Σrem_cst.
Check FSAT_NOCST.

(* Lemma 26 *)

About FIN_DISCR_DEC_nSAT_FIN_DEC_2SAT.
Print Assumptions FIN_DISCR_DEC_nSAT_FIN_DEC_2SAT.

(* Theorem 27 *)

About reln_hfs.
Print Assumptions reln_hfs.

(* Theorem 28 *)

About FSAT_REL_nto2.
Print Assumptions FSAT_REL_nto2.

(* Lemma 29 *)

Print Σn1.
About FSAT_REL2_to_FUNnREL1.
Print Assumptions FSAT_REL2_to_FUNnREL1.

(* Fact 30 *)

Print Σrel.
About FSAT_REL_2ton.
About FSAT_RELn_ANY.
Print Σn1.
About FSAT_FUNnREL1_ANY.

(* Lemma 31 *)

About FSAT_in_dec.
Print Assumptions FSAT_in_dec.

(* Lemma 32 *)

About fo_form_fin_discr_dec_SAT_pos.
Print Assumptions fo_form_fin_discr_dec_SAT_pos.

(* Lemma 33 *)

Print Σ11.
About FSAT_MONADIC_DEC.
Print Assumptions FSAT_MONADIC_DEC.

(* Lemma 34 *)

Print Σ11.
About FSAT_MONADIC_11_FSAT_MONADIC_1.
Print Assumptions FSAT_MONADIC_11_FSAT_MONADIC_1.

(* Fact 35 *)

Print Σ11.
About FSAT_FULL_MONADIC_FSAT_11.
Print Assumptions FSAT_FULL_MONADIC_FSAT_11.
About Σrem_constants_correct.
About Σrem_props_correct.

(* Theorem 36 *)

About FSAT_rec_enum_t.
Print Assumptions FSAT_rec_enum_t.

About FSAT_opt_enum_t.
Print Assumptions FSAT_opt_enum_t.

(* Theorem 37 *)

About FULL_TRAKHTENBROT.
Print Assumptions FULL_TRAKHTENBROT.

(* Theorem 38 *)

About FULL_MONADIC.
Print Assumptions FULL_MONADIC.



