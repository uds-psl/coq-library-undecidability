(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Bool Lia Relations.

From Undecidability.Synthetic
  Require Import Definitions 
                 ReducibilityFacts
                 InformativeDefinitions 
                 InformativeReducibilityFacts
                 Undecidability.

From Undecidability.PCP
  Require Import PCP PCP_undec.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite php.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import wf_finite.

From Undecidability.TRAKHTENBROT
  Require Import notations bpcp 
                 fo_sig fol_ops fo_terms fo_logic fo_sat fo_sat_dec
                 decidable enumerable discrete discernable 
                 reln_hfs membership

                 BPCP_SigBPCP Sig_Sig_fin Sig_rem_syms Sig_uniform 
                 Sig_one_rel Sig_rem_cst Sig2_SigSSn1 Sig1_1 Sig0
                 Sig_rem_constants Sig_rem_props
                 Sig_discernable

                 red_utils red_enum red_dec red_undec
                 .

Set Implicit Arguments.

Local Infix "∊" := In (at level 70, no associativity).
Local Infix "⊑" := incl (at level 70, no associativity). 

(** * Summary File *)

(* You can comment out "Print Assumptions" below to check for
   that no axioms where used. Printing assumptions takes a big 
   toll on the compilation time 

   Notice that you can also just check for axiom-freeness on the
   main results at the end of this file. This entails that intermediate
   result are also free of axioms, ie.

        FULL_MONADIC
        FULL_MONADIC_discernable
        FULL_TRAKHTENBROT
*)

(* Definition 1 *)

Locate "≋".
About decidable. Print decidable.
Check decidable_bool_eq.
About opt_enum_t. Print opt_enum_t.
About type_enum_t. Print type_enum_t.
About discrete. Print discrete.

(* Definition 2 *)

About "⪯". Print "⪯".
About "⪯ᵢ". Print "⪯ᵢ".

(* Fact 3 *)

About reduction_decidable.
About reduction_rec_enum_t.
About reduction_opt_enum_t.

(* Definition 4 *)

About BPCP_problem. Print BPCP_problem.

(* Fact 5, for the reduction for TM halting, you need much more code from the
   undec. library and that one is not trivial at all *)

About bpcp_hand_dec. (* Print Assumptions bpcp_hand_dec. *)

About derivable. Print derivable.
About BPCP. Print BPCP.

About BPCP_BPCP_problem_eq. (* Print Assumptions BPCP_BPCP_problem_eq. *)
About BPCP_BPCP_problem.    (* Print Assumptions BPCP_BPCP_problem. *)

(* Definition 6 *)

About finite_t. Print finite_t.

(* Theorem 7 *)

About PHP_rel. (* Print Assumptions PHP_rel. *)

(* Fact 8 *)

About wf_strict_order_finite. (* Print Assumptions wf_strict_order_finite. *)

(* Theorem 9 *)

About decidable_EQUIV_fin_quotient. (* Print Assumptions decidable_EQUIV_fin_quotient. *)

(* Corollary 10 *)

Print bij_t.   (* to understand the meaning of the following result *)
About finite_t_discrete_bij_t_pos. (* Print Assumptions finite_t_discrete_bij_t_pos. *)

(* Lemma 11 *)

About finite_t_weak_dec_rels. (* Print Assumptions finite_t_weak_dec_rels. *)

(* Definition FOL *)

About fo_term. Print fo_term.
Print fo_signature.
Print fol_bop.
Print fol_qop.
About fol_form. Print fol_form.

(* Definition 12 *)

About fo_model. Print fo_model.
About fo_term_sem. Print fo_term_sem.
About fol_sem. Print fol_sem.

(* Fact 13 *)

About fol_sem_dec. (* Print Assumptions fol_sem_dec. *)

(* Definition 14 *)

About fo_form_fin_dec_SAT_in.
Print fo_form_fin_dec_SAT_in.
Print fo_form_fin_dec_SAT.
About FSAT. Print FSAT.

About fo_form_fin_dec_eq_SAT_in.
Print fo_form_fin_dec_eq_SAT_in.
Print fo_form_fin_dec_eq_SAT.
About FSATEQ. Print FSATEQ.

(* Theorem 15 *)

About BPCP_FIN_DEC_EQ_SAT. (* Print Assumptions BPCP_FIN_DEC_EQ_SAT. *)

(* Lemma 16 *)

About Sig_bpcp_encode_sound. (* Print Assumptions Sig_bpcp_encode_sound. *)

(* Lemma 17 *)

About Sig_bpcp_encode_complete. (* Print Assumptions Sig_bpcp_encode_complete. *)

(* Definition 18 *)

About fo_bisimilar. Print fo_bisimilar.

(* Facts 19 *)

Print discrete.fom_op1.
Print discrete.fom_op2.
Print discrete.fom_op.
Check discrete.fom_op_mono.       (* Print Assumptions discrete.fom_op_mono. *)
Check discrete.fom_op_continuous. (* Print Assumptions discrete.fom_op_continuous. *)
Check discrete.fom_op_id.         (* Print Assumptions discrete.fom_op_id. *)
Check discrete.fom_op_sym.        (* Print Assumptions discrete.fom_op_sym. *)
Check discrete.fom_op_trans.      (* Print Assumptions discrete.fom_op_trans. *)
Check discrete.fom_op_dec.        (* Print Assumptions discrete.fom_op_dec. *)

(* Theorem 20 *)

About gfp.gfp. Print gfp.gfp.
About fom_eq. Print fom_eq.
About fom_eq_fol_characterization. (* Print Assumptions fom_eq_fol_characterization. *)

(* Theorem 21 *)

About gfp.gfp_finite_t. (* Print Assumptions gfp.gfp_finite_t. *)

(* Theorem 22 *)

Print fo_congruence_upto.  (* to understand the meaning of the following result *)
About fo_bisimilar_dec_congr. (* Print Assumptions fo_bisimilar_dec_congr. *)

(* Definition 23 *)

About fo_form_fin_discr_dec_SAT_in.
Print fo_form_fin_discr_dec_SAT_in.
Print fo_form_fin_discr_dec_SAT.
About FSAT'. Print FSAT'.

(* Theorem 24 *)

About fo_form_fin_dec_SAT_discr_equiv. (* Print Assumptions fo_form_fin_dec_SAT_discr_equiv. *)
Check FIN_DEC_SAT_FIN_DISCR_DEC_SAT.   (* Print Assumptions FIN_DEC_SAT_FIN_DISCR_DEC_SAT. *)

(* Theorem 25 *)

About FIN_DEC_EQ_SAT_FIN_DEC_SAT. (* Print Assumptions FIN_DEC_EQ_SAT_FIN_DEC_SAT. *)

(* Lemma 26 *)

About Sig_discrete_to_pos. (* Print Assumptions Sig_discrete_to_pos. *)

(* Lemma 27 *)

Print Σnosyms.
About FSAT_Σnosyms. (* Print Assumptions FSAT_Σnosyms. *)

(* Lemma 28 *)

Print Σrel.      (* to understand the meaning of the following result *)
About FSAT_REL_BOUNDED_ONE_REL. (* Print Assumptions FSAT_REL_BOUNDED_ONE_REL. *)

(* Fact 29 *)

Print Σunif.     (* to understand the meaning of the following result *)
About FSAT_UNIFORM. (* Print Assumptions FSAT_UNIFORM. *)

Print Σone_rel.  (* to understand the meaning of the following result *)
About FSAT_ONE_REL. (* Print Assumptions FSAT_ONE_REL. *)

Print Σrem_cst.  (* to understand the meaning of the following result *)
Check FSAT_NOCST. (* Print Assumptions FSAT_NOCST. *)

(* Theorem 30 *)

About FIN_DISCR_DEC_nSAT_FIN_DEC_2SAT. (* Print Assumptions FIN_DISCR_DEC_nSAT_FIN_DEC_2SAT. *)

(* Theorem 31 *)

About reln_hfs. (* Print Assumptions reln_hfs. *)

(* Theorem 32 *)

Print Σrel.    (* to understand the meaning of the following result *)
About DISCRETE_TO_BINARY. (* Print Assumptions DISCRETE_TO_BINARY. *)

(* Lemma 33 *)

Print Σn1.     (* to understand the meaning of the following result *)
About FSAT_REL2_to_FUNnREL1. (* Print Assumptions FSAT_REL2_to_FUNnREL1. *)

(* Facts 34 *)

Print Σrel.    (* to understand the meaning of the following results *)
About FSAT_REL_2ton.     (* Print Assumptions FSAT_REL_2ton. *)
About FSAT_RELn_ANY.     (* Print Assumptions FSAT_RELn_ANY. *)
Print Σn1.     (* to understand the meaning of the following result *)
About FSAT_FUNnREL1_ANY. (* Print Assumptions FSAT_FUNnREL1_ANY. *)

(* Definition 35 is only in the paper. In the code, it is inlined
   when needed *)

(* Lemma 36 *)

About FSAT_in_dec.  (* Print Assumptions FSAT_in_dec. *)

(* Lemma 37 *)

About fo_form_fin_discr_dec_SAT_pos. (* Print Assumptions fo_form_fin_discr_dec_SAT_pos. *)

(* Lemma 38 *)

Print Σ11.     (* to understand the meaning of the following result *)
(* F -> False below implies that F is an empty type, so in particular,
   this works for Empty_set *)
About FSAT_MONADIC_DEC. (* Print Assumptions FSAT_MONADIC_DEC. *)

(* Lemma 39 *)

Print Σ11.     (* to understand the meaning of the following result *)
About FSAT_MONADIC_11_FSAT_MONADIC_1. (* Print Assumptions FSAT_MONADIC_11_FSAT_MONADIC_1. *)

(* Fact 40 *)

Print Σ11.     (* to understand the meaning of the following result *)
About FSAT_FULL_MONADIC_FSAT_11. (* Print Assumptions FSAT_FULL_MONADIC_FSAT_11. *)

(* Fact 41 *)

About FSAT_PROP_FSAT_x0. (* Print Assumptions FSAT_PROP_FSAT_x0. *)
About FSAT_x0_FSAT_PROP. (* Print Assumptions FSAT_x0_FSAT_PROP. *)

(* Theorem 42 *)

About FULL_MONADIC.  (* Print Assumptions FULL_MONADIC. *)

(* Definition 43 *)

About discernable.   Print discernable.
About undiscernable. Print undiscernable.

(* Fact 44 *)

About FSAT_dec_implies_discernable_rels_dec. (* Print Assumptions FSAT_dec_implies_discernable_rels_dec. *)

(* Fact 45 *)

About FSAT_dec_implies_discernable_syms_dec. (* Print Assumptions FSAT_dec_implies_discernable_syms_dec. *)

(* Lemma 46 *)

About Sig_discernable_dec_to_discrete. (* Print Assumptions Sig_discernable_dec_to_discrete. *)

(* Theorem 47 *)

About FSAT_FULL_MONADIC_discernable. (* Print FSAT_FULL_MONADIC_discernable. *)

(* But see also the equivalence *)
About FULL_MONADIC_discernable_dec_FSAT_dec_equiv. (* Print Assumptions FULL_MONADIC_discernable_dec_FSAT_dec_equiv. *)

(* Theorem 48 *)

About FSAT_PROP_ONLY_discernable. (* Print Assumptions FSAT_PROP_ONLY_discernable. *)

(* But see also the equivalence *)
About MONADIC_PROP_discernable_dec_FSAT_dec_equiv. (* Print Assumptions MONADIC_PROP_discernable_dec_FSAT_dec_equiv. *)

(* Theorem 49 *)

About FSAT_rec_enum_t. (* Print Assumptions FSAT_rec_enum_t. *)
About FSAT_opt_enum_t. (* Print Assumptions FSAT_opt_enum_t. *)

(* Theorem 50 *)

About FULL_MONADIC_discernable. (* Print Assumptions FULL_MONADIC_discernable. *)

(* Theorem 51 *)

About FULL_TRAKHTENBROT. (* Print Assumptions FULL_TRAKHTENBROT. *)

(* Application to Separation Logic *)

From Undecidability.FOL
  Require Import FSAT FSAT_undec.

From Undecidability.SeparationLogic 
  Require Import SL MSL SL_undec Reductions.FSATdc_to_MSLSAT.

(* Syntax of full separation logic *)

Print sp_term.
Print sp_form.

(* Syntax of fragment *)
 
Print msp_form.

(* Definitions 53 *)

(* Satisfaction relation for (M)SL *)

Print msp_sat.
Print sp_sat.

(* Satisfiability for (M)SL *)

Print MSLSAT.
Print SLSAT.

(* Lemma 54 *)

Print FullTarski.sat. (* This is Tarski's satisfaction predicate *)
Check env2stack.
About FSATdc_to_MSLSAT.reduction_forwards. (* Print Assumptions FSATdc_to_MSLSAT.reduction_forwards. *)

(* Lemma 55 *)

Print FullTarski.sat. (* This is Tarski's satisfaction predicate *)
Check env.
About FSATdc_to_MSLSAT.reduction_backwards. (* Print Assumptions FSATdc_to_MSLSAT.reduction_backwards. *)

(* Theorem 56 *)

About TRAKHTENBROT_to_FSAT.reduction.  (* Print Assumptions TRAKHTENBROT_to_FSAT.reduction. *)
About FSATd_to_FSATdc.reduction.       (* Print Assumptions FSATd_to_FSATdc.reduction. *)
About FSATdc_to_MSLSAT.reduction.      (* Print Assumptions FSATdc_to_MSLSAT.reduction. *)
About MSLSAT_to_SLSAT.reduction.       (* Print Assumptions MSLSAT_to_SLSAT.reduction. *)

(* Corollary 57 *)

About SLSAT_undec.                     (* Print Assumptions SLSAT_undec.  *)




