(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Max.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations utils enumerable
                 fol_ops fo_sig fo_terms fo_logic fo_enum
                 fo_sat fo_sat_dec red_utils.

Set Implicit Arguments.

Section FSAT_enumerable.

  Variable (Σ : fo_signature) 
           (H1 : discrete (syms Σ)) 
           (H2 : discrete (rels Σ)).

  Theorem FSAT_FSAT_in_pos A : FSAT Σ A <-> exists n, fo_form_fin_dec_SAT_in A (pos n).
  Proof.
    rewrite fo_form_fin_dec_SAT_discr_equiv.
    apply fo_form_fin_discr_dec_SAT_pos.
  Qed.

  Theorem FSAT_rec_enum_t : rec_enum_t (FSAT Σ).
  Proof.
    exists (fun n A => fo_form_fin_dec_SAT_in A (pos n)).
    exists.
    + intros n A; apply FSAT_in_dec; auto; apply finite_t_pos.
    + intros A; apply FSAT_FSAT_in_pos.
  Qed.

  Hypothesis (H3 : type_enum_t (syms Σ)).
  Hypothesis (H4 : type_enum_t (rels Σ)).

  Theorem FSAT_opt_enum_t : opt_enum_t (FSAT Σ).
  Proof.
    generalize FSAT_rec_enum_t.
    apply rec_enum_opt_enum_type_enum_t.
    apply type_enum_t_fol_form; auto.
  Qed.

End FSAT_enumerable.
