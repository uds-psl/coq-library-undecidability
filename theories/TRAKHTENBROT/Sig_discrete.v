(*************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(*************************************************************)

Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops fo_sig fo_terms fo_logic fo_sat discrete.

Set Implicit Arguments.

(* * FSAT and FSAT over discrete model are equivalent *)

(* This equivalence and hence reduction most probably cannot
    be proved for infinite models, or at least the way it is
    proved in here *)

(* Satisfiability of A in a finite and decidable model implies satisfiability 
    of A in a finite, decidable and discrete model, in fact in a model based on 
    the finite type (pos n) *)

Theorem fo_discrete_removal Σ (A : fol_form Σ) :
             fo_form_fin_dec_SAT A
          -> exists n, fo_form_fin_discr_dec_SAT_in A (pos n).
Proof.
  intros (X & M & Hfin & Hdec & phi & HA).
  set (ls := fol_syms A).
  set (lr := fol_rels A).
  destruct (fo_fin_model_discretize ls lr Hfin Hdec)
    as (n & Md & Mdec & f & E).
  set (psy n := f (phi n)).
  exists n, (@pos_eq_dec _), Md, (finite_t_pos _) , Mdec, psy.
  revert HA.
  apply fo_model_projection with (p := f); 
    unfold lr, ls; auto; apply incl_refl.
Qed.

Theorem fo_form_fin_dec_SAT_fin_discr_dec Σ (A : fol_form Σ) :
             fo_form_fin_dec_SAT A 
          -> fo_form_fin_discr_dec_SAT A.
Proof.
  intros H.
  destruct fo_discrete_removal with (1 := H) (A := A)
    as (n & Hn); auto.
  exists (pos n); auto.
Qed.
