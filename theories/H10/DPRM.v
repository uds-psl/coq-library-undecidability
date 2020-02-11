(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** The DPRM theorem *)

Require Import List Arith Omega.

From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list sums.
From Undecidability.ILL.Code Require Import sss.
From Undecidability.ILL.Mm   Require Import mm_defs.
From Undecidability.H10.Fractran Require Import fractran_defs fractran_dio mm_fractran prime_seq.
From Undecidability.H10.Dio Require Import dio_logic dio_elem dio_single.
From Undecidability.MuRec Require Import recalg ra_utils recomp ra_recomp ra_dio_poly ra_mm ra_simul.

Set Implicit Arguments.

Local Notation "P /MM/ s ↓" := (sss_terminates (@mm_sss _) P s) (at level 70, no associativity).
Local Notation "l '/F/' x ↓" := (fractran_terminates l x) (at level 70, no associativity).
Local Notation "'⟦' p '⟧'" := (fun φ ν => dp_eval φ ν p).
Local Notation "f ⇓ v" := (ex (@ra_rel _ f v)) (at level 70, no associativity).

(** Definitions of n-ary recursive enumerable predicates *)

Section Various_definitions_of_recursive_enum.

  (* P is a predicate over n-tuples of nat *)

  Variable (n : nat) (P : vec nat n -> Prop).

  (* There is a Minsky machine that recognises P *)

  Definition mm_recognisable_n :=
    { m & { M : list (mm_instr (pos (n+m))) | forall v, P v <-> (1,M) /MM/ (1,vec_app v vec_zero) ↓ } }.

  (* There is a µ-recursive function of which P is the domain *)

  Definition µ_recursive_n := { f | forall v, P v <-> f ⇓ v }.

  Notation vec2val := (fun v => vec2fun v 0).

  (* There is a Diophantine logic formula satisfied exactly on P *)

  Definition dio_rec_form_n := 
    { A | forall v, P v <-> df_pred A (vec2val v) }.

  (* There is a list of elementary Diophantine constraints simultaneously
     satisfiable exactly on P *)

  Definition dio_rec_elem_n :=
    { l | forall v, P v <-> exists φ, Forall (dc_eval φ (vec2val v)) l }.

  (* There is a single Diophantine equations solvable exactly when
     its n-tuple of parameters belong to P *)

  Definition dio_rec_single_n :=
    { m : nat &
    { p : dio_polynomial (pos m) (pos n) &
    { q : dio_polynomial (pos m) (pos n) |
        forall v, P v <-> exists w, ⟦p⟧ (vec_pos w) (vec_pos v) 
                                  = ⟦q⟧ (vec_pos w) (vec_pos v) } } }.

  Local Theorem dio_rec_form_elem : dio_rec_form_n -> dio_rec_elem_n.
  Proof.
    intros (A & HA).
    destruct (dio_formula_elem A) as (l & _ & _ & Hl).
    exists l; intros v.
    rewrite HA, Hl; tauto.
  Qed. 

  Local Theorem dio_rec_elem_single : dio_rec_elem_n -> dio_rec_single_n.
  Proof.
    intros (l & Hl).
    destruct (dio_elem_equation l) as (e & _ & H2).
    destruct (dio_poly_eq_pos e) as (m & p & q & H3).
    set (p' := dp_proj_par n p).
    set (q' := dp_proj_par n q).
    exists m, p', q'; intros v.
    rewrite Hl, <- H2, H3.
    unfold dio_single_pred, p', q'; simpl; split.
    + intros (phi & H).
      exists (vec_set_pos phi).
      rewrite !dp_proj_par_eval.
      eq goal H; f_equal; apply dp_eval_ext; auto.
      all: intros; rewrite vec_pos_set; auto.
    + intros (w & H).
      exists (vec_pos w).
      rewrite !dp_proj_par_eval in H; auto.
  Qed.

  Local Theorem dio_rec_single_µ_rec : dio_rec_single_n -> µ_recursive_n.
  Proof.
    intros (m & p & q & H).
    exists (ra_dio_poly_find p q).
    intros v; rewrite H, ra_dio_poly_find_spec; tauto.
  Qed.

  Local Theorem µ_rec_mm_reco : µ_recursive_n -> mm_recognisable_n.
  Proof.
    intros (f & Hf).
    destruct (ra_mm_simulator f) as (m & M & H).
    exists (S m), M; intro.
    rewrite Hf, H; tauto.
  Qed.

  (** For n = 1 one could add FRACTRAN as well. The Gödel encoding
      of tuple make the definition of FRACTRAN recognisability for
      n > 1 a bit weird *)

  Section mm_reco_dio_form.

    Variable (HP : mm_recognisable_n).

    (* There is a FRACTRAN program simulating R *)

    Let FRACTRAN : { l | forall v, P v <-> l /F/ ps 1 * exp 1 v ↓ }.
    Proof.
      destruct HP as (m & Q & HQ).
      destruct mm_fractran_n with (P := Q) as (l & _ & Hl).
      exists l. 
      intros x; rewrite HQ, Hl.
      rewrite exp_app, exp_zero, Nat.mul_1_r; tauto.
    Qed.

    Local Theorem mm_reco_dio_form : dio_rec_form_n.
    Proof.
      destruct FRACTRAN as (Q & HQ).
      clear FRACTRAN HP.
      destruct FRACTRAN_HALTING_on_exp_diophantine with n Q as (A & HA); auto.
      exists A; intros v.
      rewrite HQ, HA, fun2vec_vec2fun; tauto.
    Qed.

  End mm_reco_dio_form.

End Various_definitions_of_recursive_enum.

Local Hint Resolve dio_rec_form_elem  dio_rec_elem_single
                   dio_rec_single_µ_rec  µ_rec_mm_reco
                   mm_reco_dio_form : core.

Local Ltac lsplit n := 
  match n with 
    | 0    => idtac 
    | S ?n => split; [ lsplit n | ]
   end.

Theorem DPRM_n n (R : vec nat n -> Prop) : 
         (mm_recognisable_n R  -> dio_rec_form_n R)
       * (dio_rec_form_n R     -> dio_rec_elem_n R)
       * (dio_rec_elem_n R     -> dio_rec_single_n R)
       * (dio_rec_single_n R   -> µ_recursive_n R)
       * (µ_recursive_n R      -> mm_recognisable_n R).
Proof. lsplit 4; auto. Qed. 

Check DPRM_n.
Print Assumptions DPRM_n.
