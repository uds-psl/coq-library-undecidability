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

  Definition mu_recursive_n := { f | forall v, P v <-> f ⇓ v }.

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

  Local Theorem dio_rec_single_µ_rec : dio_rec_single_n -> mu_recursive_n.
  Proof.
    intros (m & p & q & H).
    exists (ra_dio_poly_find p q).
    intros v; rewrite H, ra_dio_poly_find_spec; tauto.
  Qed.

  Local Theorem µ_rec_mm_reco : mu_recursive_n -> mm_recognisable_n.
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

Theorem DPRM_n n (R : vec nat n -> Prop) : 
         (mm_recognisable_n R  -> dio_rec_form_n R)
       * (dio_rec_form_n R     -> dio_rec_elem_n R)
       * (dio_rec_elem_n R     -> dio_rec_single_n R)
       * (dio_rec_single_n R   -> mu_recursive_n R)
       * (mu_recursive_n R     -> mm_recognisable_n R).
Proof. lsplit 4; auto. Qed. 

(* Check DPRM_n. *)


Local Notation ø := vec_nil.

Section Various_definitions_of_recursive_enum_1.

  (* P is a predicate over nat *)

  Variable (P : nat -> Prop).

  (* There is a Minsky machine that recognises P *)

  Definition mm_recognisable :=
    { m & { M : list (mm_instr (pos (S m))) | forall x, P x <-> (1,M) /MM/ (1,x##vec_zero) ↓ } }.

  (* There is a µ-recursive function of which P is the domain *)

  Definition mu_recursive := { f | forall x, P x <-> f ⇓ (x##ø) }.

  (* There is a single Diophantine equations solvable exactly when
     its n-tuple of parameters belong to P *)

  Definition dio_rec_single :=
    { m : nat &
    { p : dio_polynomial (pos m) (pos 1) &
    { q : dio_polynomial (pos m) (pos 1) |
        forall x, P x <-> exists w, ⟦p⟧ (vec_pos w) (fun _ => x) 
                                  = ⟦q⟧ (vec_pos w) (fun _ => x) } } }.

  (** Reworking ps and qs to avoid the first primes, may be 2, 3 and 5
      and show be possible to replace with

            FRACTRAN_RECO := { l | forall x, P x <-> l /F/ 2^(1+x) ↓ }

      Let use assume l does not use 2, 3, 5 and P x <-> l /F/ 7.11^x ↓

      then let us define l' = [ 5*11/3*2; 3/5; 3/2; 7/3 ] ++ l

      then l' /F/ 2^(1+x) ~~> 3.2^x
           l' /F/ 3.2^0  ~~> 7.11^0
           l' /F/ 3.11^y.2^(1+x) ~~> 5.11^(1+y).2^x ~~> 3.11^(1+y).2^x
      hence l' /F/ 3.2^x ~~> 3.11^x ~~> 7.11^x 

      and after that the first fractions of l' cannot be used
      because neither 2, 3 or 5 will ever be a factor of the 
      current state.

      So l' /F/ 2^(1+x) ↓ <-> l /F/ 7.11^x <-> P x

      One the other hand, with P x <-> l /F/ x ↓ it is not possible
      to represent arbitrary RE predicates 

      Indeed for any l, on can show forall x, l /F/ x ↓ -> l /F/ 1 ↓  
      because for l to terminate on x, it cannot contain any p/q being
      a nat, hence in that case, the computation from 1 cannot start

      So the predicate l /F/ x ↓ cannot serve as a generic RE predicate
      because it cannot simulate P x := x = 2.

     *)

  Definition fractran_recognisable := { l | forall x, P x <-> l /F/ 5*7^x ↓ }.

  Local Theorem µ_rec_mm_reco_1 : mu_recursive -> mm_recognisable.
  Proof.
    intros H.
    destruct µ_rec_mm_reco with (P := fun v : vec _ 1 => P (vec_head v))
      as (m & M & HM).
    + destruct H as (f & Hf); exists f.
      intros v; vec split v with x; vec nil v; auto.
    + exists m, M; intros x; rewrite (HM (x##ø)).
      rewrite vec_app_cons, vec_app_nil; tauto.
  Qed.

  Local Theorem mm_reco_fractran_1 : mm_recognisable -> fractran_recognisable.
  Proof.
    intros (m & M & HM).
    destruct mm_fractran with (P := M) as (l & Hl).
    exists l; intro; rewrite HM, Hl, ps_1, qs_1; tauto.
  Qed.

  Local Theorem fractran_dio_rec_single_1 : fractran_recognisable -> dio_rec_single.
  Proof.
    intros (l & Hl).
    destruct (FRACTRAN_HALTING_on_exp_diophantine 1 l) as (A & HA).
    simpl fun2vec in HA; unfold exp in HA.
    destruct dio_rec_elem_single with (P := fun v : vec _ 1 => P (vec_head v))
      as (m & p & q & H).
    + apply dio_rec_form_elem.
      exists A.
      intros v; vec split v with x; vec nil v; simpl.
      rewrite Hl, HA, <- qs_1, <- ps_1.
      unfold vec2fun; simpl.
      rewrite mult_1_r; tauto.
    + exists m, p, q; intros x.
      rewrite (H (x##ø)).
      apply exists_equiv; intros v.
      apply equal_equiv; f_equal; apply dp_eval_ext; auto.
      all: intros i; analyse pos i; auto.
  Qed.

  Local Theorem dio_rec_single_mm_1 : dio_rec_single -> mu_recursive.
  Proof.
    intros H.
    destruct dio_rec_single_µ_rec with (P := fun v : vec _ 1 => P (vec_head v))
      as (f & Hf).
    + destruct H as (m & p & q & H).
      exists m, p, q.
      intros v; vec split v with x; vec nil v.
      simpl vec_head; rewrite H.
      apply exists_equiv; intros w.
      apply equal_equiv; f_equal; apply dp_eval_ext; auto.
      all: intros i; analyse pos i; auto.
    + exists f; intros x; apply (Hf (_##ø)).
  Qed.

End Various_definitions_of_recursive_enum_1.

Local Hint Resolve µ_rec_mm_reco_1
                   mm_reco_fractran_1 
                   fractran_dio_rec_single_1
                   dio_rec_single_mm_1 : core.

Theorem DPRM_1 (P : nat -> Prop) :
         (mm_recognisable P       -> fractran_recognisable P)
       * (fractran_recognisable P -> dio_rec_single P)   
       * (dio_rec_single P        -> mu_recursive P)
       * (mu_recursive P           -> mm_recognisable P).
Proof. lsplit 3; auto. Qed. 

Check DPRM_1.



