(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** Elementary Diophantine constraints w/o parameters
    and with only the constant 1 i.e. constraints 
    are of three shapes:

      x = 1 | x+y = z | x*y = z  with x,y,z in nat 

  *)

Require Import List Arith.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_decidable utils_nat.

From Undecidability.H10C
  Require Import h10c_defs.

Set Implicit Arguments.

Local Notation "〚 c 〛" := (h10c_sem c).
Local Notation " '⟪' c '⟫' " := (h10uc_sem c).

Section decidability_of_validity.

  (** Validity is decidable, this is easily proved in here
      but of course satisfiability is undecidable but this 
      is much more complicated to establish *)

  Let plus_swap (P Q : Prop) : { P } + { Q } -> { Q } + { P }.
  Proof. tauto. Qed.

  Fact h10c_sem_dec c φ : {〚c〛φ } + { ~〚c〛φ }.
  Proof. destruct c; apply eq_nat_dec. Qed.

  Fact h10lc_sem_dec l φ : { c | In c l /\ ~〚c〛φ } + { forall c, In c l ->〚c〛φ }.
  Proof.
    apply list_choose_dep. 
    intros c _; apply plus_swap, h10c_sem_dec.
  Qed.

  Fact h10luc_sem_dec l φ : { c | In c l /\ ~ ⟪c⟫ φ } + { forall c, In c l -> ⟪c⟫ φ }.
  Proof.
    apply list_choose_dep.
    intros c _; apply plus_swap.
    destruct c as ((?,?),?); apply eq_nat_dec.
  Qed.

End decidability_of_validity.

Section h10c_vars_bound.

  (** A small utility library that help at encoding φ with a finitary map *)

  Definition h10c_vars c :=
    match c with
      | h10c_one x      => x::nil
      | h10c_plus x y z => x::y::z::nil
      | h10c_mult x y z => x::y::z::nil
    end.

  Definition h10uc_vars (c : h10uc) :=
    match c with (x,y,z) => x::y::z::nil end.

  Fact h10c_vars_equiv c phi psy : (forall x, In x (h10c_vars c) -> phi x = psy x)
                                -> 〚c〛phi <->〚c〛psy.
  Proof.
    destruct c; simpl; intros H; repeat rewrite H; tauto.
  Qed.

  Fact h10uc_vars_equiv c phi psy : (forall x, In x (h10uc_vars c) -> phi x = psy x)
                                -> ⟪c⟫ phi <-> ⟪c⟫ psy.
  Proof.
    destruct c as ((?,?),?); simpl; intros H; repeat rewrite H; tauto.
  Qed.

  Definition h10lc_vars := flat_map h10c_vars.
  Definition h10luc_vars := flat_map h10uc_vars.

  Fact h10lc_vars_equiv l phi psy : (forall x, In x (h10lc_vars l) -> phi x = psy x)
                                  -> forall c, In c l ->〚c〛phi <->〚c〛psy.
  Proof.
    intros H c Hc.
    apply h10c_vars_equiv.
    intros x Hx; apply H, in_flat_map.
    exists c; auto.
  Qed.

  Fact h10luc_vars_equiv l phi psy : (forall x, In x (h10luc_vars l) -> phi x = psy x)
                                   -> forall c, In c l -> ⟪c⟫ phi <-> ⟪c⟫ psy.
  Proof.
    intros H c Hc.
    apply h10uc_vars_equiv.
    intros x Hx; apply H, in_flat_map.
    exists c; auto.
  Qed.

  Definition h10lc_bound l := S (lmax (h10lc_vars l)).
  Definition h10luc_bound l := S (lmax (h10luc_vars l)).

  Fact h10lc_bound_prop l phi psy : (forall x, x < h10lc_bound l -> phi x = psy x)
                                  -> forall c, In c l ->〚c〛phi <->〚c〛psy.
  Proof.
    intros H; apply h10lc_vars_equiv.
    intros x Hc; apply H, le_n_S, lmax_prop; auto.
  Qed.

  Fact h10luc_bound_prop l phi psy : (forall x, x < h10luc_bound l -> phi x = psy x)
                                   -> forall c, In c l -> ⟪c⟫ phi <-> ⟪c⟫ psy.
  Proof.
    intros H; apply h10luc_vars_equiv.
    intros x Hc; apply H, le_n_S, lmax_prop; auto.
  Qed.

End h10c_vars_bound.

