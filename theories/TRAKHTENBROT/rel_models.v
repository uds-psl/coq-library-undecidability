(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Nat Lia Relations Bool.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec fin_quotient.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops.

Set Implicit Arguments.

Local Notation " e '#>' x " := (vec_pos e x).
Local Notation " e [ v / x ] " := (vec_change e x v).

Section reifying_relational_models.

  Variable (X Y : Type) 
           (Yfin : finite_t Y) 
           (Ydiscr : discrete Y)
           (R : X -> Y -> Prop) 
           (Rdec : forall x y, { R x y } + { ~ R x y })
           (Rtot : forall x, exists y, R x y).

  (** A finitary strong choice principle *)

  Theorem reify_total_dec_rel2 : { f : X -> Y | forall x, R x (f x) }.
  Proof.
    destruct (finite_t_discrete_bij_t_pos Yfin Ydiscr)
      as (n & i & s & H1 & H2).
    set (P x p := R x (s p)).
    assert (H3 : forall x p, {P x p} + {~ P x p}) by (intros; apply Rdec).
    assert (H4 : forall x, ex (P x)).
    { intros x; destruct (Rtot x) as (y & Hy); exists (i y); red; rewrite H1; auto. }
    generalize (fun x => (pos_dec_reif (H3 x) (H4 x))); intros H5.
    exists (fun x => s (proj1_sig (H5 x))).
    intros x; apply (proj2_sig (H5 x)).
  Qed.

End reifying_relational_models.

Check reify_total_dec_rel2.