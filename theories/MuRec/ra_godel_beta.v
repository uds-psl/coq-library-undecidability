(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Lia.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_nat gcd crt sums.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.MuRec 
  Require Import recalg recomp beta ra_utils ra_recomp.

Set Implicit Arguments.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

Opaque ra_cst_n ra_iter_n ra_iter ra_prim_min ra_prim_max.
Opaque ra_plus ra_pred ra_minus ra_mult ra_exp ra_div ra_rem.
Opaque ra_ite ra_eq.
Opaque ra_div2 ra_mod2 ra_pow2 ra_notdiv_pow2.
Opaque ra_decomp_l ra_decomp_r ra_recomp.

Section ra_godel_beta.

  (** Gödel Beta function *)

  Definition ra_godel_beta : recalg 3.
  Proof.
    ra root ra_rem.
    + ra arg pos0.
    + ra root ra_succ.
      ra root ra_mult.
      * ra root ra_succ.
        ra arg pos2.
      * ra arg pos1.
  Defined.

  Fact ra_godel_beta_prim_rec : prim_rec ra_godel_beta.
  Proof. ra prim rec. Qed.
 
  Fact ra_godel_beta_val a b n : ⟦ra_godel_beta⟧ (a##b##n##vec_nil) (godel_beta a b n).
  Proof.
    exists (a##S ((S n)*b)##vec_nil); split.
    + apply ra_rem_val; discriminate.
    + pos split; simpl; auto.
      exists (((S n)*b)##vec_nil); split; simpl; auto.
      pos split; simpl.
      exists (S n##b##vec_nil); split.
      * apply ra_mult_val.
      * pos split; simpl; auto.
        exists (n##vec_nil); split; simpl; auto.
        pos split; simpl; auto.
  Qed.

  Fact ra_godel_beta_rel v e : ⟦ra_godel_beta⟧ v e <-> e = godel_beta (vec_pos v pos0) (vec_pos v pos1) (vec_pos v pos2).
  Proof.
    vec split v with a; vec split v with b; vec split v with n; vec nil v.
    split.
    + intros H; apply ra_rel_fun with (1 := H), ra_godel_beta_val; auto.
    + intros; subst; apply ra_godel_beta_val; auto.
  Qed.

End ra_godel_beta.

Hint Resolve ra_godel_beta_prim_rec ra_godel_beta_val.
Opaque ra_godel_beta.

Section ra_beta.

  Definition ra_beta : recalg 2.
  Proof.
    ra root ra_godel_beta.
    + ra root ra_decomp_l.
      ra arg pos0.
    + ra root ra_decomp_r.
      ra arg pos0.
    + ra arg pos1.
  Defined.

  Fact ra_beta_prim_rec : prim_rec ra_beta.
  Proof. ra prim rec. Qed.

  Fact ra_beta_val a n : ⟦ra_beta⟧ (a##n##vec_nil) (beta a n).
  Proof.
    exists (decomp_l a##decomp_r a##n##vec_nil); split.
    { apply ra_godel_beta_val. }
    pos split; simpl; auto;
      exists (a##vec_nil); split; auto;
      pos split; simpl; auto.
  Qed.

  Fact ra_beta_rel v e : ⟦ra_beta⟧ v e <-> e = beta (vec_pos v pos0) (vec_pos v pos1).
  Proof.
    vec split v with a; vec split v with n; vec nil v.
    split.
    + intros H; apply ra_rel_fun with (1 := H), ra_beta_val; auto.
    + intros; subst; apply ra_beta_val; auto.
  Qed.

End ra_beta.

Hint Resolve ra_beta_prim_rec ra_beta_val.

Eval compute in ra_size ra_rem.
 

