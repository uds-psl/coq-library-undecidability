(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega Permutation Relations Bool Eqdep_dec.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_nat.

Set Implicit Arguments.

Definition nat_enum X := { f : nat -> option X & forall x, { n | f n = Some x } }.

Section ep_quotient.

  Variable (R : nat -> nat -> Prop).

  Infix "≈" := R (at level 70, no associativity).
 
  Hypothesis HR1 : equiv _ R.
  Hypothesis HR2 : forall x y, { x ≈ y } + { x ≈ y -> False }.

  Let is_repr n r := r ≈ n /\ forall m, m ≈ n -> r <= m.

  Let is_repr_inj n r1 r2 : is_repr n r1 -> is_repr n r2 -> r1 = r2.
  Proof.
    intros (H1 & H2) (H3 & H4).
    apply Nat.le_antisymm; auto.
  Qed.

  Let is_repr_involutive n r : is_repr n r -> is_repr r r.
  Proof.
    intros (H1 & H2); split.
    + apply (proj1 HR1).
    + intros m Hm; apply H2.
      apply (proj1 (proj2 HR1) _ r); auto.
  Qed.

  Let find_repr n : sig (is_repr n).
  Proof. 
    destruct min_dec with (P := fun x => x ≈ n)
      as (r & H1 & H2).
    + intros m; destruct (HR2 m n); auto.
    + exists n; apply (proj1 HR1).
    + exists r; split; auto.
  Qed.

  Let is_repr_dec n r : { is_repr n r } + { ~ is_repr n r }.
  Proof.
    destruct (HR2 r n) as [ H1 | H1 ].
    2: right; intros []; contradict H1; auto.
    destruct bounded_search with (m := r) (P := fun x => x ≈ r)
      as [ (p & H2 & H3) | H ].
    + intros m ?; destruct (HR2 m r); auto.
    + right; intros [ H4 H5 ].
      specialize (H5 _ (proj1 (proj2 HR1) _ _ _ H3 H4)); omega.
    + left; split; auto.
      intros m Hm.
      destruct (le_lt_dec r m) as [ | D ]; auto.
      apply H in D; try tauto.
      apply (proj1 (proj2 HR1) _ n); auto.
      revert H1; apply HR1.
  Qed.

  Let P n := if is_repr_dec n n then true else false.

  Let P_spec n : P n = true <-> is_repr n n.
  Proof.
    unfold P; destruct (is_repr_dec n n); split; try tauto; discriminate.
  Qed.

  Let X := sig (fun x => P x = true).

  Let pi1_inj : forall x y : X, proj1_sig x = proj1_sig y -> x = y.
  Proof.
    intros (x & H1) (y & H2); simpl; intros; subst; f_equal.
    apply UIP_dec, bool_dec.
  Qed.

  Let X_discrete : forall x y : X, { x = y } + { x <> y }.
  Proof.
    intros (x & Hx) (y & Hy).
    destruct (eq_nat_dec x y) as [ | H ].
    + left; apply pi1_inj; simpl; auto.
    + right; contradict H; inversion H; auto.
  Qed.

  Let HX : nat_enum X.
  Proof.
    assert (f : forall n, { x : X | proj1_sig x = n } + { P n = false }).
    { intros n.
      case_eq (P n).
      + intros Hn; left; exists (exist _ n Hn); auto.
      + right; auto. }
    exists (fun n => match f n with inleft (exist _ x _) => Some x | inright _ => None end).
    intros (n & Hn).
    exists n.
    destruct (f n) as [ (x & Hx) | H ].
    + f_equal; apply pi1_inj; simpl; auto.
    + exfalso; revert H; rewrite Hn; discriminate.
  Qed.

  Let is_repr_P n : is_repr n n -> P n = true.
  Proof. apply P_spec. Qed.

  Let cls (n : nat) : X.
  Proof.
    destruct (find_repr n) as (x & Hx).
    exists x; apply is_repr_P.
    revert Hx; apply is_repr_involutive.
  Defined.

  Let rpr (x : X) := proj1_sig x.

  Theorem ep_quotient : { X : Type & 
                        { _ : nat_enum X & 
                        { _ : forall x y : X, { x = y } + { x <> y } &
                        { cls : nat -> X & 
                        { rpr : X -> nat |
                             (forall c, cls (rpr c) = c)
                          /\ (forall x, rpr (cls x) ≈ x) } } } } }.
  Proof.
    exists X, HX, X_discrete, cls, rpr; split.
    + intros (n & Hn); simpl.
      apply pi1_inj; simpl.
      unfold cls.
      destruct (find_repr n) as (r & Hr); simpl.
      rewrite P_spec in Hn.
      revert Hr Hn; apply is_repr_inj.
    + intros x.
      unfold cls.
      destruct (find_repr x) as (n & Hn); apply Hn.
  Qed.

End ep_quotient.

Print nat_enum.
Check ep_quotient.
