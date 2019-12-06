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
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations utils.

Set Implicit Arguments.

(** Description of what is a model described in extension *)

Definition ext_eq X Y (f g : X -> Y) := forall x, f x = g x.

Arguments ext_eq {_ _}.

Infix "≡" := ext_eq (at level 70, no associativity).

Definition described_ext_upto X (R : X -> X -> Prop) := 
     { n : nat & 
     { f : X -> pos n &
     { g : pos n -> X |
          (forall x, R (g (f x)) x)
       /\ (forall p, f (g p) = p) } } }.

Arguments described_ext_upto : clear implicits.

Fact finite_t_discr_enum_upto X : 
         ((finite_t X * discrete X) -> described_ext_upto X eq)
       * (described_ext_upto X eq -> (finite_t X * discrete X)).
Proof.
  split.
  * intros ((l & Hl) & Hd).
    destruct decidable_EQUIV_fin_quotient with (l := l) (R := @eq X)
      as [ n c r H1 H2 ]; auto.
    + intros; subst; auto.
    + intros x; exists x; auto.
    + exists n, c, r; split; auto.
      intros x; apply H2; rewrite H1; auto.
  * intros (n & f & g & H1 & H2); split.
    + exists (map g (pos_list _)).
      intros x; apply in_map_iff.
      exists (f x); split; auto.
      apply pos_list_prop.
    + intros x y.
      destruct (pos_eq_dec (f x) (f y)) as [ H | H ]; [ left | right ].
      - rewrite <- (H1 x), H, H1; auto.
      - contradict H; f_equal; auto.
Qed.

Section extensional.

  Fact finite_upto_pos_pos n m : finite_t_upto (pos n -> pos m) ext_eq.
  Proof.
    assert (finite_t (vec (pos m) n)) as H.
    { apply finite_t_vec, finite_t_pos. }
    destruct H as (l & Hl).
    exists (map (@vec_pos _ _)  l).
    intros f.
    exists (vec_pos (vec_set_pos f)); split.
    + apply in_map_iff; exists (vec_set_pos f); auto.
    + intro; rew vec.
  Qed.

  Fact decidable_pos_pos_ext_eq n m (f g : pos n -> pos m) : 
         { f ≡ g } + { ~ f ≡ g }.
  Proof.
    destruct (vec_eq_dec (@pos_eq_dec _) (vec_set_pos f) (vec_set_pos g)) 
        as [ H | H ]; [ left | right ].
    + intros p; rewrite <- (vec_pos_set f p), H; rew vec.
    + contradict H; apply vec_pos_ext; intro; rew vec.
  Qed.

  (** Upto extensional equality, pos n -> pos m 
      is in bijection with some (pos k) *)

  Fact enum_upto_pos_pos n m : described_ext_upto (pos n -> pos m) ext_eq.
  Proof.
    destruct (finite_upto_pos_pos n m) as (l & Hl).
    destruct decidable_EQUIV_fin_quotient with (l := l) (R := @ext_eq (pos n) (pos m))
      as [ k c r H1 H2 ]; auto.
    + intros p x; auto.
    + intros f g H p; rewrite H; auto.
    + intros f g h H1 H2 p; rewrite H1, H2; auto.
    + apply decidable_pos_pos_ext_eq.
    + exists k, c, r; split; auto.
      intros f p; apply H2; rewrite H1; auto.
  Qed.

End extensional.

Section fun_described_ext_upto.

  Variable (X Y : Type).

  Theorem fun_described_ext_upto :
             described_ext_upto X eq
          -> described_ext_upto Y eq
          -> described_ext_upto (X->Y) ext_eq.
  Proof.
    intros (n & f1 & g1 & H1 & H2) (m & f2 & g2 & H3 & H4).
    destruct (enum_upto_pos_pos n m) as (k & f & g & G1 & G2).
    set (c (h : X -> Y) := f (fun p => f2 (h (g1 p)))).
    set (r (p : pos k) (x : X) := g2 (g p (f1 x))).
    exists k, c, r; split.
    + intros h p; unfold r, c.
      rewrite G1, H3, H1; auto.
    + (** need to assume that f is extensional itself *)
      admit.
  Admitted.

End fun_described_ext_upto.

