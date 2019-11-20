(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Nat Lia Relations.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list finite.

From Undecidability.TRAKHTENBROT
  Require Import notations fin_upto.

Set Implicit Arguments.

Check finite_t_fin_t_eq.

Section gfp.

  Variable (M : Type). 

  Implicit Type (R T : M -> M -> Prop).

  Notation "R ⊆ T" := (forall x y, R x y -> T x y).

  Notation "R 'o' T" := (fun x z => exists y, R x y /\ T y z) (at level 58).

  Let incl_trans R S T : R ⊆ S -> S ⊆ T -> R ⊆ T.
  Proof. firstorder. Qed.

  Let comp_mono R R' T T' : R ⊆ R' -> T ⊆ T' -> R o T ⊆ R' o T'.
  Proof. firstorder. Qed. 

  Variable (F : (M -> M -> Prop) -> M -> M -> Prop)
           (HF0 : forall R T, R ⊆ T -> F R ⊆ F T).

  Let sym R := fun x y => R y x.

  Let i := iter F (fun _ _ => True).

  Let iS n : i (S n) = F (i n).
  Proof. apply iter_S. Qed.

  Let i0 : i 0 = fun _ _ => True.
  Proof. auto. Qed.

  Let i_S n : i (S n) ⊆ i n.
  Proof.
    unfold i.
    induction n as [ | n IHn ].
    + simpl; auto.
    + intros x y.
      rewrite iter_S with (n := n).
      rewrite iter_S.
      apply HF0, IHn.
  Qed.

  Let i_decr n m : n <= m -> i m ⊆ i n.
  Proof. induction 1; auto. Qed.

  Definition gfp x y := forall n, i n x y.

  Notation I := (@eq M).

  Hypothesis HF1 : I ⊆ F I.

  Let i_refl n : I ⊆ i n.
  Proof.
    induction n as [ | n IHn ].
    + rewrite i0; auto.
    + rewrite iS.
      apply incl_trans with (1 := HF1), HF0, IHn.
  Qed.
  
  Let gfp_refl : I ⊆ gfp.
  Proof.
    intros x y [] n.
    apply i_refl; auto.
  Qed.

  Hypothesis HF2 : forall R, sym (F R) ⊆ F (sym R).

  Let i_sym n : sym (i n) ⊆ i n.
  Proof.
    induction n as [ | n IHn ].
    + intros x y; unfold i; simpl; auto.
    + rewrite iS.
      apply incl_trans with (2 := HF0 _ IHn), HF2.
  Qed.

  Let gfp_sym : sym gfp ⊆ gfp.
  Proof.
    intros x y H n.
    apply i_sym, H.
  Qed.

  Hypothesis HF3 : forall R, F R o F R ⊆ F (R o R).

  Let i_trans n : i n o i n ⊆ i n.
  Proof.
    induction n as [ | n IHn ].
    + rewrite i0; auto.
    + rewrite iS.
      apply incl_trans with (1 := @HF3 _), HF0, IHn.
  Qed.

  Let gfp_trans : gfp o gfp ⊆ gfp.
  Proof.
    intros x y H n.
    apply i_trans.
    revert H; apply comp_mono; auto.
  Qed.

  Fact gfp_equiv : equiv _ gfp.
  Proof.
    msplit 2.
    + intro; apply gfp_refl; auto.
    + intros x y z H1 H2; apply gfp_trans; exists y; auto.
    + intros x y; apply gfp_sym.
  Qed.

  Fact gfp_greatest R : R ⊆ F R -> R ⊆ gfp.
  Proof.
    intros HR x y H n.
    revert x y H.
    induction n as [ | n IHn ].
    + now auto.
    + apply incl_trans with (1 := HR).
      rewrite iS; apply HF0; auto.
  Qed. 

  Let gfp_fix1 : F gfp ⊆ gfp.
  Proof.
    intros x y H n.
    apply i_S; rewrite iS.
    revert H; apply HF0; auto.
  Qed.

  (** This is omega continuity *)

  Variable HF4 : forall (s : nat -> M -> M -> Prop), 
                        (forall n m, n <= m -> s m ⊆ s n) 
                     -> (fun x y => forall n, F (s n) x y) ⊆ F (fun x y => forall n, s n x y).

  Let gfp_fix0 : gfp ⊆ F gfp.
  Proof.
    intros x y H.
    apply HF4; auto.
    intro; rewrite <- iS; apply H.
  Qed.

  Fact gfp_fix x y : F gfp x y <-> gfp x y.
  Proof. split; auto. Qed.

  (** This is for decidability *)

  Let dec R := forall x y, { R x y } + { ~ R x y }.

  Variable HF5 : forall R, dec R -> dec (F R).

  Let i_dec n : dec (i n).
  Proof.
    induction n as [ | n IHn ].
    + rewrite i0; left; auto.
    + rewrite iS; apply HF5; auto.
  Qed.

  (** For the decidability of gfp, we need the finiteness
      so that gfp = i n for a sufficiently large n *)

  (** There is a list lR of relations which contains every
      i n upto equivalence (because X is finite_t)

      By the (generalized) PHP, for n greater than
      the length of lR, one can find a duplicate
      in the list [i 0; ...;i n] ie a < b <= n such
      that i a ~ T1 ~ T2 ~ i b

      Then one can deduce i a ~ i (S a) ~ gfp *)

  Let i_dup n m : n < m -> i n ⊆ i m -> forall k, n <= k -> forall x y, gfp x y <-> i k x y.
  Proof.
    intros H1 H2.
    generalize (i_decr H1) (i_S n); rewrite iS; intros H3 H4.
    generalize (incl_trans _ _ _ H2 H3); intros H5.
    assert (forall p, i n ⊆ i (p+n)) as H6.
    { induction p as [ | p IHp ]; auto.
      simpl plus; rewrite iS.
      apply incl_trans with (1 := H5), HF0; auto. }
    intros k Hk x y; split; auto.
    intros H a.
    destruct (le_lt_dec a k).
    + revert H; apply i_decr; auto.
    + replace a with (a-n+n) by lia.
      apply H6.
      revert H; apply i_decr; auto.
  Qed.
 
  Let gfp_finite b : (exists n m, n < m <= b /\ i n ⊆ i m) -> (forall x y, gfp x y <-> i b x y).
  Proof.
    intros (n & m & H1 & H2). 
    apply i_dup with (2 := H2); auto; try lia.
  Qed.

  Variable HF6 : finite_t M.

  Theorem gfp_finite_t : { n | forall x y, gfp x y <-> i n x y }.
  Proof.
    destruct finite_t_weak_dec_rels with (1 := HF6)
      as (mR & HmR).
    exists (S (length mR)).
    set (l := map i (list_an 0 (S (length mR)))).
    apply (@gfp_finite (S (length mR))).
    destruct php_upto 
      with (R := fun R T => forall x y, R x y <-> T x y)
           (l := l) (m := mR)
      as (a & R & b & T & c & H1 & H2).
    + intros R S H ? ?; rewrite H; tauto.
    + intros R S T H1 H2 ? ?; rewrite H1, H2; tauto.
    + intros R HR.
      apply in_map_iff in HR.
      destruct HR as (n & <- & _).
      destruct (HmR (i n)) as (T & H1 & H2).
      * intros x y; destruct (i_dec n x y); tauto.
      * exists T; auto.
    + unfold l; rewrite map_length, list_an_length; auto.
    + unfold l in H1.
      apply map_middle_inv in H1.
      destruct H1 as (a' & n & r' & H1 & H3 & H4 & H5).
      apply map_middle_inv in H5.
      destruct H5 as (b' & m & c' & H5 & H6 & H7 & H8).
      exists n, m; rewrite H4, H7; split; try (intros ? ?; apply H2).
      clear H3 H4 H6 H7 H8 H2; subst r'.
      generalize H1; intros H2.
      apply f_equal with (f := @length _) in H2.
      rewrite list_an_length, app_length in H2.
      simpl in H2; rewrite app_length in H2; simpl in H2.
      apply list_an_app_inv in H1.
      destruct H1 as (_ & H1); simpl in H1.
      injection H1; clear H1; intros H1 H3.
      symmetry in H1.
      apply list_an_app_inv in H1.
      destruct H1 as (_ & H1); simpl in H1.
      injection H1; clear H1; intros _ H1.
      lia.
  Qed.

  Theorem gfp_decidable : dec gfp.
  Proof.
    destruct gfp_finite_t as (n & Hn).
    intros x y.
    destruct (i_dec n x y); [ left | right ]; rewrite Hn; tauto.
  Qed.
  
End gfp.