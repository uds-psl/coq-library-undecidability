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

Section gfp_unary.

  Variable (M : Type). 

  Implicit Type (P Q R : M -> Prop).

  Notation "P ⊆ Q" := (forall x, P x -> Q x).

  Let incl_trans P Q R : P ⊆ Q -> Q ⊆ R -> P ⊆ R.
  Proof. firstorder. Qed.

  Variable (F : (M -> Prop) -> M -> Prop)
           (HF0 : forall P Q, P ⊆ Q -> F P ⊆ F Q).

  Let i := iter F (fun _ => True).

  Let i0 : i 0 = fun _ => True.    Proof. auto. Qed.
  Let iS n : i (S n) = F (i n).    Proof. apply iter_S. Qed.

  Let i_S n : i (S n) ⊆ i n.
  Proof.
    unfold i.
    induction n as [ | n IHn ].
    + simpl; auto.
    + intros x.
      rewrite iter_S with (n := n).
      rewrite iter_S.
      apply HF0, IHn.
  Qed.

  Let i_decr n m : n <= m -> i m ⊆ i n.
  Proof. induction 1; auto. Qed.

  Definition gfp_unary x := forall n, i n x.

  Fact gfp_unary_greatest P : P ⊆ F P -> P ⊆ gfp_unary.
  Proof.
    intros HR x H n.
    revert x H.
    induction n as [ | n IHn ].
    + now auto.
    + apply incl_trans with (1 := HR).
      rewrite iS; apply HF0; auto.
  Qed. 

  Let gfp_fix1 : F gfp_unary ⊆ gfp_unary.
  Proof.
    intros x H n.
    apply i_S; rewrite iS.
    revert H; apply HF0; auto.
  Qed.

  (** This is omega continuity *)

  Variable HF4 : forall (s : nat -> M -> Prop), 
                        (forall n m, n <= m -> s m ⊆ s n) 
                     -> (fun x => forall n, F (s n) x) ⊆ F (fun x => forall n, s n x).

  Let gfp_fix0 : gfp_unary ⊆ F gfp_unary.
  Proof.
    intros x H.
    apply HF4; auto.
    intro; rewrite <- iS; apply H.
  Qed.

  Fact gfp_unary_fix x : F gfp_unary x <-> gfp_unary x.
  Proof. split; auto. Qed.

  (** This is for decidability *)

  Let dec P := forall x, { P x } + { ~ P x }.

  Variable HF5 : forall R, dec R -> dec (F R).

  Let i_dec n : dec (i n).
  Proof.
    induction n as [ | n IHn ].
    + rewrite i0; left; auto.
    + rewrite iS; apply HF5; auto.
  Qed.

  Let i_dup n m : n < m -> i n ⊆ i m -> forall k, n <= k -> forall x, gfp_unary x <-> i k x.
  Proof.
    intros H1 H2.
    generalize (i_decr H1) (i_S n); rewrite iS; intros H3 H4.
    generalize (incl_trans _ _ _ H2 H3); intros H5.
    assert (forall p, i n ⊆ i (p+n)) as H6.
    { induction p as [ | p IHp ]; auto.
      simpl plus; rewrite iS.
      apply incl_trans with (1 := H5), HF0; auto. }
    intros k Hk x; split; auto.
    intros H a.
    destruct (le_lt_dec a k).
    + revert H; apply i_decr; auto.
    + replace a with (a-n+n) by lia.
      apply H6.
      revert H; apply i_decr; auto.
  Qed.
 
  Let gfp_finite b : (exists n m, n < m <= b /\ i n ⊆ i m) 
                  -> (forall x, gfp_unary x <-> i b x).
  Proof.
    intros (n & m & H1 & H2). 
    apply i_dup with (2 := H2); auto; try lia.
  Qed.

  Variable HF6 : finite_t M.

  Theorem gfp_unary_finite_t : { n | forall x, gfp_unary x <-> i n x }.
  Proof.
    destruct finite_t_weak_dec_powerset with (1 := HF6)
      as (mR & HmR).
    exists (S (length mR)).
    set (l := map i (list_an 0 (S (length mR)))).
    apply (@gfp_finite (S (length mR))).
    destruct php_upto 
      with (R := fun R T => forall x, R x <-> T x)
           (l := l) (m := mR)
      as (a & R & b & T & c & H1 & H2).
    + intros R S H ?; rewrite H; tauto.
    + intros R S T H1 H2 ?; rewrite H1, H2; tauto.
    + intros R HR.
      apply in_map_iff in HR.
      destruct HR as (n & <- & _).
      destruct (HmR (i n)) as (T & H1 & H2).
      * intros x; destruct (i_dec n x); tauto.
      * exists T; auto.
    + unfold l; rewrite map_length, list_an_length; auto.
    + unfold l in H1.
      apply map_middle_inv in H1.
      destruct H1 as (a' & n & r' & H1 & H3 & H4 & H5).
      apply map_middle_inv in H5.
      destruct H5 as (b' & m & c' & H5 & H6 & H7 & H8).
      exists n, m; rewrite H4, H7; split; try (intros ? ?; apply H2); auto.
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

  Theorem gfp_unary_decidable : dec gfp_unary.
  Proof.
    destruct gfp_unary_finite_t as (n & Hn).
    intros x.
    destruct (i_dec n x); [ left | right ]; rewrite Hn; tauto.
  Qed.
  
End gfp_unary.