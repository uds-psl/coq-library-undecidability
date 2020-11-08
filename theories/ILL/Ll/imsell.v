(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation.

From Undecidability.CounterMachines
  Require Import ndMM2.

From Undecidability.ILL 
  Require Import IMSELL.

From Undecidability.Shared.Libs.DLW 
  Require Import utils pos vec.

Set Implicit Arguments.

(** * Intuionistic Multiplicative Linear Logic with several exponentials and modabilities *)

Local Infix "~p" := (@Permutation _) (at level 70).
Local Notation "X ⊆ Y" := (forall a, X a -> Y a : Prop) (at level 70).
Local Infix "∊" := In (at level 70).

Local Reserved Notation "'⟦' A '⟧'" (at level 1, format "⟦ A ⟧").

Section IMSELL.

  Variable bang : Type.

  Notation "£ A" := (@imsell_var _ _ A) (at level 1).
  Notation "‼ l" := (@imsell_lban nat bang l).

  Fact imsell_lban_perm Σ Γ : Σ ~p Γ -> ‼Σ ~p ‼Γ.
  Proof. apply Permutation_map. Qed.

  Variable (bang_le : bang -> bang -> Prop) (bang_U : bang -> Prop).

  Infix "≤" := bang_le (at level 70).
  Notation U := bang_U. 

  Notation "u ≼ l" := (forall '(v,A), (v,A) ∊ l -> u ≤ v) (at level 70).
  Notation "Γ ⊢ A" := (S_imsell bang_le bang_U Γ A) (at level 70).

  Fact S_imsell_weak Γ Δ B : Forall (fun '(u,_) => U u) Γ -> Δ ⊢ B -> ‼Γ++Δ ⊢ B.
  Proof. 
    intros H1 H2; revert H1. 
    induction 1 as [ | (u,A) Γ H1 IH1 ]; simpl; auto.
    apply in_imsell_weak; auto. 
  Qed.

  Fact S_imsell_cntr Γ Δ B : Forall (fun '(u,_) => U u) Γ -> ‼Γ++‼Γ++Δ ⊢ B -> ‼Γ++Δ ⊢ B.
  Proof.
    intros H; revert H Δ.
    induction 1 as [ | (u,A) Γ H1 H2 IH2 ]; simpl; auto; intros Δ H.
    apply in_imsell_cntr; auto.
    apply in_imsell_perm with (‼Γ ++ (![u]A::![u]A::Δ)).
    + apply Permutation_sym.
      do 2 apply Permutation_cons_app; auto.
    + apply IH2.
      revert H; apply in_imsell_perm.
      rewrite app_assoc.
      apply Permutation_cons_app.
      rewrite <- app_assoc.
      apply Permutation_app; auto.
      apply Permutation_cons_app; auto.
  Qed.

  Theorem S_imsell_weak_cntr Σ Γ u A B : (u,A) ∊ Σ -> U u -> ‼Σ++Γ ⊢ B <-> ![u]A::‼Σ++Γ ⊢ B.
  Proof.
    intros H H1; apply In_perm in H as (Σ' & H).
    split.
    + apply in_imsell_weak; auto.
    + intros H2.
      apply in_imsell_perm with (‼((u,A) :: Σ') ++ Γ).
      * apply Permutation_app; auto.
        apply imsell_lban_perm; auto.
      * simpl; apply in_imsell_cntr; auto.
        revert H2; apply in_imsell_perm.
        simpl; apply Permutation_cons; auto.
        change (![u]A::‼Σ'++Γ) with (‼((u,A)::Σ')++Γ).
        apply Permutation_app; auto.
        apply imsell_lban_perm, Permutation_sym; auto.
  Qed.

  Section Trivial_Phase_semantics.

    (* We only consider the monoids nat^n *)

    Variables (n : nat) (s : nat -> vec nat n -> Prop)
              (K : bang -> vec nat n -> Prop).

    Hypothesis HK_antitone : forall u v, u ≤ v -> K v ⊆ K u.

    Notation ø := vec_zero.

    Definition imsell_tps_mult (X Y : _ -> Prop) (x : vec _ n) := exists a b, x = vec_plus a b /\ X a /\ Y b.
    Definition imsell_tps_imp (X Y : _ -> Prop) (v : vec _ n) := forall x, X x -> Y (vec_plus x v).
 
    Infix "⊛" := imsell_tps_mult (at level 65, right associativity).
    Infix "-⊛" := imsell_tps_imp (at level 65, right associativity).

    Fact imsell_tps_imp_zero X Y : (X -⊛ Y) ø <-> X ⊆ Y.
    Proof.
      split.
      + intros ? ? ?; rewrite <- vec_zero_plus, vec_plus_comm; auto.
      + intros ? ?; rewrite vec_plus_comm, vec_zero_plus; auto.
    Qed.

    Hypothesis HK_unit0 : forall u, K u ø.
    Hypothesis HK_plus  : forall u, K u ⊛ K u ⊆ K u.
    Hypothesis HK_unit1 : forall u, U u -> forall x, K u x -> x = ø.

    Fact imsell_tps_mult_mono (X1 X2 Y1 Y2 : _ -> Prop) : 
              X1 ⊆ X2 -> Y1 ⊆ Y2 -> X1⊛Y1 ⊆ X2⊛Y2.
    Proof.
      intros H1 H2 x (y & z & H3 & H4 & H5); subst.
      exists y, z; auto.
    Qed.

    Fixpoint imsell_tps (A : imsell_form nat bang) x : Prop :=
      match A with
        | £ X   => s X x
        | ![u]A => ⟦A⟧ x /\ K u x
        | A⊸B   => (⟦A⟧-⊛⟦B⟧) x
      end
    where "⟦ A ⟧" := (imsell_tps A).

    Fact imsell_tps_bang_zero u A : ⟦![u]A⟧ ø <-> ⟦A⟧ ø.
    Proof. simpl; split; auto; tauto. Qed.

    Fact imsell_tps_bang_U u A : U u -> (forall v, ⟦![u]A⟧ v <-> v = ø) <-> ⟦A⟧ ø.
    Proof.
      intros Hu; split.
      + intros H; rewrite <- imsell_tps_bang_zero, H; auto.
      + intros H v; split; simpl.
        * intros (_ & H1); revert H1; eauto.
        * intros ->; auto.
    Qed.

    Reserved Notation "⟪ Γ ⟫" (at level 1, format "⟪ Γ ⟫").

    Fixpoint imsell_tps_list Γ :=
      match Γ with
        | nil  => eq ø
        | A::Γ => ⟦A⟧⊛⟪Γ⟫
      end
    where "⟪ Γ ⟫" := (imsell_tps_list Γ).

    Fact imsell_tps_app Γ Δ x : ⟪Γ++Δ⟫ x <-> (⟪Γ⟫⊛⟪Δ⟫) x.
    Proof.
      revert Γ Δ x; intros Ga De.
      induction Ga as [ | A Ga IH ]; intros x; simpl; split; intros Hx.
      + exists vec_zero, x; simpl; rew vec.
      + destruct Hx as (? & ? & ? & ? & ?); subst; auto; rewrite vec_zero_plus; auto.
      + destruct Hx as (y & z & H1 & H2 & H3).
        apply IH in H3.
        destruct H3 as (c & d & H4 & H5 & H6).
        exists (vec_plus y c), d; split.
        * subst; apply vec_plus_assoc.
        * split; auto.
        exists y, c; auto.
      + destruct Hx as (y & d & ? & (z & g & ? & ? & ?) & ?).
        exists z, (vec_plus g d); split.
        * subst; symmetry; apply vec_plus_assoc.
        * split; auto.
          apply IH.
          exists g, d; auto.
    Qed.

    Fact imsell_tps_list_zero Γ : (forall A, A ∊ Γ -> ⟦A⟧ ø) -> ⟪Γ⟫ ø.
    Proof.
      induction Γ as [ | A Γ IH ]; simpl; auto; intros H.
      exists ø, ø; msplit 2; auto; now rewrite vec_zero_plus.
    Qed.

    Fact imsell_tps_lbang u Γ : u ≼ Γ -> ⟪‼Γ⟫ ⊆ K u.
    Proof.
      induction Γ as [ | (v,A) Γ IH ]; simpl; intros H1 x.
      + intros <-; auto.
      + intros (y & z & -> & (G1 & G2) & G3).
        apply HK_plus; exists y, z; msplit 2; auto.
        * revert G2; apply HK_antitone; auto.
          apply (H1 (v,A)); auto.
        * revert G3; apply IH.
          intros (w,B) ?; apply (H1 (_,B)); auto.
    Qed.

    Fact imsell_tps_perm Γ Δ : Γ ~p Δ -> ⟪Γ⟫ ⊆ ⟪Δ⟫.
    Proof.
      induction 1 as [ | A Ga De H IH | A B Ga | ]; simpl; auto.
      + intros x (y & z & H1 & H2 & H3).
        exists y, z; repeat split; auto.
      + intros x (y & z & H1 & H2 & c & d & H3 & H4 & H5).
        exists c, (vec_plus y d); split.
        * subst; rewrite (vec_plus_comm c), vec_plus_assoc, (vec_plus_comm c); auto.
        * split; auto.
          exists y, d; auto.
    Qed.
  
    Definition imsell_sequent_tps Γ A := ⟪Γ⟫ -⊛ ⟦A⟧.

    Notation "'[<' Γ '|-' A '>]'" := (imsell_sequent_tps Γ A) (at level 1, format "[<  Γ  |-  A  >]").

    Fact imsell_sequent_tps_mono Γ A B :
           ⟦A⟧ ⊆ ⟦B⟧ -> [< Γ |- A >] ⊆ [< Γ |- B >].
    Proof.
      intros H x; simpl; unfold imsell_sequent_tps.
      intros H1 ? H2; apply H, H1; auto.
    Qed.

    Fact imsell_perm_tps Γ Δ : Γ ~p Δ -> forall A, [< Γ |- A >] ⊆ [< Δ |- A >].
    Proof.
      intros H1 B x; unfold imsell_sequent_tps.
      intros H2 ? H3; apply H2; revert H3.
      apply imsell_tps_perm, Permutation_sym; auto.
    Qed.

    Fact imsell_sequent_tps_eq Γ A : [< Γ |- A >] ø <-> ⟪Γ⟫ ⊆ ⟦A⟧.
    Proof.
      split.
      * intros H x Hx.
        rewrite <- vec_zero_plus, vec_plus_comm.
        apply (H x); trivial.
      * intros H x Hx.
        rewrite vec_plus_comm, vec_zero_plus; auto.
    Qed.

    Theorem imsell_tps_sound Γ A : Γ ⊢ A -> [< Γ |- A >] ø.
    Proof.
      induction 1 as [ A 
                     | Γ Δ A H1 H2 IH2
                     | Γ Δ A B C H1 IH1 H2 IH2
                     | Γ A B H1 IH1
                     | u Γ A B H1 IH1
                     | u Γ A H1 H2 IH2
                     | u Γ A B H1 H2 IH2
                     | u Γ A B H1 H2 IH2
                     ]; unfold imsell_sequent_tps in * |- *.

      + intros x; simpl; intros (y & z & H1 & H2 & H3); subst; eq goal H2.
        f_equal; do 2 rewrite vec_plus_comm, vec_zero_plus; auto.

      + revert IH2; apply imsell_perm_tps; auto.

      + intros x (y & z & H3 & H4 & H5); simpl.
        apply IH2.
        apply imsell_tps_app in H5 as (g & d & H5 & H6 & H7).
        simpl in H4.
        apply IH1, H4 in H6.
        exists (vec_plus y g), d; repeat split; auto.
        * subst; apply vec_plus_assoc.
        * eq goal H6; f_equal; rew vec.

      + simpl; intros y Hy x Hx.
        rewrite vec_plus_assoc.
        apply IH1.
        exists x, y; repeat split; auto.

      + intros x (y & z & H2 & H3 & H4).
        apply IH1; exists y, z; repeat split; auto.
        apply H3.

      + intros x Hx; split.
        * apply IH2; auto.
        * rew vec.
          revert Hx. apply imsell_tps_lbang; auto.

      + intros x (y & z & -> & H3 & H4); rew vec.
        apply proj2, HK_unit1 in H3; auto; subst.
        rewrite vec_plus_comm.
        now apply IH2.
  
      + intros x (y & z & G2 & G3 & G4).
        apply IH2.
        exists y, z; repeat (split; auto).
        exists y, z; repeat (split; auto).
        apply proj2, HK_unit1 in G3; auto.
        subst; rew vec; auto.
    Qed.

  End Trivial_Phase_semantics.

End IMSELL.
