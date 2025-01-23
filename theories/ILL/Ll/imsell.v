(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Permutation.

From Undecidability.ILL 
  Require Import IMSELL.

From Undecidability.Shared.Libs.DLW 
  Require Import utils pos vec.

Set Implicit Arguments.

(* * Intuionistic Multiplicative Linear Logic with several exponentials and modabilities *)

Local Infix "~p" := (@Permutation _) (at level 70).
Local Notation "X ⊆ Y" := (forall a, X a -> Y a : Prop) (at level 70).
Local Infix "∊" := In (at level 70).

Local Reserved Notation "'⟦' A '⟧'" (at level 0, format "⟦ A ⟧").

Section IMSELL.

  Variable bang : Type.

  Notation "£" := (@imsell_var _ _).
  Notation "‼ l" := (@imsell_lban nat bang l).

  Fact imsell_lban_perm Σ Γ : Σ ~p Γ -> ‼Σ ~p ‼Γ.
  Proof. apply Permutation_map. Qed.

  Variable (bang_le : bang -> bang -> Prop) (bang_U : bang -> Prop).

  Infix "≤" := bang_le (at level 70).
  Notation U := bang_U. 

  Notation "u ≼ l" := (forall '(v,A), (v,A) ∊ l -> u ≤ v) (at level 70).
  Notation "Γ ⊢ A" := (@S_imsell nat _ bang_le bang_U Γ A) (at level 70).

  Fact S_imsell_weak Γ Δ B : Forall (fun '(u,_) => U u) Γ -> Δ ⊢ B -> ‼Γ++Δ ⊢ B.
  Proof. 
    intros H1 H2; revert H1. 
    induction 1 as [ | (u,A) Γ H1 IH1 ]; simpl; auto.
    apply in_imsell_weak; auto. 
  Qed.

  Fact S_imsell_gen_weak u Γ Δ B : U u -> Δ ⊢ B -> map (fun A => ![u]A) Γ++Δ ⊢ B.
  Proof.
    intros H1 H2.
    replace (map (fun A => ![u]A) Γ) with (‼ (map (fun A => (u,A)) Γ)).
    + apply S_imsell_weak; auto.
      apply Forall_forall.
      intros ?; rewrite in_map_iff.
      intros (? & <- & ?); auto.
    + unfold imsell_lban; rewrite map_map; auto.
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

  Theorem S_imsell_extract Γ u A B : ![u]A ∊ Γ -> U u -> Γ ⊢ B <-> ![u]A::Γ ⊢ B.
  Proof.
    intros H1 H2; split.
    + apply in_imsell_weak; auto.
    + intros H3.
      apply In_perm in H1 as (Δ & H1).
      apply in_imsell_perm with (1 := H1).
      apply in_imsell_cntr; auto.
      apply in_imsell_perm with (2 := H3).
      apply perm_skip, Permutation_sym; auto.
  Qed.

(*
 
  Theorem S_imsell_weak_cntr' Σ Γ u A B : (u,A) ∊ Σ -> U u -> ‼Σ++Γ ⊢ B <-> ![u]A::‼Σ++Γ ⊢ B.
  Proof.
    intros H1 H2; apply S_imsell_extract; auto.
    apply in_app_iff; left.
    apply in_map_iff.
    exists (u,A); auto.
  Qed.

*)

  Section Trivial_Phase_semantics.

    (* We only consider the monoids nat^n *)

    Variables (n : nat) (s : nat -> vec nat n -> Prop).

    Notation "⦳" := vec_zero.
    Notation ø := vec_nil.

    Definition imsell_tps_mult (X Y : _ -> Prop) (x : vec _ n) := exists a b, x = vec_plus a b /\ X a /\ Y b.
    Definition imsell_tps_imp (X Y : _ -> Prop) (v : vec _ n) := forall x, X x -> Y (vec_plus x v).
 
    Infix "⊛" := imsell_tps_mult (at level 65, right associativity).
    Infix "-⊛" := imsell_tps_imp (at level 65, right associativity).

    Fact imsell_tps_imp_zero X Y : (X -⊛ Y) ⦳ <-> X ⊆ Y.
    Proof.
      split.
      + intros ? ? ?; rewrite <- vec_zero_plus, vec_add_comm; auto.
      + intros ? ?; rewrite vec_add_comm, vec_zero_plus; auto.
    Qed.

    Variable (K : bang -> vec nat n -> Prop).

    Hypothesis HK_antitone : forall p q, p ≤ q -> K q ⊆ K p.
    Hypothesis HK_unit0 : forall m, K m ⦳.
    Hypothesis HK_plus  : forall m, K m ⊛ K m ⊆ K m.
    Hypothesis HK_unit1 : forall u, U u -> forall x, K u x -> x = ⦳.

    Fact imsell_tps_mult_mono (X1 X2 Y1 Y2 : _ -> Prop) : 
              X1 ⊆ X2 -> Y1 ⊆ Y2 -> X1⊛Y1 ⊆ X2⊛Y2.
    Proof.
      intros H1 H2 x (y & z & H3 & H4 & H5); subst.
      exists y, z; auto.
    Qed.

    Fixpoint imsell_tps (A : imsell_form nat bang) x : Prop :=
      match A with
        | £ X   => s X x
        | ![m]A => ⟦A⟧ x /\ K m x
        | A⊸B   => (⟦A⟧-⊛⟦B⟧) x
      end
    where "⟦ A ⟧" := (imsell_tps A).

    Fact imsell_tps_bang_zero m A : ⟦![m]A⟧ ⦳ <-> ⟦A⟧ ⦳.
    Proof using HK_unit0. simpl; split; auto; tauto. Qed.

    Fact imsell_tps_bang_U u A : U u -> (forall v, ⟦![u]A⟧ v <-> v = ⦳) <-> ⟦A⟧ ⦳.
    Proof using HK_unit0 HK_unit1.
      intros Hu; split.
      + intros H; rewrite <- imsell_tps_bang_zero, H; auto.
      + intros H v; split; simpl.
        * intros (_ & H1); revert H1; eauto.
        * intros ->; auto.
    Qed.

    Reserved Notation "⟪ Γ ⟫" (at level 0, format "⟪ Γ ⟫").

    Fixpoint imsell_tps_list Γ :=
      match Γ with
        | nil  => eq ⦳
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
        * subst; apply vec_add_assoc.
        * split; auto.
        exists y, c; auto.
      + destruct Hx as (y & d & ? & (z & g & ? & ? & ?) & ?).
        exists z, (vec_plus g d); split.
        * subst; symmetry; apply vec_add_assoc.
        * split; auto.
          apply IH.
          exists g, d; auto.
    Qed.

    Fact imsell_tps_perm Γ Δ : Γ ~p Δ -> ⟪Γ⟫ ⊆ ⟪Δ⟫.
    Proof.
      induction 1 as [ | A Ga De H IH | A B Ga | ]; simpl; auto.
      + intros x (y & z & H1 & H2 & H3).
        exists y, z; repeat split; auto.
      + intros x (y & z & H1 & H2 & c & d & H3 & H4 & H5).
        exists c, (vec_plus y d); split.
        * subst; rewrite (vec_add_comm c), vec_add_assoc, (vec_add_comm c); auto.
        * split; auto.
          exists y, d; auto.
    Qed.

    Fact imsell_tps_list_zero Γ : (forall A, A ∊ Γ -> ⟦A⟧ ⦳) -> ⟪Γ⟫ ⦳.
    Proof.
      induction Γ as [ | A Γ IH ]; simpl; auto; intros H.
      exists ⦳, ⦳; msplit 2; auto; now rewrite vec_zero_plus.
    Qed.

    Definition imsell_sequent_tps Γ A := ⟪Γ⟫ -⊛ ⟦A⟧.

    Notation "'[<' Γ '|-' A '>]'" := (imsell_sequent_tps Γ A) (at level 0, format "[<  Γ  |-  A  >]").

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

    Fact imsell_sequent_tps_eq Γ A : [< Γ |- A >] ⦳ <-> ⟪Γ⟫ ⊆ ⟦A⟧.
    Proof.
      split.
      * intros H x Hx.
        rewrite <- vec_zero_plus, vec_add_comm.
        apply (H x); trivial.
      * intros H x Hx.
        rewrite vec_add_comm, vec_zero_plus; auto.
    Qed.

   Fact imsell_tps_lbang m Γ : m ≼ Γ -> ⟪‼Γ⟫ ⊆ K m.
    Proof using HK_unit0 HK_plus HK_antitone.
      induction Γ as [ | (v,A) Γ IH ]; simpl; intros H1 x.
      + intros <-; auto.
      + intros (y & z & -> & (G1 & G2) & G3).
        apply HK_plus; exists y, z; msplit 2; auto.
        * revert G2; apply HK_antitone; auto.
          apply (H1 (v,A)); auto.
        * revert G3; apply IH.
          intros (w,B) ?; apply (H1 (_,B)); auto.
    Qed.

    Theorem imsell_tps_sound Γ A : Γ ⊢ A -> [< Γ |- A >] ⦳.
    Proof using All.
      induction 1 as [ A 
                     | Γ Δ A H1 H2 IH2
                     | Γ Δ A B C H1 IH1 H2 IH2
                     | Γ A B H1 IH1
                     | Γ m A B H1 IH1
                     | Γ m A H1 H2 IH2
                     | Γ u A B H1 H2 IH2
                     | Γ u A B H1 H2 IH2
                     ]; unfold imsell_sequent_tps in * |- *.

      + intros x; simpl; intros (y & z & H1 & H2 & H3); subst; eq goal H2.
        f_equal; do 2 rewrite vec_add_comm, vec_zero_plus; auto.

      + revert IH2; apply imsell_perm_tps; auto.

      + intros x (y & z & H3 & H4 & H5); simpl.
        apply IH2.
        apply imsell_tps_app in H5 as (g & d & H5 & H6 & H7).
        simpl in H4; apply IH1, H4 in H6.
        exists (vec_plus y g), d; repeat split; auto.
        * subst; apply vec_add_assoc.
        * eq goal H6; f_equal; rew vec.

      + simpl; intros y Hy x Hx.
        rewrite vec_add_assoc.
        apply IH1.
        exists x, y; repeat split; auto.

      + intros x (y & z & H2 & H3 & H4).
        apply IH1; exists y, z; repeat split; auto.
        apply H3.

      + intros x Hx; split.
        * apply IH2; auto.
        * rew vec.
          revert Hx; apply imsell_tps_lbang; auto.

      + intros x (y & z & -> & H3 & H4); rew vec.
        apply proj2, HK_unit1 in H3; auto; subst.
        rewrite vec_add_comm.
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
