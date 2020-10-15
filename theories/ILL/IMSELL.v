(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation Arith Lia.

From Undecidability.Shared.Libs.DLW 
  Require Import utils pos vec.

Set Implicit Arguments.

(** * Intuionistic Multiplicative Linear Logic with several exponentials *)

Local Infix "~p" := (@Permutation _) (at level 70).

(** We consider  IMSELL:
    - the (!^*,-o) fragment with or without cut
*)

Notation eimsell_vars := nat.

Inductive eimsell_cmd : Set :=
  | eimsell_cmd_stop  : eimsell_vars -> eimsell_cmd
  | eimsell_cmd_inc  : bool -> eimsell_vars -> eimsell_vars -> eimsell_cmd
  | eimsell_cmd_dec  : bool -> eimsell_vars -> eimsell_vars -> eimsell_cmd
  | eimsell_cmd_zero : bool -> eimsell_vars -> eimsell_vars -> eimsell_cmd.

Notation LL_STOP := eimsell_cmd_stop.
Notation LL_INC  := eimsell_cmd_inc.
Notation LL_DEC  := eimsell_cmd_dec.
Notation LL_ZERO := eimsell_cmd_zero.

Definition eimsell_cmd_vars c := 
  match c with
    | LL_STOP p     => p::nil
    | LL_INC  _ p q => p::q::nil
    | LL_DEC  _ p q => p::q::nil
    | LL_ZERO _ p q => p::q::nil
  end.

(* Section GeIMSELL. *)

  Reserved Notation "Σ ; a ⊕ b ⊦ u" (at level 70, no associativity).

  Inductive G_eimsell (Σ : list eimsell_cmd) : nat -> nat -> eimsell_vars -> Prop :=
    | in_geimsell_stop  : forall p,         In (LL_STOP p) Σ         ->  Σ; 0 ⊕ 0 ⊦ p

    | in_geimsell_inc_1 : forall a b p q,   In (LL_INC true p q) Σ   ->  Σ; 1+a ⊕ b  ⊦ p
                                                                     ->  Σ;   a ⊕ b  ⊦ q
    | in_geimsell_inc_0 : forall a b p q,   In (LL_INC false p q) Σ  ->  Σ; a ⊕ 1+b  ⊦ p
                                                                     ->  Σ; a ⊕ b    ⊦ q

    | in_geimsell_dec_1 : forall a b p q,   In (LL_DEC true p q) Σ   ->  Σ;   a ⊕ b  ⊦ p
                                                                     ->  Σ; 1+a ⊕ b  ⊦ q
    | in_geimsell_dec_0 : forall a b p q,   In (LL_DEC false p q) Σ  ->  Σ; a ⊕   b  ⊦ p
                                                                     ->  Σ; a ⊕ 1+b  ⊦ q

    | in_geimsell_zero_1 : forall b p q,    In (LL_ZERO true p q) Σ  ->  Σ;   0 ⊕ b  ⊦ p
                                                                     ->  Σ;   0 ⊕ b  ⊦ q
    | in_geimsell_zero_0 : forall a p q,    In (LL_ZERO false p q) Σ ->  Σ;   a ⊕ 0  ⊦ p
                                                                     ->  Σ;   a ⊕ 0  ⊦ q

  where "Σ ; a ⊕ b ⊦ u" := (G_eimsell Σ a b u).

(* End GeIMSELL. *)

Notation imsell_vars := nat.

Section IMSELL.

  Notation "X ⊆ Y" := (forall a, X a -> Y a : Prop) (at level 70).

  Variable bang : Type.

  Inductive imsell_form : Type :=
    | imsell_var  : imsell_vars -> imsell_form
    | imsell_ban  : bang -> imsell_form -> imsell_form
    | imsell_imp  : imsell_form -> imsell_form -> imsell_form.

  (* Symbols for cut&paste ⟙   ⟘   𝝐  ﹠ ⊗  ⊕  ⊸  !   ‼  ∅  ⊢ *)

  Infix "⊸" := (imsell_imp) (at level 51, right associativity).

  Notation "'![' u ']' x" := (imsell_ban u x) (at level 52, format "![ u ] x").

  Notation "£" := imsell_var.

  Reserved Notation "‼ x" (at level 60, format "‼ x").
  Reserved Notation "l '⊢' x" (at level 70, no associativity).

  Fixpoint imsell_lban (l : list (bang * imsell_form)) : list imsell_form :=
    match l with 
      | nil      => nil
      | (u,A)::l => (![u] A)::‼l
    end
  where "'‼' l" := (imsell_lban l).

  Fact imsell_lban_map l : imsell_lban l = map (fun '(u,A) => ![u]A) l.
  Proof. induction l as [ | [] ]; simpl; f_equal; auto. Qed.

  Fact imsell_lban_perm Σ Γ : Σ ~p Γ -> ‼Σ ~p ‼Γ.
  Proof.
    induction 1 as [ | [] | [] [] | ]; simpl; auto.
    + constructor.
    + eapply perm_trans; eauto.
  Qed. 

  Variable (bang_le : bang -> bang -> Prop) (bang_U : bang -> Prop).

  Notation "u ≼ l" := (forall c, In c l -> bang_le u (fst c)) (at level 70). 

  Inductive S_imsell : _ -> _ -> Prop :=

    | in_imsell_ax     : forall A,                        A::nil ⊢ A

    | in_imsell_perm   : forall Γ Δ A,              Γ ~p Δ     ->   Γ ⊢ A 
                                           (*-----------------------------*)
                                        ->                 Δ ⊢ A

    | in_imsell_limp_l : forall Γ Δ A B C,         Γ ⊢ A      ->   B::Δ ⊢ C
                                           (*-----------------------------*)    
                                      ->           A ⊸ B::Γ++Δ ⊢ C

    | in_imsell_limp_r : forall Γ A B,                  A::Γ ⊢ B
                                           (*-----------------------------*)
                                        ->            Γ ⊢ A ⊸ B

    | in_imsell_bang_l : forall u Γ A B,                 A::Γ ⊢ B
                                           (*-----------------------------*)
                                      ->           ![u]A::Γ ⊢ B

    | in_imsell_bang_r : forall u Γ A,            u ≼ Γ    ->     ‼Γ ⊢ A
                                           (*-----------------------------*)
                                      ->              ‼Γ ⊢ ![u]A

    | in_imsell_weak : forall u Γ A B,          bang_U u    ->   Γ ⊢ B
                                           (*-----------------------------*)
                                      ->             ![u]A::Γ ⊢ B

    | in_imsell_cntr : forall u Γ A B,        bang_U u  -> ![u]A::![u]A::Γ ⊢ B
                                           (*-----------------------------*)
                                      ->               ![u]A::Γ ⊢ B

  where "Γ ⊢ A" := (S_imsell Γ A).

  Fact S_imsell_weak Γ Δ B : Forall (fun '(u,_) => bang_U u) Γ -> Δ ⊢ B -> ‼Γ++Δ ⊢ B.
  Proof. 
    intros H1 H2; revert H1. 
    induction 1 as [ | (u,A) Γ H1 IH1 ]; simpl; auto.
    apply in_imsell_weak; auto. 
  Qed.

  Fact S_imsell_cntr Γ Δ B : Forall (fun '(u,_) => bang_U u) Γ -> ‼Γ++‼Γ++Δ ⊢ B -> ‼Γ++Δ ⊢ B.
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

  Theorem S_imsell_weak_cntr Σ Γ u A B : In (u,A) Σ -> bang_U u -> ‼Σ++Γ ⊢ B <-> ![u]A::‼Σ++Γ ⊢ B.
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

  Variable (a b i : bang).

  Notation "∞" := i. 

  Hypothesis (Hai : bang_le a ∞) (Hbi : bang_le b ∞) (Hi : bang_U ∞) (Hbang : forall x, bang_le x x).

  Definition bool2form x := 
    match x with 
      | true  => ![a]£0
      | false => ![b]£1
    end.

  Definition bool2bang_op x :=
    match x with 
      | true  => b
      | false => a
    end.

  Definition eill_map_imsell c :=
  match c with
    | LL_STOP p     => (£p ⊸ £p) ⊸ £p 
    | LL_INC  x p q => (bool2form x ⊸ £p) ⊸ £q
    | LL_DEC  x p q => bool2form x ⊸ £p ⊸ £q
    | LL_ZERO x p q  => (![bool2bang_op x]£p) ⊸ £q
  end.

  Check repeat.

  Definition eimsell_imsell Σ x y := map (fun c => ![∞](eill_map_imsell c)) Σ ++ repeat (![a]£0) x ++ repeat (![b]£1) y. 

  Fact eill_map_imsell_eq Σ :  map (fun c => ![∞](eill_map_imsell c)) Σ
                            = ‼(map (fun c => (∞,eill_map_imsell c)) Σ).
  Proof. induction Σ; simpl; f_equal; auto. Qed.

  Fact eill_map_imsell_eq2 Σ x y :  eimsell_imsell Σ x y
                            = ‼(map (fun c => (∞,eill_map_imsell c)) Σ ++ repeat (a,£0) x ++ repeat (b,£1) y).
  Proof.
    unfold eimsell_imsell.
    rewrite imsell_lban_map, !map_app, map_map; f_equal.
    induction x; simpl; f_equal; auto.
    induction y; simpl; f_equal; auto.
  Qed.

  Theorem G_eimsell_weak c Σ x y u :
            In c Σ
        ->  eimsell_imsell Σ x y ⊢ £u 
       <-> ![∞](eill_map_imsell c)::eimsell_imsell Σ x y ++ nil ⊢ £u.
  Proof.
    intros H; rewrite <- app_nil_end.
    unfold eimsell_imsell.
    rewrite !eill_map_imsell_eq.
    apply S_imsell_weak_cntr with (u := ∞) (A := eill_map_imsell c); auto.
    apply in_map_iff; eauto.
  Qed.

  Theorem G_eimsell_sound Σ x y u : Σ ; x ⊕ y ⊦ u -> eimsell_imsell Σ x y ⊢ £u .
  Proof.
    induction 1 as [ p H1 
                   | x y p q H1 H2 IH2 | x y p q H1 H2 IH2 
                   | x y p q H1 H2 IH2 | x y p q H1 H2 IH2
                   | y p q H1 H2 IH2 | x p q H1 H2 IH2 ].
    + apply G_eimsell_weak with (1 := H1); simpl.
      apply in_imsell_bang_l, in_imsell_limp_l.
      * apply in_imsell_limp_r.
        apply in_imsell_perm with (1 := Permutation_sym (Permutation_cons_append _ _)).
        unfold eimsell_imsell.
        rewrite eill_map_imsell_eq; simpl; rewrite <- app_nil_end.
        apply S_imsell_weak.
        - apply Forall_forall; intros ?; rewrite in_map_iff.
          intros (? & <- & ?); auto.
        - apply in_imsell_ax.
      * apply in_imsell_ax.

    + apply G_eimsell_weak with (1 := H1); simpl.
      apply in_imsell_bang_l, in_imsell_limp_l.
      * apply in_imsell_limp_r.
        revert IH2; apply in_imsell_perm.
        unfold eimsell_imsell.
        apply Permutation_sym, perm_trans with (1 := Permutation_cons_append _ _).
        rewrite !app_ass; apply Permutation_app; auto.
        simpl; apply Permutation_sym, perm_trans with (1 := Permutation_cons_append _ _).
        now rewrite app_ass.
      * apply in_imsell_ax.
    + apply G_eimsell_weak with (1 := H1); simpl.
      apply in_imsell_bang_l, in_imsell_limp_l.
      * apply in_imsell_limp_r.
        revert IH2; apply in_imsell_perm.
        unfold eimsell_imsell.
        apply Permutation_sym, perm_trans with (1 := Permutation_cons_append _ _).
        rewrite !app_ass; repeat apply Permutation_app; auto.
        simpl; apply Permutation_sym, perm_trans with (1 := Permutation_cons_append _ _); auto.
      * apply in_imsell_ax.

    + apply G_eimsell_weak with (1 := H1); simpl.
      apply in_imsell_bang_l.
      apply in_imsell_perm with (Γ := (![a]£0) ⊸ £p ⊸ £q :: (![a]£0 :: nil) ++ eimsell_imsell Σ x y).
      * apply perm_skip; rewrite <- app_nil_end.
        simpl; apply perm_trans with (1 := Permutation_cons_append _ _).
        unfold eimsell_imsell; simpl; rewrite !app_ass.
        apply Permutation_app; auto.
        apply Permutation_sym, perm_trans with (1 := Permutation_cons_append _ _).
        now rewrite !app_ass.
      * apply in_imsell_limp_l.
        - apply in_imsell_ax.
        - rewrite app_nil_end with (l := eimsell_imsell Σ x y).
          apply in_imsell_limp_l; auto.
          apply in_imsell_ax.

    + apply G_eimsell_weak with (1 := H1); simpl.
      apply in_imsell_bang_l.
      apply in_imsell_perm with (Γ := (![b]£1) ⊸ £p ⊸ £q :: (![b]£1 :: nil) ++ eimsell_imsell Σ x y).
      * apply perm_skip; rewrite <- app_nil_end.
        simpl; apply perm_trans with (1 := Permutation_cons_append _ _).
        unfold eimsell_imsell; simpl; rewrite !app_ass.
        repeat apply Permutation_app; auto.
        apply Permutation_sym, perm_trans with (1 := Permutation_cons_append _ _); auto.
      * apply in_imsell_limp_l.
        - apply in_imsell_ax.
        - rewrite app_nil_end with (l := eimsell_imsell Σ x y).
          apply in_imsell_limp_l; auto.
          apply in_imsell_ax.

    + apply G_eimsell_weak with (1 := H1); simpl.
      apply in_imsell_bang_l.
      apply in_imsell_limp_l.
      * rewrite eill_map_imsell_eq2.
        apply in_imsell_bang_r.
        - intros z; simpl; rewrite !in_app_iff, in_map_iff.
          intros [ (c & <- & Hc) | H ]; simpl; auto.
          apply repeat_spec in H as ->; simpl; auto.
        - now rewrite eill_map_imsell_eq2 in IH2.
      * apply in_imsell_ax.

    + apply G_eimsell_weak with (1 := H1); simpl.
      apply in_imsell_bang_l.
      apply in_imsell_limp_l.
      * rewrite eill_map_imsell_eq2.
        apply in_imsell_bang_r.
        - intros z; simpl; rewrite !in_app_iff, in_map_iff.
          intros [ (c & <- & Hc) | [ H | [] ] ]; simpl; auto.
          apply repeat_spec in H as ->; simpl; auto.
        - now rewrite eill_map_imsell_eq2 in IH2.
      * apply in_imsell_ax.
  Qed.

  Variables (n : nat) (s : imsell_vars -> vec nat n -> Prop)
            (K : bang -> vec nat n -> Prop).

  Hypothesis HK_le : forall u v, bang_le u v -> K v ⊆ K u.

  Notation ø := vec_zero.

  Reserved Notation "'⟦' A '⟧'" (at level 65).

  Definition imsell_tps_imp (X Y : _ -> Prop) (v : vec _ n) := forall x, X x -> Y (vec_plus x v).
  Definition imsell_tps_mult (X Y : _ -> Prop) (x : vec _ n) := exists a b, x = vec_plus a b /\ X a /\ Y b. 
  
  Infix "**" := imsell_tps_mult (at level 65, right associativity).
  Infix "-*" := imsell_tps_imp (at level 65, right associativity).

  Hypothesis HK_unit0 : forall u, K u ø.
  Hypothesis HK_plus  : forall u, (K u)**(K u) ⊆ K u.
  Hypothesis HK_unit1 : forall u, bang_U u -> forall x, K u x -> x = ø.

  Fact imsell_tps_mult_mono (X1 X2 Y1 Y2 : _ -> Prop) : 
             X1 ⊆ X2 -> Y1 ⊆ Y2 -> X1**Y1 ⊆ X2**Y2.
  Proof.
    intros H1 H2 x (y & z & H3 & H4 & H5); subst.
    exists y, z; auto.
  Qed.

  Fixpoint imsell_tps A x : Prop :=
    match A with
      | £ X     => s X x
      | ![u]A   => ⟦A⟧ x /\ K u x
      | A ⊸ B   => (⟦A⟧ -* ⟦B⟧) x
    end
  where "⟦ A ⟧" := (imsell_tps A).

  Reserved Notation "⟪ Γ ⟫" (at level 0, format "⟪ Γ ⟫").

  Fixpoint ill_tps_list Γ :=
    match Γ with
      | nil  => eq vec_zero
      | A::Γ => ⟦A⟧ ** ⟪Γ⟫
    end
  where "⟪ Γ ⟫" := (ill_tps_list Γ).

  Fact imsell_tps_app Γ Δ x : ⟪Γ++Δ⟫ x <-> (⟪Γ⟫**⟪Δ⟫) x.
  Proof.
    revert Γ Δ x; intros Ga De.
    induction Ga as [ | A Ga IH ]; intros x; simpl; split; intros Hx.
    + exists vec_zero, x; simpl; rew vec.
    + destruct Hx as (? & ? & H1 & H2 & H3); subst; auto; rewrite vec_zero_plus; auto.
    + destruct Hx as (y & z & H1 & H2 & H3).
      apply IH in H3.
      destruct H3 as (c & d & H4 & H5 & H6).
      exists (vec_plus y c), d; split.
      * subst; apply vec_plus_assoc.
      * split; auto.
        exists y, c; auto.
    + destruct Hx as (y & d & H1 & H2 & H3).
      destruct H2 as (z & g & H2 & H4 & H5).
      exists z, (vec_plus g d); split.
      * subst; symmetry; apply vec_plus_assoc.
      * split; auto.
        apply IH.
        exists g, d; auto.
  Qed.

  Fact imsell_tps_lbang u Γ : u ≼ Γ -> ⟪‼Γ⟫ ⊆ K u.
  Proof.
    rewrite <- Forall_forall.
    induction 1 as [ | (v,A) Γ H1 H2 IH2 ]; intros x; simpl.
    + intros <-; auto.
    + intros (y & z & -> & (G1 & G2) & G3).
      apply HK_plus; exists y, z; msplit 2; auto.
      revert G2; apply HK_le; auto.
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
  
  Definition imsell_sequent_tps Γ A := ⟪Γ⟫ -* ⟦A⟧.

  Notation "'[<' Γ '|-' A '>]'" := (imsell_sequent_tps Γ A).

  Fact imsell_sequent_tps_mono Γ A B :
         ⟦A⟧ ⊆ ⟦B⟧ -> [< Γ |- A >] ⊆ [< Γ |- B >].
  Proof.
    intros H x; simpl; unfold imsell_sequent_tps.
    intros H1 a H2.
    apply H, H1; auto.
  Qed.

  Fact imsell_perm_tps Γ Δ : Γ ~p Δ -> forall A, [< Γ |- A >] ⊆ [< Δ |- A >].
  Proof.
    intros H1 B x; unfold imsell_sequent_tps.
    intros H2 a H3.
    apply H2; revert H3. 
    apply imsell_tps_perm, Permutation_sym; auto.
  Qed.

  Fact imsell_sequent_tps_eq Γ A : [< Γ |- A >] vec_zero <-> ⟪Γ⟫ ⊆ ⟦A⟧.
  Proof.
    split.
    * intros H x Hx.
      rewrite <- vec_zero_plus, vec_plus_comm.
      apply (H x); trivial.
    * intros H x Hx.
      rewrite vec_plus_comm, vec_zero_plus; auto.
  Qed.

  Theorem imsell_tps_sound Γ A : Γ ⊢ A -> [< Γ |- A >] vec_zero.
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

    + simpl; intros y Hy a Ha.
      rewrite vec_plus_assoc.
      apply IH1.
      exists a, y; repeat split; auto; lia.

    + intros x (a & g & H2 & H3 & H4).
      apply IH1; exists a, g; repeat split; auto.
      apply H3.

    + intros x Hx; split.
      * apply IH2; auto.
      * rew vec.
        revert Hx; apply imsell_tps_lbang; auto. 

    + intros x (a & g & -> & H3 & H4); rew vec.
      apply proj2, HK_unit1 in H3; auto; subst.
      rewrite vec_plus_comm.
      now apply IH2.
  
    + intros x (a & g & G2 & G3 & G4).
      apply IH2.
      exists a, g.
      repeat (split; auto).
      exists a, g.
      repeat (split; auto).
      apply proj2, HK_unit1 in G3; auto.
      subst; rew vec; auto.
  Qed.

End IMSELL.
