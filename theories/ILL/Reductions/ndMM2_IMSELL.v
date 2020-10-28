(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation Arith Lia.

From Undecidability.CounterMachines
  Require Import ndMM2.

From Undecidability.ILL 
  Require Import IMSELL imsell.

From Undecidability.Shared.Libs.DLW 
  Require Import utils pos vec.

From Undecidability.Synthetic
  Require Import Definitions ReducibilityFacts.

Set Implicit Arguments.

Local Infix "~p" := (@Permutation _) (at level 70).
Local Notation "X ⊆ Y" := (forall a, X a -> Y a : Prop) (at level 70).

Local Reserved Notation "'⟦' A '⟧'" (at level 1, format "⟦ A ⟧").

Local Fact pair_plus x1 y1 x2 y2 : 
          vec_plus (x1##y1##vec_nil) (x2##y2##vec_nil) 
        = (x1+x2)##(y1+y2)##vec_nil.
Proof. reflexivity. Qed.

Local Tactic Notation "pair" "split" hyp(v) "as" ident(x) ident(y) :=
  vec split v with x; vec split v with y; vec nil v; clear v.

Local Tactic Notation "intro" "pair" "as" ident(x) ident (y) :=
  let v := fresh in intro v; pair split v as x y.

Section ndmm2_imsell.

  Notation ø := vec_zero.

  Let bang := option bool.

  Let a := Some true.
  Let b := Some false.
  Let i : bang := None.

  Notation "∞" := i. 

  Let bang_le (u v : bang) := 
    match v with
      | None   => True
      | Some _ => u = v
    end.

  Let bang_U := eq ∞.

  Local Definition Hai : bang_le a ∞ := I.
  Local Definition Hbi : bang_le b ∞ := I. 
  Local Definition Hi : bang_U ∞ := eq_refl.
  Local Fact Hbang : forall x, bang_le x x.
  Proof. intros [ [] | ]; simpl; auto. Qed. 

  Hint Resolve Hai Hbi Hi Hbang : core.

  Definition imsell3 : IMSELL_sig.
  Proof.
    exists bang bang_le bang_U; trivial.
    + do 3 intros [[]|]; now simpl.
    + do 2 intros [[]|]; now simpl.
  Defined.

  Infix "⊸" := (@imsell_imp _ _).
  Notation "![ m ] x" := (@imsell_ban _ _ m x).
  Notation "£ A" := (@imsell_var _ _ A) (at level 1).
  Notation "‼ l" := (@imsell_lban nat bang l).

  Definition bool2form (x : bool) := if x then ![a]£0 else ![b]£1.
  Definition bool2bang_op (x : bool) := if x then b else a.

  Notation STOP := ndmm2_stop.
  Notation INC  := ndmm2_inc.
  Notation DEC  := ndmm2_dec.
  Notation ZERO := ndmm2_zero.

  Definition ndmm2_imsell_form c :=
    match c with
      | STOP p     => (£(2+p) ⊸ £(2+p)) ⊸ £(2+p) 
      | INC  x p q => (bool2form x ⊸ £(2+p)) ⊸ £(2+q)
      | DEC  x p q => bool2form x ⊸ £(2+p) ⊸ £(2+q)
      | ZERO x p q => (![bool2bang_op x]£(2+p)) ⊸ £(2+q)
    end.

  Notation "⟬ c ⟭" := (ndmm2_imsell_form c) (at level 65, format "⟬ c ⟭").

  Definition ndmm2_imsell_ctx Σ x y := map (fun c => ![∞]⟬c⟭) Σ
                                    ++ repeat (![a]£0) x 
                                    ++ repeat (![b]£1) y. 

  Fact ndmm2_imsell_eq1 Σ : map (fun c => ![∞]⟬c⟭) Σ = ‼(map (fun c => (∞,⟬c⟭)) Σ).
  Proof. unfold imsell_lban; rewrite map_map; auto. Qed.

  Fact ndmm2_imsell_eq2 Σ x y : 
          ndmm2_imsell_ctx Σ x y
        = ‼(map (fun c => (∞,⟬c⟭)) Σ ++ repeat (a,£0) x ++ repeat (b,£1) y).
  Proof.
    unfold ndmm2_imsell_ctx.
    rewrite ndmm2_imsell_eq1.
    unfold imsell_lban; rewrite !map_app, !map_map; f_equal.
    induction x; simpl; f_equal; auto.
    induction y; simpl; f_equal; auto.
  Qed.

  Notation "Γ ⊢ A" := (S_imsell bang_le bang_U Γ A) (at level 70).

  Theorem ndmm2_imsell_weak c Σ x y u :
            In c Σ
        ->  ndmm2_imsell_ctx Σ x y ⊢ £u 
       <-> (![∞]⟬c⟭)::ndmm2_imsell_ctx Σ x y ++ nil ⊢ £u.
  Proof.
    intros H; rewrite <- app_nil_end.
    unfold ndmm2_imsell_ctx.
    rewrite !ndmm2_imsell_eq1.
    apply S_imsell_weak_cntr with (u := ∞) (A := ⟬c⟭); auto.
    apply in_map_iff; eauto.
  Qed.

  Notation "Σ ; a ⊕ b ⊦ u" := (ndmm2_accept Σ a b u) (at level 70, no associativity).

  Theorem ndmm2_imsell_sound Σ x y u : Σ ; x ⊕ y ⊦ u -> ndmm2_imsell_ctx Σ x y ⊢ £(2+u) .
  Proof.
    induction 1 as [ p H1 
                   | x y p q H1 H2 IH2 | x y p q H1 H2 IH2 
                   | x y p q H1 H2 IH2 | x y p q H1 H2 IH2
                   | y p q H1 H2 IH2 | x p q H1 H2 IH2 ].
    + apply ndmm2_imsell_weak with (1 := H1); simpl.
      apply in_imsell_bang_l, in_imsell_limp_l.
      * apply in_imsell_limp_r.
        apply in_imsell_perm with (1 := Permutation_sym (Permutation_cons_append _ _)).
        unfold ndmm2_imsell_ctx.
        rewrite ndmm2_imsell_eq1; simpl; rewrite <- app_nil_end.
        apply S_imsell_weak.
        - apply Forall_forall; intros x Hx.
          apply in_map_iff in Hx; revert Hx.
          intros (? & <- & ?); auto.
        - apply in_imsell_ax.
      * apply in_imsell_ax.

    + apply ndmm2_imsell_weak with (1 := H1); simpl.
      apply in_imsell_bang_l, in_imsell_limp_l.
      * apply in_imsell_limp_r.
        revert IH2; apply in_imsell_perm.
        unfold ndmm2_imsell_ctx.
        apply Permutation_sym, perm_trans with (1 := Permutation_cons_append _ _).
        rewrite !app_ass; apply Permutation_app; auto.
        simpl; apply Permutation_sym, perm_trans with (1 := Permutation_cons_append _ _).
        now rewrite app_ass.
      * apply in_imsell_ax.

    + apply ndmm2_imsell_weak with (1 := H1); simpl.
      apply in_imsell_bang_l, in_imsell_limp_l.
      * apply in_imsell_limp_r.
        revert IH2; apply in_imsell_perm.
        unfold ndmm2_imsell_ctx.
        apply Permutation_sym, perm_trans with (1 := Permutation_cons_append _ _).
        rewrite !app_ass; repeat apply Permutation_app; auto.
        simpl; apply Permutation_sym, perm_trans with (1 := Permutation_cons_append _ _); auto.
      * apply in_imsell_ax.

    + apply ndmm2_imsell_weak with (1 := H1); simpl.
      apply in_imsell_bang_l.
      apply in_imsell_perm with (Γ := (![a]£0) ⊸ £(2+p) ⊸ £(2+q) :: (![a]£0 :: nil) ++ ndmm2_imsell_ctx Σ x y).
      * apply perm_skip; rewrite <- app_nil_end.
        simpl; apply perm_trans with (1 := Permutation_cons_append _ _).
        unfold ndmm2_imsell_ctx; simpl; rewrite !app_ass.
        apply Permutation_app; auto.
        apply Permutation_sym, perm_trans with (1 := Permutation_cons_append _ _).
        now rewrite !app_ass.
      * apply in_imsell_limp_l.
        - apply in_imsell_ax.
        - rewrite app_nil_end with (l := ndmm2_imsell_ctx Σ x y).
          apply in_imsell_limp_l; auto.
          apply in_imsell_ax.

    + apply ndmm2_imsell_weak with (1 := H1); simpl.
      apply in_imsell_bang_l.
      apply in_imsell_perm with (Γ := (![b]£1) ⊸ £(2+p) ⊸ £(2+q) :: (![b]£1 :: nil) ++ ndmm2_imsell_ctx Σ x y).
      * apply perm_skip; rewrite <- app_nil_end.
        simpl; apply perm_trans with (1 := Permutation_cons_append _ _).
        unfold ndmm2_imsell_ctx; simpl; rewrite !app_ass.
        repeat apply Permutation_app; auto.
        apply Permutation_sym, perm_trans with (1 := Permutation_cons_append _ _); auto.
      * apply in_imsell_limp_l.
        - apply in_imsell_ax.
        - rewrite app_nil_end with (l := ndmm2_imsell_ctx Σ x y).
          apply in_imsell_limp_l; auto.
          apply in_imsell_ax.

    + apply ndmm2_imsell_weak with (1 := H1); simpl.
      apply in_imsell_bang_l, in_imsell_limp_l.
      * rewrite ndmm2_imsell_eq2.
        apply in_imsell_bang_r.
        - intros (v,A) HvA. 
          apply in_app_iff in HvA as [ HvA | HvA ].
          ++ apply in_map_iff in HvA as (c & H & Hc); simpl; auto.
             inversion H; subst; auto.
          ++ apply in_app_iff in HvA as [ [] | HvA ].
             apply repeat_spec in HvA; inversion HvA; subst; simpl; auto.
        - now rewrite ndmm2_imsell_eq2 in IH2.
      * apply in_imsell_ax.

    + apply ndmm2_imsell_weak with (1 := H1); simpl.
      apply in_imsell_bang_l, in_imsell_limp_l.
      * rewrite ndmm2_imsell_eq2.
        apply in_imsell_bang_r.
        - intros (v,A) HvA. 
          apply in_app_iff in HvA as [ HvA | HvA ].
          ++ apply in_map_iff in HvA as (c & H & Hc); simpl; auto.
             inversion H; subst; auto.
          ++ apply in_app_iff in HvA as [ HvA | [] ].
             apply repeat_spec in HvA; inversion HvA; subst; simpl; auto.
        - now rewrite ndmm2_imsell_eq2 in IH2.
      * apply in_imsell_ax.
  Qed.

  Variable Σ : list (ndmm2_instr nat).

  Let sem u (v : vec nat 2) := 
    let x := vec_head v in
    let y := vec_head (vec_tail v) 
    in match u with
      | 0 => x = 1 /\ y = 0
      | 1 => x = 0 /\ y = 1
      | S (S i) => Σ ; x ⊕ y ⊦ i
    end.

  Let K (u : bang) (v : vec nat 2) := 
    let x := vec_head v in
    let y := vec_head (vec_tail v) 
    in match u with 
      | None       => x = 0 /\ y = 0
      | Some true  => y = 0
      | Some false => x = 0
    end.

  Notation "⟦ A ⟧" := (imsell_tps sem K A).
  Notation "⟪ Γ ⟫" := (imsell_tps_list sem K Γ).

  Local Fact sem_0 x y : sem 0 (x##y##vec_nil) <-> x = 1 /\ y = 0.
  Proof. simpl; tauto. Qed.
 
  Local Fact sem_1 x y : sem 1 (x##y##vec_nil) <-> x = 0 /\ y = 1.
  Proof. simpl; tauto. Qed.

  Local Fact sem_2 u x y : sem (2+u) (x##y##vec_nil) <-> Σ ; x ⊕ y ⊦ u.
  Proof. simpl; tauto. Qed.

  Local Fact HK1 u v : bang_le u v -> K v ⊆ K u.
  Proof.
    intros Huv; intro pair as x y.
    revert u v Huv; intros [[]|] [[]|]; simpl; try discriminate; tauto.
  Qed.

  Local Fact HK2 : forall u, K u ø.
  Proof. intros [[]|]; simpl; auto. Qed.

  Local Fact HK3 u : forall w, imsell_tps_mult (K u) (K u) w -> K u w.
  Proof.
    intro pair as x y.
    revert u; intros [[]|]; simpl; 
      intros (u & v & H1 & H2 & H3);
      simpl in H2, H3; revert H1 H2 H3;
      pair split u as x1 y1; pair split v as x2 y2; simpl;
      rewrite pair_plus; inversion 1; lia.
  Qed.

  Local Fact HK4 u : bang_U u -> forall w, K u w -> w = ø.
  Proof. 
    revert u; intros [[]|]; simpl; try discriminate.
    intros _; intro pair as x y; simpl.
    intros (-> & ->); auto.
  Qed.

  Local Lemma sem_Σ c : In c Σ -> ⟦ndmm2_imsell_form c⟧ ø.
  Proof.
    intros H.
    destruct c as [ p | [] p q | [] p q | [] p q ]; simpl; 
      apply imsell_tps_imp_zero; intro pair as x y; simpl; intros H1.
    + specialize (H1 ø); rewrite vec_zero_plus in H1.
      apply H1; constructor; auto.
    + constructor 2 with (1 := H).
      apply (H1 (1##0##vec_nil)); auto.
    + constructor 3 with (1 := H).
      apply (H1 (0##1##vec_nil)); auto.
    + destruct H1 as ((-> & ->) & _); simpl.
      intro pair as x y; simpl; rewrite (plus_comm x), (plus_comm y).
      constructor 4 with p; auto.
    + destruct H1 as ((-> & ->) & _); simpl.
      intro pair as x y; simpl; rewrite (plus_comm x), (plus_comm y).
      constructor 5 with p; auto.
    + destruct H1 as (H1 & ->).
      constructor 6 with p; auto.
    + destruct H1 as (H1 & ->).
      constructor 7 with p; auto.
  Qed.

  Hint Resolve HK1 HK2 HK3 HK4 sem_Σ : core.

  Local Fact sem_Σ_zero : ⟪map (fun c => ![∞](ndmm2_imsell_form c)) Σ⟫ ø.
  Proof.
    apply imsell_tps_list_zero.
    intros A; rewrite in_map_iff.
    intros (c & <- & Hc); simpl; auto. 
  Qed.

  Theorem ndmm2_imsell_complete u x y : 
           ndmm2_imsell_ctx Σ x y ⊢ £ (2+u)
        -> Σ ; x ⊕ y ⊦ u.
  Proof.
    intros Hxy; apply imsell_tps_sound with (s := sem) (K := K) in Hxy; eauto.
    specialize (Hxy (x##y##vec_nil)).
    rewrite vec_plus_comm, vec_zero_plus in Hxy.
    apply Hxy.
    unfold ndmm2_imsell_ctx.
    apply imsell_tps_app.
    exists ø, (x##y##vec_nil).
    rewrite vec_zero_plus; msplit 2; auto.
    + apply sem_Σ_zero; auto.
    + apply imsell_tps_app.
      clear Hxy.
      exists (x##0##vec_nil), (0##y##vec_nil); msplit 2; auto.
      * rewrite pair_plus; f_equal; lia.
      * generalize x; clear x y; intros n. 
        induction n as [ | n IHn ]; simpl; auto.
        exists (1##0##vec_nil), (n##0##vec_nil); auto.
      * generalize y; clear x y; intros n. 
        induction n as [ | n IHn ]; simpl; auto.
        exists (0##1##vec_nil), (0##n##vec_nil); auto.
  Qed.

  Hint Resolve ndmm2_imsell_sound ndmm2_imsell_complete : core.

  Theorem ndmm2_imsell_correct u x y : Σ ; x ⊕ y ⊦ u <-> ndmm2_imsell_ctx Σ x y ⊢ £ (2+u).
  Proof. split; auto. Qed.

End ndmm2_imsell.

Theorem reduction : @ndMM2_ACCEPT nat ⪯ @IMSELL_cf_provable imsell3.
Proof.
  apply reduces_dependent; exists.
  intros (Σ & u & x & y).
  exists (ndmm2_imsell_ctx Σ x y, imsell_var _ (2+u)).
  apply ndmm2_imsell_correct.
Qed.
