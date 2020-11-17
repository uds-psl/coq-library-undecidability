(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation Arith Lia.

From Undecidability.MinskyMachines
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
Local Infix "∊" := In (at level 70).

Local Reserved Notation "'⟦' A '⟧'" (at level 1, format "⟦ A ⟧").

Local Fact pair_plus x1 y1 x2 y2 : 
          vec_plus (x1##y1##vec_nil) (x2##y2##vec_nil) 
        = (x1+x2)##(y1+y2)##vec_nil.
Proof. reflexivity. Qed.

Local Tactic Notation "pair" "split" hyp(v) "as" ident(x) ident(y) :=
  vec split v with x; vec split v with y; vec nil v; clear v.

Local Tactic Notation "intro" "pair" "as" ident(x) ident (y) :=
  let v := fresh in intro v; pair split v as x y.

Local Notation ø := vec_zero.

Local Infix "≤" := (@IMSELL_le _) (at level 70).
Local Notation "u ≰ v" := (~ u ≤ v) (at level 70).
Local Notation U := (@IMSELL_U _).

Section ndmm2_imsell.

  Variable (sig : IMSELL_sig) (a b i : sig).

  Notation "∞" := i.

  Notation bang_le := (IMSELL_le sig).

  Hypothesis (Hai : a ≤ ∞) (Hbi : b ≤ ∞) (Hab : a ≰ b) (Hba : b ≰ a)
             (Ha : ~ U a) (Hb : ~ U b) (Hi : U ∞).

  Implicit Type u v w : sig.

  Local Definition bang_le_refl : forall u, u ≤ u := IMSELL_refl _.
  Local Definition bang_le_trans : forall u v w, u ≤ v -> v ≤ w -> u ≤ w := IMSELL_trans _.
  Local Definition bang_U_clos : forall u v, U u -> u ≤ v -> U v := IMSELL_clos _.

  Hint Resolve Hai Hbi Ha Hb Hi Hab Hba bang_le_refl bang_U_clos : core.

  Notation "£ A" := (@imsell_var _ _ A) (at level 1).
  Notation "‼ l" := (@imsell_lban nat sig l).

  Definition bool2form (x : bool) := if x then ![a]£0 else ![b]£1.
  Definition bool2bang_op (x : bool) := if x then b else a.

  Notation STOP := ndmm2_stop.
  Notation INC  := ndmm2_inc.
  Notation DEC  := ndmm2_dec.
  Notation ZERO := ndmm2_zero.

  Definition ndmm2_imsell_form c :=
    match c with
      | STOP p     => (£(2+p) ⊸ £(2+p)) ⊸ £(2+p) 
      | INC  x p q => (bool2form x ⊸ £(2+q)) ⊸ £(2+p)
      | DEC  x p q => bool2form x ⊸ £(2+q) ⊸ £(2+p)
      | ZERO x p q => (![bool2bang_op x]£(2+q)) ⊸ £(2+p)
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

  Notation "Γ ⊢ A" := (S_imsell bang_le U Γ A) (at level 70).

  Theorem ndmm2_imsell_weak c Σ x y p :
            In c Σ
        ->  ndmm2_imsell_ctx Σ x y ⊢ £p 
       <-> (![∞]⟬c⟭)::ndmm2_imsell_ctx Σ x y ++ nil ⊢ £p.
  Proof.
    intros H; rewrite <- app_nil_end.
    unfold ndmm2_imsell_ctx.
    rewrite !ndmm2_imsell_eq1.
    apply S_imsell_weak_cntr with (u := ∞) (A := ⟬c⟭); auto.
    apply in_map_iff; eauto.
  Qed.

  Notation "Σ // a ⊕ b ⊦ p" := (ndmm2_accept Σ a b p) (at level 70, no associativity).

  Theorem ndmm2_imsell_sound Σ x y p : Σ // x ⊕ y ⊦ p -> ndmm2_imsell_ctx Σ x y ⊢ £(2+p) .
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
      apply in_imsell_perm with (Γ := (![a]£0) ⊸ £(2+q) ⊸ £(2+p) :: (![a]£0 :: nil) ++ ndmm2_imsell_ctx Σ x y).
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
      apply in_imsell_perm with (Γ := (![b]£1) ⊸ £(2+q) ⊸ £(2+p) :: (![b]£1 :: nil) ++ ndmm2_imsell_ctx Σ x y).
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

  Let sem p (w : vec nat 2) := 
    let x := vec_head w in
    let y := vec_head (vec_tail w) 
    in match p with
      | 0 => x = 1 /\ y = 0
      | 1 => x = 0 /\ y = 1
      | S (S i) => Σ // x ⊕ y ⊦ i
    end.

  Local Fact sem_0 x y : sem 0 (x##y##vec_nil) <-> x = 1 /\ y = 0.
  Proof. simpl; tauto. Qed.
 
  Local Fact sem_1 x y : sem 1 (x##y##vec_nil) <-> x = 0 /\ y = 1.
  Proof. simpl; tauto. Qed.

  Local Fact sem_2 p x y : sem (2+p) (x##y##vec_nil) <-> Σ // x ⊕ y ⊦ p.
  Proof. simpl; tauto. Qed.

  Let K u (w : vec nat 2) := 
    let x := vec_head w in
    let y := vec_head (vec_tail w) 
    in (a ≤ u -> y = 0)
    /\ (b ≤ u -> x = 0)
    /\ (U u -> x = 0 /\ y = 0).

  Infix "⊛" := imsell_tps_mult (at level 65, right associativity).
  Infix "-⊛" := imsell_tps_imp (at level 65, right associativity).

  Notation "⟦ A ⟧" := (imsell_tps sem K A).
  Notation "⟪ Γ ⟫" := (imsell_tps_list sem K Γ).

  Local Fact HK1 u v : u ≤ v -> K v ⊆ K u.
  Proof.
    intros Huv; intro pair as x y.
    unfold K; simpl; intros (H1 & H2 & H3); msplit 2; intros H.
    + apply H1, bang_le_trans with (2 := Huv); auto.
    + apply H2, bang_le_trans with (2 := Huv); auto.
    + apply H3, bang_U_clos with (2 := Huv); auto.
  Qed.

  Local Fact HK2 : forall u, K u ø.
  Proof. intros; split; auto. Qed.

  Local Fact HK3 u : K u ⊛ K u ⊆ K u.
  Proof.
    intro pair as x y.
    intros (p & q & H); revert p q H.
    intro pair as x1 y1; intro pair as x2 y2; simpl.
    rewrite pair_plus; unfold K; simpl.
    intros (H1 & (H2 & H3 & H6) & H4 & H5 & H7).
    inversion H1; subst x y; clear H1.
    msplit 2; intros.
    + rewrite H2, H4; auto.
    + rewrite H3, H5; auto.
    + destruct H6; subst; auto.
  Qed.

  Local Fact HK4 u : U u -> forall x, K u x -> x = ø.
  Proof.
    intros Hu; intro pair as x y; unfold K; simpl.
    intros (_ & _ & H); destruct H; subst; auto.
  Qed. 

  Local Fact HKa x y : K a (x##y##vec_nil) <-> y = 0.
  Proof.
    split; unfold K; simpl.
    + intros []; auto.
    + intros ->; msplit 2; auto; intros; tauto.
  Qed.

  Local Fact HKb x y : K b (x##y##vec_nil) <-> x = 0.
  Proof.
    split; unfold K; simpl.
    + intros (? & ? & ?); auto.
    + intros ->; msplit 2; auto; tauto.
  Qed.

  Local Fact HKi : forall x, K ∞ x -> x = ø.
  Proof.
    intro pair as x y; unfold K; simpl.
    intros (H1 & H2 & ?); rewrite H1, H2; auto.
  Qed.

  Local Lemma sem_Σ c : c ∊ Σ -> ⟦ndmm2_imsell_form c⟧ ø.
  Proof.
    intros H.
    destruct c as [ p | [] p q | [] p q | [] p q ]; simpl; 
      apply imsell_tps_imp_zero; intro pair as x y; simpl; intros H1.
    + specialize (H1 ø); rewrite vec_zero_plus in H1.
      apply H1; constructor; auto.
    + constructor 2 with (1 := H).
      apply (H1 (1##0##vec_nil)).
      simpl; rewrite HKa; auto.
    + constructor 3 with (1 := H).
      apply (H1 (0##1##vec_nil)); auto.
      simpl; rewrite HKb; auto.
    + destruct H1 as ((-> & ->) & _); simpl.
      intro pair as x y; simpl; rewrite (plus_comm x), (plus_comm y).
      constructor 4 with q; auto.
    + destruct H1 as ((-> & ->) & _); simpl.
      intro pair as x y; simpl; rewrite (plus_comm x), (plus_comm y).
      constructor 5 with q; auto.
    + rewrite HKb in H1.
      destruct H1 as (H1 & ->).
      constructor 6 with q; auto.
    + rewrite HKa in H1.
      destruct H1 as (H1 & ->).
      constructor 7 with q; auto.
  Qed.

  Hint Resolve HK1 HK2 HK3 HK4 HKa HKb HKi sem_Σ : core.

  Local Fact sem_Σ_zero : ⟪map (fun c => ![∞](ndmm2_imsell_form c)) Σ⟫ ø.
  Proof.
    apply imsell_tps_list_zero.
    intros A; rewrite in_map_iff.
    intros (c & <- & Hc); simpl; auto. 
  Qed.

  Theorem ndmm2_imsell_complete p x y : 
           ndmm2_imsell_ctx Σ x y ⊢ £ (2+p)
        -> Σ // x ⊕ y ⊦ p.
  Proof.
    intros Hxy; apply imsell_tps_sound with (s := sem) (K := K) in Hxy; eauto.
    specialize (Hxy (x##y##vec_nil)).
    rewrite vec_plus_comm, vec_zero_plus in Hxy.
    apply Hxy; clear Hxy.
    unfold ndmm2_imsell_ctx.
    apply imsell_tps_app.
    exists ø, (x##y##vec_nil).
    rewrite vec_zero_plus; msplit 2; auto.
    + apply sem_Σ_zero; auto.
    + apply imsell_tps_app.
      exists (x##0##vec_nil), (0##y##vec_nil); msplit 2; auto.
      * rewrite pair_plus; f_equal; lia.
      * generalize x; clear x y; intros n. 
        induction n as [ | n IHn ]; simpl; auto.
        exists (1##0##vec_nil), (n##0##vec_nil); simpl; msplit 2; auto.
        rewrite HKa; auto.
      * generalize y; clear x y; intros n. 
        induction n as [ | n IHn ]; simpl; auto.
        exists (0##1##vec_nil), (0##n##vec_nil); simpl; msplit 2; auto.
        rewrite HKb; auto.
  Qed.

  Hint Resolve ndmm2_imsell_sound ndmm2_imsell_complete : core.

  Theorem ndmm2_imsell_correct p x y : Σ // x ⊕ y ⊦ p <-> ndmm2_imsell_ctx Σ x y ⊢ £ (2+p).
  Proof. split; auto. Qed.

End ndmm2_imsell.

Theorem conditional_reduction (S : IMSELL_sig) :
      (exists a b i : S, a ≤ i /\ b ≤ i /\ a ≰ b /\ b ≰ a /\ ~ U a /\ ~ U b /\ U i)
   -> @ndMM2_ACCEPT nat ⪯ @IMSELL_cf_PROVABILITY S.
Proof.
  intros (a & b & i & ?).
  apply reduces_dependent; exists.
  intros (Σ & u & x & y).
  exists (ndmm2_imsell_ctx _ a b i Σ x y, imsell_var _ (2+u)).
  apply ndmm2_imsell_correct; simpl; tauto.
Qed.

Theorem reduction (S : IMSELL_sig3) : @ndMM2_ACCEPT nat ⪯ @IMSELL_cf_PROVABILITY3 S.
Proof.
  destruct S as (S & HS).
  apply conditional_reduction, HS.
Qed.

