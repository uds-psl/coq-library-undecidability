(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Dominik Kirst              [+]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [+] Affiliation U. Sarrbrucken *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* This was implemented by DLW following the ideas of 
   the reduction BPCP -> fin SAT described in a draft by DK. *)

Require Import List Arith Bool Lia.

From Undecidability.PCP Require Import PCP Util.PCP_facts.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import wf_finite.

From Undecidability.FOL.TRAKHTENBROT
  Require Import notations utils bpcp fol_ops fo_sig fo_terms fo_logic fo_sat.

Import fol_notations.

Set Implicit Arguments.

(* * Reduction from BPCP to specialized FSAT *)

Local Notation ø := vec_nil.

Section BPCP_FIN_DEC_EQ_SAT.

  Variable lc : list (list bool * list bool).  (* A BPCP instance *)

  Notation 𝕋 := (fol_term Σbpcp).
  Notation 𝔽 := (fol_form Σbpcp).

  Notation e := (@in_fot _ (ar_syms Σbpcp) Σbpcp_unit ø).
  Notation "∗" := (@in_fot _ (ar_syms Σbpcp) Σbpcp_undef ø).
  Notation "b ⤚ x" := (@in_fot _ (ar_syms Σbpcp) (Σbpcp_bool b) (x##ø)) (at level 51, right associativity, format "b ⤚ x").

  Notation "¬ x" := (x ⤑ ⊥) (at level 59).
  Notation "x ⧓ y" := (@fol_atom Σbpcp Σbpcp_hand (x##y##ø)) (at level 58).
  Notation "x ≺ y" := (@fol_atom Σbpcp Σbpcp_ssfx (x##y##ø)) (at level 58).
  Notation "x ≡ y" := (@fol_atom Σbpcp Σbpcp_eq (x##y##ø)) (at level 58).
  Notation "x ≢ y" := (x ≡ y ⤑ ⊥) (at level 58).

  Local Definition lb_app l t := fold_right (fun b x => b ⤚ x) t l.

  Notation "l ⤜ x" := (lb_app l x) (at level 51, right associativity, format "l ⤜ x").

  Local Fact lb_app_app l m t : (l++m)⤜t = l⤜m⤜t.
  Proof. apply fold_right_app. Qed.
 
  Local Fact fot_vars_lb_app l t : fo_term_vars (l⤜t) = fo_term_vars t.
  Proof.
    induction l as [ | x l IHl ]; simpl; rew fot; auto.
    simpl; rewrite <- app_nil_end; auto.
  Qed.

  Notation lb2term := (fun l => l⤜e).

  Local Definition phi_P      := ∀∀ £1 ⧓ £0 ⤑ £1 ≢ ∗ ⟑ £0 ≢ ∗.

  Local Definition lt_irrefl  := ∀ ¬ £0 ≺ £0.
  Local Definition lt_trans   := ∀∀∀ £2 ≺ £1 ⤑ £1 ≺ £0 ⤑ £2 ≺ £0.

  Local Definition phi_lt     := lt_irrefl ⟑ lt_trans.

  Local Definition eq_neq b   := ∀ b⤚£0 ≢ e.
  Local Definition eq_inj b   := ∀∀ b⤚£1 ≢ ∗ ⤑ b⤚£1 ≡ b⤚ £0⤑ £1 ≡ £0.
  Local Definition eq_real    := ∀∀ true⤚£1 ≡ false⤚£0 ⤑ true⤚£1 ≡ ∗ ⟑ false⤚£0 ≡ ∗.
  Local Definition eq_undef b := b⤚∗ ≡ ∗.

  Local Definition phi_eq := 
            eq_neq true   ⟑ eq_neq false 
          ⟑ eq_inj true   ⟑ eq_inj false 
          ⟑ eq_undef true ⟑ eq_undef false
          ⟑ eq_real.

  Local Definition lt_pair u v x y := 
            (u ≺ x ⟑ v ≡ y) 
          ⟇ (v ≺ y ⟑ u ≡ x) 
          ⟇ (u ≺ x ⟑ v ≺ y).

  Local Definition lt_simul '(s,t) := 
            £1 ≡ s⤜e 
          ⟑ £0 ≡ t⤜e
       ⟇ ∃∃ £1 ⧓ £0 
          ⟑ £3 ≡ s⤜£1 
          ⟑ £2 ≡ t⤜£0 
          ⟑ lt_pair (£1) (£0) (£3) (£2).

  Local Definition phi_simul := ∀∀ £1 ⧓ £0 ⤑ fol_ldisj (map lt_simul lc).

  Definition Σbpcp_encode := phi_P ⟑ phi_lt ⟑ phi_eq ⟑ phi_simul ⟑ ∃ £0 ⧓ £0.

  Section soundness.

    (* We assume a solution to pcp_hand and we build a finite and decidable model
        of Σbpcp_encode from it *)

    Variable (l : list bool) (Hl : lc ⊳ l∕l). 

    Let n := length l.
    Let X := option { m : list bool | length m < S n }.

    Fact Σbpcp_model_finite : finite_t X.
    Proof. apply finite_t_option, finite_t_list, finite_t_bool. Qed.

    Hint Resolve Σbpcp_model_finite : core.

    Definition Σbpcp_model : fo_model Σbpcp X.
    Proof using lc.
      exists.
      + intros []; simpl.
        * intros v.
          case_eq (vec_head v).
          - intros (m & Hm) H.
            destruct (le_lt_dec n (length m)) as [ | H1 ].
            ++ right.
            ++ left; exists (b::m). apply -> Nat.succ_lt_mono. apply H1.
          - right.
        * left; exists nil; apply Nat.lt_0_succ.
        * right.
      + intros []; simpl; intros v.
        * destruct (vec_head v) as [ (s & _) | ].
          2: exact False.
          destruct (vec_head (vec_tail v)) as [ (t & _) | ].
          2: exact False.
          exact (lc ⊳ s∕t).
        * destruct (vec_head v) as [ (s & _) | ].
          2: exact False.
          destruct (vec_head (vec_tail v)) as [ (t & _) | ].
          2: exact False.
          exact (s <> t /\ exists u, u++s = t).
        * exact (vec_head v = vec_head (vec_tail v)).
    Defined.

    (* This model his decidable sem_pred *)

    Lemma Σbpcp_model_dec : fo_model_dec Σbpcp_model.
    Proof.
      intros []; simpl; intros v; vec split v with x; vec split v with y; vec nil v; clear v; simpl;
        revert x y; intros [ (x & Hx) | ] [ (y & Hy) | ]; simpl; try tauto.
      + apply bpcp_hand_dec.
      + destruct (list_eq_dec bool_dec x y);
        destruct (is_a_tail_dec bool_dec y x); tauto.
      + destruct (list_eq_dec bool_dec x y) as [ | C ]; [ left | right ].
        * subst; repeat f_equal; apply lt_pirr.
        * contradict C; inversion C; auto.
      + right; discriminate.
      + right; discriminate.
    Qed.

    Lemma Σbpcp_model_interpreted x y : 
           fom_rels Σbpcp_model Σbpcp_eq (x##y##ø) <-> x = y.
    Proof. reflexivity. Qed.

    Hint Resolve Σbpcp_model_dec : core.

    Notation sem_sym  := (fom_syms Σbpcp_model).
    Notation sem_pred := (fom_rels Σbpcp_model).

    Notation "⟦ t ⟧" := (fun φ => fo_term_sem Σbpcp_model φ t).
    Notation "⟪ A ⟫" := (fun φ => fol_sem Σbpcp_model φ A).

    Let fot_sem_lb_app lb t φ : 
      match ⟦ t ⟧ φ with
        | Some (exist _ m Hm) =>   
          match le_lt_dec (S n) (length lb + length m) with
            | left _  => ⟦ lb_app lb t ⟧ φ = None
            | right _ => exists H, ⟦ lb_app lb t ⟧ φ = Some (exist _ (lb++m) H)
          end
        | None => ⟦ lb_app lb t ⟧ φ = None
      end.
    Proof.
      induction lb as [ | x lb IH ]; simpl lb_app.
      + destruct (⟦ t ⟧ φ) as [ (m & Hm) | ]; auto.
        simpl plus; solve ite; simpl; exists Hm; auto.
      + destruct (⟦ t ⟧ φ) as [ (m & Hm) | ]; auto.
        2: { rew fot; unfold vec_map.
             simpl in IH |- *; rewrite IH; auto. }
        simpl plus.
        destruct (le_lt_dec (S n) (length lb + length m)) as [ H1 | H1 ].
        * destruct (le_lt_dec (S n) (S (length lb+length m))) as [ H2 | H2 ].
          2: exfalso; lia.
          rew fot; unfold vec_map.
          simpl in IH |- *; rewrite IH; auto. 
        * destruct IH as (H2 & IH).
          destruct (le_lt_dec (S n) (S (length lb+length m))) as [ H3 | H3 ].
          - rew fot; unfold vec_map; simpl in IH |- *; rewrite IH; simpl.
            destruct (le_lt_dec n (length (lb++m))) as [ | C ]; auto.
            exfalso; rewrite app_length in C; lia.
          - assert (length ((x::lb)++m) < S n) as H4.
            { simpl; rewrite app_length; auto. }
            exists H4; rew fot; unfold vec_map.
            simpl in IH |- *; rewrite IH; simpl.
            destruct (le_lt_dec n (length (lb++m))) as [ H5 | H5 ].
            ++ exfalso; rewrite app_length in H5; lia.
            ++ do 2 f_equal; apply lt_pirr.
    Qed.

    Let fot_sem_lb_app_Some lb t φ lt Ht (H : length (lb++lt) < S n) : 
           ⟦t⟧ φ = Some (exist _ lt Ht) -> ⟦lb⤜t⟧ φ = Some (exist _ (lb++lt) H).
    Proof.
      intros H1.
      generalize (fot_sem_lb_app lb t φ); rew fot; simpl vec_map; rewrite H1.
      rewrite <- app_length; solve ite.
      intros (G & ->); do 2 f_equal; apply lt_pirr.
    Qed.

    Let fot_sem_lb_app_e lb φ (H : length lb < S n) : ⟦lb⤜e⟧ φ = Some (exist _ lb H).
    Proof.
      revert H.
      rewrite (app_nil_end lb); intros H.
      rewrite <- app_nil_end at 1. 
      apply fot_sem_lb_app_Some with (Ht := Nat.lt_0_succ _).
      rew fot; simpl; auto.
    Qed.

    Let sem_fol_dec A φ : { ⟪A⟫ φ } + { ~ ⟪A⟫ φ }.
    Proof. apply fol_sem_dec; auto. Qed.

    Let φ0 : nat -> X := fun _ => None.

    Let sem_phi_P : ⟪ phi_P ⟫ φ0.
    Proof.
      simpl; intros [ (x & Hx) | ] [ (y & Hy) | ]; simpl;
      rew fot; unfold sem_sym in |- *; simpl; try tauto.
      intros _; split; intros ?; discriminate.
    Qed.

    Let sem_phi_lt : ⟪ phi_lt ⟫ φ0.
    Proof.
      simpl; split; rew fot; simpl.
      + intros [ (x & Hx) | ]; simpl; auto.
        intros ( [] & _ ); auto.
      + intros [ (x & Hx) | ] [ (y & Hy) | ] [ (z & Hz) | ]; rew fot; simpl; try tauto.
        intros (H1 & H2) (H3 & H4); split; repeat (rew fot; simpl); auto.
        * intros ->.
          destruct H2 as (a & <-).
          destruct H4 as (b & H4).
          destruct b as [ | u b ].
          - destruct a as [ | v a ].
            ++ destruct H3; auto.
            ++ apply f_equal with (f := @length _) in H4.
               simpl in H4; rewrite app_length in H4; lia.
          - apply f_equal with (f := @length _) in H4.
            simpl in H4; do 2 rewrite app_length in H4; lia.
        * clear H1 H3; revert H2 H4.
          intros (a & <-) (b & <-).
          exists (b++a); rewrite app_ass; auto.
    Qed.

    Let sem_phi_eq : ⟪ phi_eq ⟫ φ0.
    Proof.
      msplit 6; rew fot.
      1,2: intros [ (x & Hx) | ]; repeat (rew fot; simpl); try discriminate;
          destruct (le_lt_dec n (length x)) as [ | ]; try discriminate.
      1,2: intros [ (x & Hx) | ] [ (y & Hy) | ]; repeat (rew fot; simpl); auto;
          try destruct (le_lt_dec n (length x)) as [ | ]; try destruct (le_lt_dec n (length y)) as [ | ];
          try discriminate; try tauto;
          inversion 2; subst; repeat f_equal; apply lt_pirr.
      1,2: repeat (rew fot; simpl); auto.
      intros [ (x & Hx) | ] [ (y & Hy) | ]; repeat (rew fot; simpl); auto;
          try destruct (le_lt_dec n (length x)) as [ | ]; try destruct (le_lt_dec n (length y)) as [ | ];
          try discriminate; try tauto.
    Qed.

    Opaque le_lt_dec.

    (* (Σbpcp_model,φ0) is a model of phi_simul *)

    Let sem_phi_simul : ⟪ phi_simul ⟫ φ0.
    Proof.
      intros x y H; rewrite fol_sem_ldisj; revert x y H.
      intros [ (x' & Hx) | ] [ (y' & Hy) | ]; 
        repeat (rew fot; simpl); try tauto.
      intros H.
      apply pcp_hand_inv in H.
      destruct H as [ H | (x & y & p & q & H1 & H2 & -> & -> & H) ].
      + exists (lt_simul (x',y')); split.
        * apply in_map_iff; exists (x',y'); auto.
        * unfold lt_simul; simpl; left; split.
          - rew fot.
            rewrite fot_sem_lb_app_e with (H := Hx).
            simpl; auto.
          - rew fot.
            rewrite fot_sem_lb_app_e with (H := Hy).
            simpl; auto.
      + exists (lt_simul (x,y)); split.
        * apply in_map_iff; exists (x,y); split; auto.
        * unfold lt_simul; right.          
          exists (⟦p⤜e⟧ φ0), (⟦q⤜e⟧ φ0).
          assert (length p < S n) as H5 by (rewrite app_length in Hx; lia).
          assert (length q < S n) as H6 by (rewrite app_length in Hy; lia).
          rewrite fot_sem_lb_app_e with (H := H5).
          rewrite fot_sem_lb_app_e with (H := H6).
          simpl; msplit 3; simpl; auto.
          - rew fot.
            rewrite fot_sem_lb_app_Some with (lt := p) (Ht := H5) (H := Hx).
            ++ simpl; auto.
            ++ rew fot; simpl; auto.
          - rew fot.
            rewrite fot_sem_lb_app_Some with (lt := q) (Ht := H6) (H := Hy).
            ++ simpl; auto.
            ++ rew fot; simpl; auto.
          - destruct H as [ (G1 & G2) | [ (G1 & G2) | (G1 & G2) ] ].
            ++ left; split.
               ** split.
                  -- revert G1; apply list_app_head_not_nil.
                  -- exists x; auto.
               ** rew fot; simpl; subst; do 2 f_equal; apply lt_pirr.
            ++ right; left; split.
               ** split.
                  -- revert G2; apply list_app_head_not_nil.
                  -- exists y; auto.
               ** rew fot; simpl; subst; do 2 f_equal; apply lt_pirr.
            ++ do 2 right; split.
               ** split.
                  -- revert G1; apply list_app_head_not_nil.
                  -- exists x; auto.
               ** split.
                  -- revert G2; apply list_app_head_not_nil.
                  -- exists y; auto.
    Qed.

    Let sem_phi_solvable : ⟪ ∃ £0 ⧓ £0 ⟫ φ0.
    Proof. exists (Some (exist _ l (Nat.lt_succ_diag_r _))); simpl; auto. Qed.

    Theorem Sig_bpcp_encode_sound : @fo_form_fin_dec_eq_SAT Σbpcp Σbpcp_eq eq_refl Σbpcp_encode.
    Proof using Hl.
      exists X, Σbpcp_model, Σbpcp_model_finite, Σbpcp_model_dec,
             Σbpcp_model_interpreted, φ0; split; auto.
      unfold Σbpcp_encode; repeat (split; auto).
    Qed.

  End soundness.

  Section completeness.

    (* We assume an interpreted and finite model *)

    Variable (X : Type) (M : fo_model Σbpcp X) 
             (HM : finite X)
             (He : forall x y, fom_rels M Σbpcp_eq (x##y##ø) <-> x = y)
             .

    Notation sem_sym := (fom_syms M).
    Notation sem_pred := (fom_rels M).

    Notation "⟦ t ⟧" := (fun φ => fo_term_sem M φ t).
    Notation "⟪ A ⟫" := (fun φ => fol_sem M φ A).

    Let fot_sem_lb_app l t φ : ⟦l⤜t⟧ φ = ⟦l⤜£0⟧ (⟦t⟧φ)·φ.
    Proof.
      revert φ; induction l as [ | b l IHl ]; intros phi; simpl.
      + rew fot; auto.
      + rew fot; f_equal; simpl; f_equal; auto.
    Qed.

    Variable (φ : nat -> X) (model : ⟪ Σbpcp_encode ⟫ φ).

    Notation ε := (@sem_sym Σbpcp_unit ø).
    Notation "⋇" := (@sem_sym Σbpcp_undef ø).

    Let f b x := (@sem_sym (Σbpcp_bool b) (x##ø)).
    Let P x y := @sem_pred Σbpcp_hand (x##y##ø).
    Notation "x ⪡ y" := (@sem_pred Σbpcp_ssfx (x##y##ø)) (at level 70).
    Notation "x ≅ y" := (@sem_pred Σbpcp_eq (x##y##ø)) (at level 70).

    Let lt_pair u v x y := (  u ⪡ x /\ v ≅ y
                           \/ v ⪡ y /\ u ≅ x
                           \/ u ⪡ x /\ v ⪡ y ).

    (* The axiom interpreted directly gives us properties of the model *)

    Let HP x y : P x y -> x <> ⋇ /\ y <> ⋇.
    Proof. do 2 rewrite <- He; apply model. Qed.

    Let Hfb_1 b x : f b x <> ε.
    Proof. rewrite <- He; destruct b; apply model. Qed.

    Let Hfb_2 b x y : f b x <> ⋇ -> f b x = f b y -> x = y.
    Proof. do 3 rewrite <- He; destruct b; revert x y; apply model. Qed.

    Let Hfb_3 x y : f true x = f false y -> f true x = ⋇ /\ f false y = ⋇.
    Proof. do 3 rewrite <- He; apply model. Qed.

    Let Hfb_4 b : f b ⋇ = ⋇.
    Proof.
      rewrite <- He. 
      destruct model as (_ & _ & H & _).
      destruct H as (_ & _ & _ & _ & H1 & H2 & _ ).
      destruct b; auto.
    Qed.

    Let Hlt_irrefl x : ~ x ⪡ x.
    Proof. apply model. Qed.
  
    Let Hlt_trans x y z : x ⪡ y -> y ⪡ z -> x ⪡ z.
    Proof. apply model. Qed.

    Let sb_app l x := ⟦l⤜£0⟧ x·φ.

    Let Hsimul x y : 
          P x y 
       -> exists s t, In (s,t) lc 
                  /\ ( x = sb_app s ε /\ y = sb_app t ε
                   \/  exists u v, P u v 
                                /\ x = sb_app s u 
                                /\ y = sb_app t v
                                /\ lt_pair u v x y 
                     ).
    Proof.
      intros H.
      destruct model as (_ & _ & _ & Hmodel & _).
      unfold phi_simul in Hmodel; simpl in Hmodel.
      apply Hmodel in H.
      apply fol_sem_ldisj in H.
      destruct H as (c & Hc & H).
      rewrite in_map_iff in Hc.
      destruct Hc as ((s,t) & <- & Hst).
      exists s, t; split; auto.
      unfold sb_app; simpl; rew fot.
      destruct H as [ (H1 & H2) | (u & v & H1 & H2 & H3 & H4) ].
      + apply He in H1; apply He in H2; simpl in H1, H2. 
        left; split.
        * rewrite H1; do 2 rewrite fot_sem_lb_app; simpl.
          apply fo_term_sem_ext.
          rewrite fot_vars_lb_app; simpl.
          intros ? [ <- | [] ]; auto.
        * rewrite H2; do 2 rewrite fot_sem_lb_app; simpl.
          apply fo_term_sem_ext.
          rewrite fot_vars_lb_app; simpl.
          intros ? [ <- | [] ]; auto.
      + apply He in H2; apply He in H3; simpl in H2, H3. 
        right; exists u, v; msplit 3.
        * apply H1.
        * rewrite H2; do 2 rewrite fot_sem_lb_app; simpl.
          apply fo_term_sem_ext.
          rewrite fot_vars_lb_app; simpl.
          intros ? [ <- | [] ]; auto.
        * rewrite H3; do 2 rewrite fot_sem_lb_app; simpl.
          apply fo_term_sem_ext.
          rewrite fot_vars_lb_app; simpl.
          intros ? [ <- | [] ]; auto.
        * apply H4.
    Qed.

    Let P_refl : exists x, P x x.
    Proof. apply model. Qed.

    (* Ok we have all the ops in the model ... let us prove some real stuff *)

    Let sb_app_fb b l x : sb_app (b::l) x = f b (sb_app l x).
    Proof. auto. Qed.

    Let sb_app_nil x : sb_app nil x = x.
    Proof. auto. Qed.

    Let sb_app_inj l m : sb_app l ε <> ⋇ -> sb_app l ε = sb_app m ε -> l = m.
    Proof.
      revert m; induction l as [ | [] l IH ]; intros [ | [] m ] H E; auto.
      + rewrite sb_app_fb, sb_app_nil in E.
        apply eq_sym, Hfb_1 in E; tauto.
      + rewrite sb_app_fb, sb_app_nil in E.
        apply eq_sym, Hfb_1 in E; tauto.
      + rewrite sb_app_fb, sb_app_nil in E.
        apply Hfb_1 in E; tauto.
      + do 2 rewrite sb_app_fb in E.
        apply Hfb_2 in E.
        * f_equal; apply IH; auto.
          contradict H.
          rewrite sb_app_fb, H, Hfb_4; auto.
        * intros C; apply H.
          rewrite sb_app_fb; auto.
      + do 2 rewrite sb_app_fb in E.
        apply Hfb_3 in E.
        destruct H.
        rewrite sb_app_fb; tauto.
      + rewrite sb_app_fb, sb_app_nil in E.
        apply Hfb_1 in E; tauto.
      + do 2 rewrite sb_app_fb in E. 
        apply eq_sym, Hfb_3 in E; tauto.
      + do 2 rewrite sb_app_fb in E.
        apply Hfb_2 in E.
        * f_equal; apply IH; auto.
          contradict H.
          rewrite sb_app_fb, H, Hfb_4; auto.
        * intros C; apply H.
          rewrite sb_app_fb; auto.
    Qed.

    Let sb_app_congr l m x y z : x = sb_app l y -> y = sb_app m z -> x = sb_app (l++m) z.
    Proof.
      intros H1 H2.
      unfold sb_app.
      rewrite lb_app_app, fot_sem_lb_app.
      subst; simpl.
      apply fo_term_sem_ext.
      intros n; rewrite fot_vars_lb_app; simpl.
      intros [ <- | [] ]; simpl; auto.
    Qed. 

    Ltac mysolve :=
      match goal with
        | H1 : ?x ⪡ ?y, H2 : ?y ⪡ ?z |- ?x ⪡ ?z => revert H2; apply Hlt_trans
        | H1 : ?x = ?y, H2 : ?y ⪡ ?z |- ?x ⪡ ?z => rewrite H1; apply H2 
        | H1 : ?x ⪡ ?y, H2 : ?y = ?z |- ?x ⪡ ?z => rewrite <- H2; apply H1
        | H1 : ?x = ?y, H2 : ?y = ?z |- ?x = ?z => rewrite H1; apply H2 
      end; auto.

    Let Hlt_wf : well_founded (fun p q => match p, q with (u,v), (x,y) => lt_pair u v x y end).
    Proof. 
      apply wf_strict_order_finite; auto.
      + apply finite_prod; auto.
      + intros (x,y) [ (H1 & H2) | [ (H1 & H2) | (H1 & H2) ] ].
        all: revert H1; apply Hlt_irrefl.
      + intros (x1,x2) (y1,y2) (z1,z2); unfold lt_pair; simpl; rewrite !He.
        intros [ (H1 & H2) | [ (H1 & H2) | (H1 & H2) ] ]
               [ (G1 & G2) | [ (G1 & G2) | (G1 & G2) ] ].
        1: left; split; mysolve.
        4: right; left; split; mysolve.
        all: right; right; split; mysolve.
    Qed.

    Let P_implies_pcp_hand (c : X*X) : 
         let (x,y) := c 
         in   P x y 
           -> exists s t, x = sb_app s ε 
                       /\ y = sb_app t ε 
                       /\ lc ⊳ s∕t.
    Proof.
      induction c as [ (x,y) IH ] using (well_founded_induction Hlt_wf).
      intros Hxy.
      apply Hsimul in Hxy.
      destruct Hxy as (s & t & Hst & [ (H1 & H2) | H ]).
      + exists s, t; msplit 2; auto; constructor 1; auto.
      + destruct H as (u & v & H1 & H2 & H3 & H4).
        destruct (IH (u,v)) with (2 := H1)
          as (s' & t' & G1 & G2 & G3); auto.
        exists (s++s'), (t++t'); msplit 2.
        * apply sb_app_congr with (1 := H2); auto.
        * apply sb_app_congr with (1 := H3); auto.
        * constructor 2; auto.
    Qed.  

    Local Theorem completeness : exists s, lc ⊳ s∕s.
    Proof using HP HM.
      destruct P_refl as (x & Hx).
      destruct (P_implies_pcp_hand (x,x)) with (1 := Hx)
        as (s & t & H1 & H2 & H3).
      apply HP in Hx.
      replace t with s in H3.
      + exists s; auto.
      + apply sb_app_inj; auto.
        * intros H; destruct Hx as [ [] _ ]; subst; auto.
        * rewrite <- H1; auto.
    Qed.

  End completeness.

  Hint Resolve finite_t_finite : core.

  Theorem Sig_bpcp_encode_complete : 
             @fo_form_fin_dec_eq_SAT Σbpcp Σbpcp_eq eq_refl Σbpcp_encode 
          -> exists l, lc ⊳ l∕l.
  Proof.
    intros (X & M & fM & dM & He & phi & Hphi).
    apply completeness with (M := M) (φ := phi); auto.
  Qed.

End BPCP_FIN_DEC_EQ_SAT.
