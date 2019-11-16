(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Bool Lia.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import wf_finite.

From Undecidability.TRAKHTENBROT
  Require Import notations bpcp fol_ops fo_terms fo_logic.

Set Implicit Arguments.

Local Notation ø := vec_nil.

(* Opaque fo_term_subst fo_term_map fo_term_sem. *)

Local Tactic Notation "solve" "ite" :=
      match goal with _ : ?x < ?y |- context[if le_lt_dec ?y ?x then _ else _]
        => let G := fresh in destruct (le_lt_dec y x) as [ G | _ ]; [ exfalso; lia | ]
      end.

Section signature_bpcp.

  Inductive bpcp_syms := fb : bool -> bpcp_syms | fe | fs.
  Inductive bpcp_rels := p_P | p_lt | p_eq.

  Definition Σbpcp : fo_signature.
  Proof.
    exists bpcp_syms bpcp_rels.
    + exact (fun s =>
        match s with
          | fb _ => 1
          | _   => 0
        end).
    + exact (fun _ => 2).
  Defined.

End signature_bpcp.

Section bpcp.

  Variable lc : list (list bool * list bool).

  Notation term := (fo_term nat (ar_syms Σbpcp)).
  Notation form := (fol_form Σbpcp).

  Notation e := (in_fot fe ø).
  Notation "∗" := (in_fot fs ø).

  Notation "¬" := (fun x => x ⤑ ⊥).
  Notation 𝓟  := (fun x y => fol_atom Σbpcp p_P (x##y##ø)).
  Notation "x ≡ y" := (fol_atom Σbpcp p_eq (x##y##ø)) (at level 59).
  Notation "x ≺ y" := (fol_atom Σbpcp p_lt (x##y##ø)) (at level 59).

  Notation f_ := (fun b x => @in_fot _ _ _ (fb b) (x##ø) : term).

  Definition lb_app l t := fold_right f_ t l.

  Fact lb_app_app l m t : lb_app (l++m) t = lb_app l (lb_app m t).
  Proof. apply fold_right_app. Qed.
 
  Fact fot_vars_lb_app l t : fo_term_vars (lb_app l t) = fo_term_vars t.
  Proof.
    induction l as [ | x l IHl ]; simpl; rew fot; auto.
    simpl; rewrite <- app_nil_end; auto.
  Qed.

  Notation lb2term := (fun l => lb_app l e).

  Definition phi_P := ∀ (∀ (𝓟  (£1) (£0) ⤑ ¬ (£1 ≡ ∗) ⟑ ¬ (£0 ≡ ∗))).

  Definition lt_irrefl := ∀ (¬ (£0 ≺ £0)).
  Definition lt_trans := ∀(∀(∀(£2 ≺ £1 ⤑ £1 ≺ £0 ⤑ £2 ≺ £0))).
  Definition phi_lt := lt_irrefl ⟑ lt_trans.

  Definition eq_neq (b : bool) := ∀(¬(f_ b (£0) ≡ e)).
  Definition eq_inj (b : bool) := ∀(∀( ¬(f_ b (£1) ≡ ∗) ⤑ f_ b (£1) ≡ f_ b (£0) ⤑ £1 ≡ £0)).
  Definition eq_real := ∀(∀(f_ true (£1) ≡ f_ false (£0) ⤑ f_ true (£1) ≡ ∗
                                                         ⟑ f_ false (£0) ≡ ∗)).
  Definition eq_undef b := f_ b ∗ ≡ ∗.  (* Dominik forgot that one in his draft *)

  Definition phi_eq := eq_neq true ⟑ eq_neq false 
                     ⟑ eq_inj true ⟑ eq_inj false 
                     ⟑ eq_undef true ⟑ eq_undef false
                     ⟑ eq_real.

  Definition eq_equiv := (∀(£0 ≡ £0)) 
                       ⟑ (∀(∀(£0 ≡ £1 ⤑ £1 ≡ £0)))
                       ⟑ (∀(∀(∀(£0 ≡ £1 ⤑ £1 ≡ £2 ⤑ £0 ≡ £2)))).
 
  Definition eq_congr_f b := ∀(∀(£0 ≡ £1 ⤑ f_ b (£0) ≡ f_ b (£1))).
  Definition eq_congr_pred p := ∀(∀(∀(∀(£0 ≡ £1 ⤑ £2 ≡ £3 ⤑ fol_atom Σbpcp p (£0##£2##ø)
                                                                                                                    ⤑ fol_atom Σbpcp p (£1##£3##ø))))).

  Definition eq_congr := eq_congr_f true 
                       ⟑ eq_congr_f false
                       ⟑ eq_congr_pred p_P
                       ⟑ eq_congr_pred p_lt
                       ⟑ eq_equiv.

  Definition lt_pair (u v x y : term) := (u ≺ x ⟑ v ≡ y) ⟇ (v ≺ y ⟑ u ≡ x) ⟇ (u ≺ x ⟑ v ≺ y).

  Definition lt_simul (c : list bool * list bool) := 
    let (s,t) := c 
    in   (£1 ≡ lb2term s ⟑ £0 ≡ lb2term t)
       ⟇ ∃(∃(𝓟 (£1) (£0) ⟑ £3 ≡ lb_app s (£1) ⟑ £2 ≡ lb_app t (£0) ⟑ lt_pair (£1) (£0) (£3) (£2) )).

  Definition phi_simul := ∀(∀(𝓟 (£1) (£0) ⤑ fol_ldisj (map lt_simul lc))).

  Definition phi_R := phi_P ⟑ phi_lt ⟑ phi_eq 
                    ⟑ phi_simul ⟑ eq_congr
                    ⟑ ∃(𝓟 (£0) (£0)).

  Section BPCP_fin_sat.

    (** This model is decidable because pcp_hand is decidable *)

    Variable (l : list bool) (Hl : pcp_hand lc l l). 

    Let n := length l.

    Let X := option { m : list bool | length m < S n }.
    Let fin_X : finite_t X.
    Proof. apply finite_t_option, finite_t_list, finite_t_bool. Qed.

    Definition bpcp_model : fo_model Σbpcp X.
    Proof.
      exists.
      + intros []; simpl.
        * intros v.
          case_eq (vec_head v).
          - intros (m & Hm) H.
            destruct (le_lt_dec n (length m)) as [ | H1 ].
            ++ right.
            ++ left; exists (b::m); apply lt_n_S, H1.
          - right.
        * left; exists nil; apply lt_0_Sn.
        * right.
      + intros []; simpl; intros v.
        * destruct (vec_head v) as [ (s & Hs) | ].
          2: exact False.
          destruct (vec_head (vec_tail v)) as [ (t & Ht) | ].
          2: exact False.
          exact (pcp_hand lc s t).
        * destruct (vec_head v) as [ (s & Hs) | ].
          2: exact False.
          destruct (vec_head (vec_tail v)) as [ (t & Ht) | ].
          2: exact False.
          exact (s <> t /\ exists u, u++s = t).
        * exact (vec_head v = vec_head (vec_tail v)).
    Defined.

    (** This model has decidable sem_pred *)

    Notation sem_sym  := (fom_syms bpcp_model).
    Notation sem_pred := (fom_rels bpcp_model).

    Let sem_pred_dec : forall p v, { sem_pred p v } + { ~ sem_pred _ v }.
    Proof.
      intros []; simpl; intros v; vec split v with x; vec split v with y; vec nil v; clear v; simpl;
        revert x y; intros [ (x & Hx) | ] [ (y & Hy) | ]; simpl; try tauto.
      + apply pcp_hand_dec, bool_dec.
      + destruct (list_eq_dec bool_dec x y);
        destruct (is_a_tail_dec bool_dec y x); tauto.
      + destruct (list_eq_dec bool_dec x y) as [ | C ]; [ left | right ].
        * subst; repeat f_equal; apply lt_pirr.
        * contradict C; inversion C; auto.
      + right; discriminate.
      + right; discriminate.
    Qed.

    Notation "⟦ t ⟧" := (fun φ => fo_term_sem sem_sym φ t).

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
           ⟦ t ⟧ φ = Some (exist _ lt Ht) -> ⟦ lb_app lb t ⟧ φ = Some (exist _ (lb++lt) H).
    Proof.
      intros H1.
      generalize (fot_sem_lb_app lb t φ); rew fot; simpl vec_map; rewrite H1.
      rewrite <- app_length; solve ite.
      intros (G & ->); do 2 f_equal; apply lt_pirr.
    Qed.

    Let fot_sem_lb_app_e lb φ (H : length lb < S n) : ⟦ lb_app lb e ⟧ φ = Some (exist _ lb H).
    Proof.
      revert H.
      rewrite (app_nil_end lb); intros H.
      rewrite <- app_nil_end at 1. 
      apply fot_sem_lb_app_Some with (Ht := lt_0_Sn _).
      rew fot; simpl; auto.
    Qed.

    Notation "⟪ A ⟫" := (fun φ => fol_sem bpcp_model φ A).

    Let sem_fol_dec A φ : { ⟪A⟫ φ } + { ~ ⟪A⟫ φ }.
    Proof. apply fol_sem_dec; auto. Qed.

    Let φ : nat -> X := fun _ => None.

    Let sem_phi_P : ⟪ phi_P ⟫ φ.
    Proof.
      simpl; intros [ (x & Hx) | ] [ (y & Hy) | ]; simpl;
      unfold env_lift; simpl; rew fot; unfold sem_sym in |- *; simpl; try tauto.
      intros _; split; intros ?; discriminate.
    Qed.

    Let sem_phi_lt : ⟪ phi_lt ⟫ φ.
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

    Let sem_phi_eq : ⟪ phi_eq ⟫ φ.
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

    Let list_app_head_not_nil K (u v : list K) : u <> nil -> v <> u++v.
    Proof.
      intros H; contradict H.
      destruct u as [ | a u ]; auto; exfalso.
      apply f_equal with (f := @length _) in H.
      revert H; simpl; rewrite app_length; lia.
    Qed.

    Let sem_phi_simul : ⟪ phi_simul ⟫ φ.
    Proof.
      intros x y H.
      apply (fol_sem_big_disj bpcp_model).
      revert x y H.
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
          exists (⟦lb_app p e⟧ φ), (⟦lb_app q e⟧ φ).
          assert (length p < S n) as H5 by (rewrite app_length in Hx; lia).
          assert (length q < S n) as H6 by (rewrite app_length in Hy; lia).
          rewrite fot_sem_lb_app_e with (H := H5).
          rewrite fot_sem_lb_app_e with (H := H6).
          simpl; msplit 3; simpl; auto.
          - rew fot.
            rewrite fot_sem_lb_app_Some with (lt0 := p) (Ht := H5) (H := Hx).
            ++ simpl; auto.
            ++ rew fot; simpl; auto.
          - rew fot.
            rewrite fot_sem_lb_app_Some with (lt0 := q) (Ht := H6) (H := Hy).
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

    Tactic Notation "solve" "congr" int(a) int(b) :=
      do a intros [(?&?)|]; simpl; rew fot; simpl; auto; try discriminate; do b inversion 1; auto.

    Let sem_eq_congr : ⟪ eq_congr ⟫ φ.
    Proof.
      msplit 6; repeat (rew fot; simpl); auto.
      + solve congr 2 1.
      + solve congr 2 1.
      + solve congr 4 2.
      + solve congr 4 2.
      + solve congr 3 0; intros H1 H2; rewrite H1; auto.
    Qed.

    Let sem_phi_solvable : ⟪ ∃(𝓟 (£0) (£0)) ⟫ φ.
    Proof.
      simpl.
      exists (Some (exist _ l (lt_n_Sn _))); simpl; auto.
    Qed.

    Theorem BPCP_sat : fo_form_fin_dec_SAT phi_R.
    Proof.
      exists X, bpcp_model, fin_X, sem_pred_dec, φ; split; auto.
      unfold phi_R; repeat (split; auto).
    Qed.

  End BPCP_fin_sat.

  Section fin_sat_BPCP.

    Variable (X : Type) (M : fo_model Σbpcp X) (HM : finite X).
     
    Print fo_model.

    Notation sem_sym := (fom_syms M).
    Notation sem_pred := (fom_rels M).

    Notation "⟦ t ⟧" := (fun φ => fo_term_sem sem_sym φ t).
    Notation "⟪ A ⟫" := (fun φ => fol_sem M φ A).

    Fact fot_sem_lb_app l t φ : ⟦ lb_app l t ⟧ φ = ⟦ lb_app l (£0) ⟧ (φ ↑ (⟦t⟧φ)).
    Proof.
      revert φ; induction l as [ | b l IHl ]; intros phi; simpl.
      + unfold env_lift; rew fot; auto.
      + rew fot; f_equal; simpl; f_equal; auto.
    Qed.

    Variable (φ : nat -> X) (model : ⟪ phi_R ⟫ φ).

    Notation ε := (@sem_sym fe ø).
    Notation "⋇" := (@sem_sym fs ø).
    Let f b x := (@sem_sym (fb b) (x##ø)).

    Let P x y := @sem_pred p_P (x##y##ø).
    Notation "x ⪡ y" := (@sem_pred p_lt (x##y##ø)) (at level 70).
    Notation "x ≋ y" := (@sem_pred p_eq (x##y##ø)) (at level 70).

    Let lt_pair u v x y    := (  u ⪡ x /\ v ≋ y
                                \/ v ⪡ y /\ u ≋ x
                                \/ u ⪡ x /\ v ⪡ y ).

    (** The axiom interpreted directly gives us properties of the model *)

    Let HP x y : P x y -> ~ x ≋ ⋇ /\ ~ y ≋ ⋇.
    Proof. apply model. Qed.

    Let Hfb_1 b x : ~ f b x ≋ ε.
    Proof. destruct b; apply model. Qed.

    Let Hfb_2 b x y : ~ f b x ≋ ⋇ -> f b x ≋ f b y -> x ≋ y.
    Proof. destruct b; revert x y; apply model. Qed.

    Let Hfb_3 x y : f true x ≋ f false y -> f true x ≋ ⋇ /\ f false y ≋ ⋇.
    Proof. apply model. Qed.

    Let Hfb_4 b : f b ⋇ ≋ ⋇.
    Proof. 
      destruct model as (_ & _ & H & _).
      destruct H as (_ & _ & _ & _ & H1 & H2 & _ ).
      destruct b; auto.
    Qed.

    Let Hlt_irrefl x : ~ x ⪡ x.
    Proof. apply model. Qed.
  
    Let Hlt_trans x y z : x ⪡ y -> y ⪡ z -> x ⪡ z.
    Proof. apply model. Qed.

    Let Heq_refl x : x ≋ x.
    Proof. revert x; apply model. Qed.
  
    Let Heq_sym x y : x ≋ y -> y ≋ x.
    Proof. apply model. Qed.

    Let Heq_trans x y z : x ≋ y -> y ≋ z -> x ≋ z.
    Proof. apply model. Qed.

    Let Heq_congr_1 b x y : x ≋ y -> f b x ≋ f b y.
    Proof. destruct b; apply model. Qed.

    Let Heq_congr_2 x y x' y' : x ≋ x' -> y ≋ y' -> P x y -> P x' y'.
    Proof. apply model. Qed.

    Let Heq_congr_3 x y x' y' : x ≋ x' -> y ≋ y' -> x ⪡ y -> x' ⪡ y'.
    Proof. apply model. Qed.
   
    Let sb_app l x := ⟦ lb_app l (£0) ⟧ (φ↑x).

    Let Hsimul x y : P x y -> exists s t, In (s,t) lc 
                                     /\ ( x ≋ sb_app s ε /\ y ≋ sb_app t ε
                                      \/  exists u v, P u v /\ x ≋ sb_app s u /\ y ≋ sb_app t v
                                                   /\ lt_pair u v x y ).
    Proof.
      intros H.
      destruct model as (_ & _ & _ & Hmodel & _).
      apply Hmodel in H.
      clear Hmodel.
      apply fol_sem_big_disj in H.
      destruct H as (c & Hc & H).
      rewrite in_map_iff in Hc.
      destruct Hc as ((s,t) & <- & Hst).
      exists s, t; split; auto.
      unfold sb_app; simpl; rew fot.
      destruct H as [ (H1 & H2) | (u & v & H1 & H2 & H3 & H4) ].
      + left; split.
        * revert H1; simpl; rew fot; simpl.
          match goal with |- ?a -> ?b => cut (a=b); [ intros -> | ]; auto end.
          do 2 f_equal.
          rewrite fot_sem_lb_app; rew fot; simpl; f_equal.
          apply fo_term_sem_ext.
          rewrite fot_vars_lb_app; simpl.
          intros ? [ <- | [] ]; auto.
        * revert H2; simpl; rew fot; simpl.
          match goal with |- ?a -> ?b => cut (a=b); [ intros -> | ]; auto end.
          do 2 f_equal.
          rewrite fot_sem_lb_app; rew fot; simpl; f_equal.
          apply fo_term_sem_ext.
          rewrite fot_vars_lb_app; simpl.
          intros ? [ <- | [] ]; auto.
      + right; exists u, v; msplit 3.
        * apply H1.
        * revert H2; simpl; rew fot; simpl.
          match goal with |- ?a -> ?b => cut (a=b); [ intros -> | ]; auto end.
          do 2 f_equal.
          rewrite fot_sem_lb_app; rew fot; simpl; f_equal.
          apply fo_term_sem_ext.
          rewrite fot_vars_lb_app; simpl.
          intros ? [ <- | [] ]; auto.
        * revert H3; simpl; rew fot; simpl.
          match goal with |- ?a -> ?b => cut (a=b); [ intros -> | ]; auto end.
          do 2 f_equal.
          rewrite fot_sem_lb_app; rew fot; simpl; f_equal.
          apply fo_term_sem_ext.
          rewrite fot_vars_lb_app; simpl.
          intros ? [ <- | [] ]; auto.
        * apply H4.
    Qed.

    Let P_refl : exists x, P x x.
    Proof. apply model. Qed.

    (* Ok we have all the ops in the model ... let us prove some real stuff *)

    Let Hfb_5 b x : x ≋ ⋇ -> f b x ≋ ⋇.
    Proof. 
      intros H; apply Heq_congr_1 with (b := b) in H.
      apply Heq_trans with (1 := H), Hfb_4.
    Qed.

    Let sb_app_congr_1 l x y : x ≋ y -> sb_app l x ≋ sb_app l y.
    Proof.
      intros H; unfold sb_app.
      induction l as [ | b l IHl ]; simpl; rew fot.
      + unfold env_lift; auto.
      + apply Heq_congr_1; auto.
    Qed.

    Let sb_app_fb b l x : sb_app (b::l) x = f b (sb_app l x).
    Proof. auto. Qed.

    Let sb_app_nil x : sb_app nil x = x.
    Proof. auto. Qed.

    Let sb_app_inj l m : ~ sb_app l ε ≋ ⋇ -> sb_app l ε ≋ sb_app m ε -> l = m.
    Proof.
      revert m; induction l as [ | [] l IH ]; intros [ | [] m ] H E; auto.
      + rewrite sb_app_fb, sb_app_nil in E.
        apply Heq_sym, Hfb_1 in E; tauto.
      + rewrite sb_app_fb, sb_app_nil in E.
        apply Heq_sym, Hfb_1 in E; tauto.
      + rewrite sb_app_fb, sb_app_nil in E.
        apply Hfb_1 in E; tauto.
      + do 2 rewrite sb_app_fb in E.
        apply Hfb_2 in E.
        * f_equal; apply IH; auto.
          contradict H.
          rewrite sb_app_fb.
          apply Hfb_5; auto.
        * intros C; apply H.
          rewrite sb_app_fb; auto.
      + do 2 rewrite sb_app_fb in E.
        apply Hfb_3 in E.
        destruct H.
        rewrite sb_app_fb; tauto.
      + rewrite sb_app_fb, sb_app_nil in E.
        apply Hfb_1 in E; tauto.
      + do 2 rewrite sb_app_fb in E. 
        apply Heq_sym, Hfb_3 in E; tauto.
      + do 2 rewrite sb_app_fb in E.
        apply Hfb_2 in E.
        * f_equal; apply IH; auto.
          contradict H.
          rewrite sb_app_fb.
          apply Hfb_5; auto.
        * intros C; apply H.
          rewrite sb_app_fb; auto.
    Qed.

    Let sb_app_congr l m x y z : x ≋ sb_app l y -> y ≋ sb_app m z -> x ≋ sb_app (l++m) z.
    Proof.
      intros H1 H2.
      unfold sb_app.
      rewrite lb_app_app, fot_sem_lb_app.
      apply (sb_app_congr_1 l) in H2.
      apply Heq_trans with (1 := H1).
      apply Heq_trans with (1 := H2).
      unfold sb_app.
      match goal with |- ?a ≋ ?b => cut (a=b); [ intros -> | ]; auto end.
      apply fo_term_sem_ext.
      intros n; rewrite fot_vars_lb_app; simpl; intros [ <- | [] ].
      auto.
    Qed. 

    Ltac mysolve :=
      match goal with 
        | H1 : ?x ⪡ ?y, H2 : ?y ⪡ ?z |- ?x ⪡ ?z => revert H2; apply Hlt_trans
        | H1 : ?x ≋ ?y, H2 : ?y ⪡ ?z |- ?x ⪡ ?z => revert H2; apply Heq_congr_3
        | H1 : ?x ⪡ ?y, H2 : ?y ≋ ?z |- ?x ⪡ ?z => revert H1; apply Heq_congr_3
        | H1 : ?x ≋ ?y, H2 : ?y ≋ ?z |- ?x ≋ ?z => revert H2; apply Heq_trans
      end; auto.

    Let Hlt_wf : well_founded (fun p q => match p, q with (u,v), (x,y) => lt_pair u v x y end).
    Proof. 
      apply wf_strict_order_finite; auto.
      + apply finite_prod; auto.
      + intros (x,y) [ (H1 & H2) | [ (H1 & H2) | (H1 & H2) ] ].
        all: revert H1; apply Hlt_irrefl.
      + intros (x1,x2) (y1,y2) (z1,z2); unfold lt_pair; simpl.
        intros [ (H1 & H2) | [ (H1 & H2) | (H1 & H2) ] ]
               [ (G1 & G2) | [ (G1 & G2) | (G1 & G2) ] ].
        1: left; split; mysolve.
        4: right; left; split; mysolve.
        all: right; right; split; mysolve.
    Qed.

    Let P_implies_pcp_hand c : match c with (x,y) => 
           P x y -> exists s t, x ≋ sb_app s ε /\ y ≋ sb_app t ε /\ pcp_hand lc s t 
         end.
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

    Theorem model_implies_pcp_hand : exists s, pcp_hand lc s s.
    Proof.
      destruct P_refl as (x & Hx).
      destruct (P_implies_pcp_hand (x,x)) with (1 := Hx)
        as (s & t & H1 & H2 & H3).
      apply HP in Hx.
      replace t with s in H3.
      + exists s; auto.
      + apply sb_app_inj.
        * intros H; destruct Hx as [ [] _ ].
          apply Heq_trans with (1 := H1); auto.
        * apply Heq_trans with (2 := H2); auto.
    Qed.

  End fin_sat_BPCP.

  Theorem fin_sat_BPCP : fo_form_fin_SAT phi_R -> exists l, pcp_hand lc l l.
  Proof.
    intros (X & M & fM  & phi & Hphi).
    apply model_implies_pcp_hand with (M := M) (φ := phi); auto.
    apply finite_t_finite; auto.
  Qed.

End bpcp.
