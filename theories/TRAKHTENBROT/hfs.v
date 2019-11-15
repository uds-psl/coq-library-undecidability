(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Nat Lia Max Wellfounded Coq.Setoids.Setoid Eqdep_dec Bool.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos fin_quotient.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import wf_finite wf_chains.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops membership.

Set Implicit Arguments.

Local Definition forall_equiv X := @fol_quant_sem_ext X fol_fa.
Local Definition exists_equiv X := @fol_quant_sem_ext X fol_ex.

Section btree.

  (* ⌞ ⌟ ∅ ⪧ ≈ ≉ ∈ ∉ ⋷  ≾ ≺ ε ∙ ∊ *)

  Inductive bt : Set := bt_leaf | bt_node : bt -> bt -> bt.

  Notation "∅" := bt_leaf.

  Infix "∙" := bt_node.  (* replaced with a non symmetric notation *)
  Infix "⪧" := bt_node.

  (** Indeed x⪧t represent {x}∪t *)

  Section bt_rect'.

    (** When we inspect bt as lists, we can switch to this principle 

        In fact, btrees code HF-sets like this

            {x1,...,xn} = x1⪧...⪧xn⪧∅

        We could also use rose-trees but may be this would be more
        difficult ?
     *)

    Variables (P : bt -> Type) 
              (HP0 : P ∅)
              (HP1 : forall x t, P t -> P (x⪧t)).
  
    Theorem bt_rect' t : P t.
    Proof. induction t; auto. Qed.

  End bt_rect'.
   
  Fact bt_eq_dec (s t : bt) : { s = t } + { s <> t }.
  Proof. decide equality. Qed.

  Fact bt_eq_pirr (s t : bt) (H1 H2 : s = t) : H1 = H2.
  Proof. apply UIP_dec, bt_eq_dec. Qed.

  Fixpoint bt_depth t :=
    match t with
      | ∅   => 0
      | r⪧s => max (S ⌞r⌟) ⌞s⌟
    end
  where "⌞ t ⌟" := (bt_depth t).

  (* ⌞ ⌟ ∅ ⪧ ≈ *)

  Inductive bt_equiv : bt -> bt -> Prop :=
    | in_bte_refl : forall s,             s ≈ s
    | in_bte_sym  : forall s t,           s ≈ t
                                       -> t ≈ s
    | in_bte_tran : forall r s t,         r ≈ s
                                       -> s ≈ t
                                       -> r ≈ t
    | in_bte_cntr : forall s t,       s⪧s⪧t ≈ s⪧t
    | in_bte_comm : forall s t u,     s⪧t⪧u ≈ t⪧s⪧u
    | in_bte_cngr : forall s s' t t',     s ≈ s'
                                       -> t ≈ t'
                                   ->   s⪧t ≈ s'⪧t'
  where "s ≈ t" := (bt_equiv s t).

  Notation "s ≉ t" := (~ s ≈ t).

  Notation bte_refl := in_bte_refl.
  Notation bte_trans := in_bte_tran.
 
  Hint Constructors bt_equiv.

  Fact bte_sym x y : x ≈ y <-> y ≈ x.
  Proof. split; auto. Qed.

  Global Add Parametric Relation: (bt) (bt_equiv)
      reflexivity proved by bte_refl
      symmetry proved by in_bte_sym
      transitivity proved by bte_trans
    as bte_rst.

  Global Add Parametric Morphism: (bt_node) with signature 
       (bt_equiv) ==> (bt_equiv) ==> (bt_equiv) as bt_node_congr.
  Proof.
    intros x y H1 a b H2; auto.
  Qed.

  Fact bte_leaf_eq s t : s ≈ t -> (s = ∅ <-> t = ∅).
  Proof. induction 1; try tauto; split; discriminate. Qed.

  Fact bte_discr s t : s⪧t ≉ ∅.
  Proof. 
   intros H; apply bte_leaf_eq in H.
   generalize (proj2 H eq_refl); discriminate.
  Qed.

  Fact bte_inv_0 s : s ≈ ∅ <-> s = ∅.
  Proof.
    split.
    + intros H; destruct s; auto.
      apply bte_discr in H; tauto.
    + intros ->; auto.
  Qed.

  (* s belongs to t if adding s to t does not change t *)

  Definition bt_mem s t := s⪧t ≈ t.

  Infix "∈" := bt_mem.
  Notation "s ∉ t" := (~ s ∈ t).

  (* ⌞ ⌟ ∅ ⪧ ≈  ∈ ⋷  *)

  Section establishing_membership_inversion.

    (* A restricted definition of membership, not up to equivalence *)

    Inductive bt_restr_mem : bt -> bt -> Prop :=
      | in_btrm_0 : forall s t,            s ⋷ s⪧t
      | in_btrm_1 : forall s t u, s ⋷ u -> s ⋷ t⪧u
    where "s ⋷ t" := (bt_restr_mem s t).

    Hint Constructors bt_restr_mem.

    Fact btrm_inv u s t : u ⋷ s⪧t <-> u = s \/ u ⋷ t.
    Proof.
      split.
      + inversion 1; auto.
      + intros [ <- | ]; constructor; auto.
    Qed.

    Notation "s ≾ t" := (forall u, u ⋷ s -> exists v, v ⋷ t /\ u ≈ v).

    Fact bt_rincl_refl s : s ≾ s.
    Proof. intros u; exists u; auto. Qed.

    Fact bt_rincl_trans r s t : r ≾ s -> s ≾ t -> r ≾ t.
    Proof.
      intros H1 H2 u Hu.
      destruct H1 with (1 := Hu) as (v & Hv & H3).
      destruct H2 with (1 := Hv) as (w & ? & ?).
      exists w; split; auto.
      apply bte_trans with v; auto.
    Qed.

    Hint Resolve bt_rincl_refl bt_rincl_trans.

    Lemma bte_rincl s t : s ≈ t -> s ≾ t.
    Proof.
      intros H.
      assert (s ≾ t /\ t ≾ s) as K; [ | apply K ].
      induction H as [ s | s t H IH | r s t H1 [] H2 [] 
                     | s t | s t u | s s' t t' H1 [H2 H3] H4 [H5 H6] ]; 
        auto; try tauto.
      + split; apply bt_rincl_trans with s; auto.
      + split; intros u; rewrite btrm_inv; intros [ <- | ]; exists u; auto.
      + split; intros v; rewrite btrm_inv; intros [ <- | ]; exists v; auto;
          revert H; rewrite btrm_inv; intros [ <- | ]; auto.
      + split.
        * intros u; rewrite btrm_inv.
          intros [ <- | ].
          - exists s'; auto.
          - destruct (H5 _ H) as (v & ? & ?); exists v; auto.
        * intros u; rewrite btrm_inv.
          intros [ <- | ].
          - exists s; auto.
          - destruct (H6 _ H) as (v & ? & ?); exists v; auto.
    Qed.
 
    Fact btrm_btm s t : s ⋷ t -> s ∈ t.
    Proof.
      induction 1 as [ | s t u ]; try (constructor; auto; fail).
      constructor; apply bte_trans with (t⪧s⪧u); auto.
    Qed.

    Hint Resolve btrm_btm.

    Fact btm_congr_l s t u : s ≈ t -> s ∈ u -> t ∈ u.
    Proof.
      intros H1 H2.
      apply bte_trans with (2 := H2); auto.
    Qed.

    Fact btm_congr_r s t u : s ≈ t -> u ∈ s -> u ∈ t.
    Proof.
      intros H1 H2.
      apply bte_trans with (2 := H1),
            bte_trans with (2 := H2); auto.
    Qed.
  
    Fact btm_inv_0 s : s ∈ ∅ <-> False.
    Proof. split; try tauto; apply bte_discr. Qed.

    Fact btm_inv u s t : u ∈ s⪧t <-> u ≈ s \/ u ∈ t.
    Proof.
      split.
      + intros H.
        destruct (@bte_rincl _ _ H u) as (v & H1 & ?); auto.
        revert H1; rewrite btrm_inv; intros [ <- | ]; auto.
        right; apply bte_trans with (v⪧t); auto.
        apply btrm_btm; auto.
      + intros [ H | H ].
        * apply btm_congr_l with s; auto.
        * apply bte_trans with (1 := in_bte_comm _ _ _); auto.
    Qed.

  End establishing_membership_inversion.

  Global Add Parametric Morphism: (bt_mem) with signature 
       (bt_equiv) ==> (bt_equiv) ==> (iff) as bte_congr.
  Proof.
    intros x y H1 a b H2; split; intros H.
    + apply btm_congr_l with (1 := H1),
            btm_congr_r with (1 := H2); auto.
    + rewrite bte_sym in H1.
      rewrite bte_sym in H2.
      apply btm_congr_l with (1 := H1),
            btm_congr_r with (1 := H2); auto.
  Qed.

  Tactic Notation "btm" "simpl" :=
    repeat match goal with
      | |- context[_ ∈ _ ⪧ _] => rewrite btm_inv; auto; try tauto
      | |- context[_ ∈ ∅]    => rewrite btm_inv_0; auto; try tauto
    end.

  Section establishing_decidability.

    Reserved Notation "x ≺ y" (at level 70, no associativity).

    Inductive bt_lt : bt -> bt -> Prop :=
      | in_btlt_0 : forall s t,                   ∅ ≺ s⪧t 
      | in_btlt_1 : forall s s' t t', s ≺ s' -> s⪧t ≺ s'⪧t'
      | in_btlt_2 : forall s t t',    t ≺ t' -> s⪧t ≺ s⪧t'
    where "s ≺ t" := (bt_lt s t).

    Hint Constructors bt_lt.

    Fact bt_lt_irrefl s : ~ s ≺ s.
    Proof.
      intros H.
      assert (forall t, s ≺ t -> s <> t) as D; 
        [ | apply D in H; destruct H; auto ].
      clear H; induction 1 as [ s t | s s' t t' H IH | s t t' H IH ]; 
        try discriminate; contradict IH; inversion IH; auto.
    Qed.

    Fact bt_lt_trans r s t : r ≺ s -> s ≺ t -> r ≺ t.
    Proof.
      intros H1; revert H1 t.
      induction 1; inversion 1; auto.
    Qed.
  
    Fact bt_lt_eq_lt_dec s t : { s ≺ t } + { s = t } + { t ≺ s }.
    Proof.
      revert t; induction s as [ | s1 H1 s2 H2 ] using bt_rect; intros [ | t1 t2 ]; auto.
      destruct (H1 t1) as [ [] | ]; auto;
        destruct (H2 t2) as [ [] | ]; subst; auto.
    Qed.

    Fixpoint bt_insert s t : bt :=
      match t with
        | ∅   => s⪧∅
        | t⪧u => match bt_lt_eq_lt_dec s t with
          | inleft (left _)  => s⪧t⪧u
          | inleft (right _) => t⪧u
          | inright _        => t⪧(s→u)
        end
      end
    where "s → t" := (bt_insert s t).

    Fact bt_lt_eq_lt_dec_refl s : exists H, bt_lt_eq_lt_dec s s = inleft (right H).
    Proof.
      destruct (bt_lt_eq_lt_dec s s) as [ [ C | H ] | C ].
      1,3: exfalso; revert C; apply bt_lt_irrefl.
      exists H; auto.
    Qed.

    Ltac bt_lt_eq H := 
      match goal with 
        |- context [bt_lt_eq_lt_dec ?x ?x] 
             => destruct (bt_lt_eq_lt_dec_refl x) as (H & ->)
      end.

    Fact bt_insert_leaf s : s→∅ = s⪧∅.
    Proof. reflexivity. Qed.

    Fact bt_insert_eq s t : s→s⪧t = s⪧t.
    Proof. simpl; bt_lt_eq H; auto. Qed.

    Fact bt_insert_lt s t u : s ≺ t -> s→t⪧u = s⪧t⪧u.
    Proof.
      intros H; simpl.
      destruct (bt_lt_eq_lt_dec s t) as [ [C|C] | C ]; auto.
      + contradict H; subst; apply bt_lt_irrefl.
      + destruct (@bt_lt_irrefl s); apply bt_lt_trans with t; auto.
    Qed.

    Fact bt_insert_gt s t u : t ≺ s -> s→t⪧u = t⪧(s→u).
    Proof.
      intros H; simpl.
      destruct (bt_lt_eq_lt_dec s t) as [ [C|C] | C ]; auto.
      + destruct (@bt_lt_irrefl s); apply bt_lt_trans with t; auto.
      + contradict H; subst; apply bt_lt_irrefl.
    Qed.

    Fact bt_insert_equiv s t : s→t ≈ s⪧t.
    Proof.
      induction t as [ | t u Hu ] using bt_rect'; simpl; auto.
      destruct (bt_lt_eq_lt_dec s t) as [ [] | ]; subst; auto.
      apply bte_trans with (t⪧s⪧u); auto.
    Qed.

    Fixpoint bt_norm t :=
      match t with
        | ∅   => ∅
        | s⪧t => s† → t†
      end
    where "t †" := (bt_norm t).

    Hint Resolve bt_insert_equiv.
  
    Fact bt_norm_eq t : t† ≈ t.
    Proof.
      induction t as [ | s ? t ? ]; simpl; auto.
      apply bte_trans with (s†⪧t†); auto.
    Qed.

    Opaque bt_insert.

    Tactic Notation "rew" "bt" "insert" := 
      repeat match goal with 
        |             |- context[_→∅]     => rewrite bt_insert_leaf
        |             |- context[?x→?x⪧_] => rewrite bt_insert_eq
        | H : ?x ≺ ?y |- context[?x→?y⪧_] => rewrite bt_insert_lt with (1 := H)
        | H : ?x ≺ ?y |- context[?y→?x⪧_] => rewrite bt_insert_gt with (1 := H)
      end.

    Tactic Notation "bt" "insert" "case" hyp(x) hyp(y) :=
      destruct (bt_lt_eq_lt_dec x y) as [ [|] | ]; subst; rew bt insert; auto.

    Tactic Notation "bt" "lt" "trans" constr(t) := apply bt_lt_trans with t; auto.

    Tactic Notation "bt" "lt" "cycle" :=
      match goal with
        | H1 : ?x ≺ ?x |- _  => destruct (@bt_lt_irrefl x); auto
        | H1 : ?x ≺ ?y, 
          H2 : ?y ≺ ?x |- _  => destruct (@bt_lt_irrefl x); bt lt trans y
        | H1 : ?x ≺ ?y,
          H2 : ?y ≺ ?z,
          H3 : ?z ≺ ?x |- _  => destruct (@bt_lt_irrefl x); bt lt trans y; bt lt trans z
      end.

    Fact bt_insert_cntr s t : s→s→t = s→t.
    Proof.
      induction t as [ | t1 t2 IH2 ] using bt_rect'; rew bt insert; auto.
      bt insert case s t1; f_equal; auto.
    Qed.

    Fact bt_insert_comm s t u : s→t→u = t→s→u.
    Proof.
      induction u as [ | u1 u2 IH ] using bt_rect'. 
      + rew bt insert; bt insert case s t.
      + bt insert case t u1; 
        bt insert case s u1; 
        bt insert case s t; 
        try bt lt cycle; 
        f_equal; auto.
    Qed.

    Hint Resolve bt_insert_cntr bt_insert_comm bt_norm_eq.

    Theorem bte_norm_iff s t : s ≈ t <-> s† = t†.
    Proof.
      split.
      + induction 1; simpl; auto.
        * transitivity s†; auto.
        * f_equal; auto.
      + intros H.
        apply bte_trans with s †; auto.
        rewrite H; auto.
    Qed.

    Theorem bt_norm_idem s : s†† = s†.
    Proof. apply bte_norm_iff; auto. Qed.

    Theorem bte_dec s t : { s ≈ t } + { s ≉ t }.
    Proof.
      destruct (bt_eq_dec s† t†) as [ H | H ];
      rewrite <- bte_norm_iff in H; auto.
    Qed.

  End establishing_decidability.

  Corollary btm_dec s t : { s ∈ t } + { s ∉ t }.
  Proof. apply bte_dec. Qed.

  Section more_decidability.

    Section btm_ex_dec.
  
      Variable (P : bt -> Prop) (HP : forall s t, s ≈ t -> P s -> P t).

      (** Exist. quantification over subsets *)

      Theorem btm_ex_dec t : (forall x, x ∈ t -> { P x } + { ~ P x })
                       -> { s | s ∈ t /\ P s } + { forall s, s ∈ t -> ~ P s }.
      Proof.
        induction t as [ | s t IHt ] using bt_rect'; intros Ht.
        + right; intros ?; btm simpl.
        + destruct (Ht s) as [ H | H ]; btm simpl; auto.
          * left; exists s; btm simpl; auto.
          * destruct IHt as [ (x & H1 & H2) | H1 ].
            - intros x Hx; apply Ht; btm simpl.
            - left; exists x; btm simpl.
            - right; intros x; btm simpl.
              intros [ | ]; auto.
              contradict H; revert H; apply HP; auto.
      Qed.

    End btm_ex_dec.

    (** Univ. quantification of subsets *)

    Corollary btm_fa_dec (P : _ -> Prop) t : 
                             (forall s t, s ≈ t -> P s -> P t)
                          -> (forall x, x ∈ t -> { P x } + { ~ P x })
                          -> { s | s ∈ t /\ ~ P s } + { forall s, s ∈ t -> P s }.
    Proof.
      intros H1 H2.
      destruct btm_ex_dec with (P := fun x => ~ P x) (t := t)
        as [ H | H ]; auto.
      + intros u v G1 G2; contradict G2; revert G2; apply H1; auto.
      + intros x Hx; specialize (H2 _ Hx); tauto.
      + right; intros s Hs; specialize (H _ Hs).
        destruct (H2 _ Hs); tauto.
    Qed.

    (** Decidable separation *)

    Definition btm_select (P : _ -> Prop) t :
                             (forall s t, s ≈ t -> P s -> P t)
                          -> (forall x, x ∈ t -> { P x } + { ~ P x })
                          -> { s | forall x, x ∈ s <-> x ∈ t /\ P x }.
    Proof.
      intros HP0.
      induction t as [ | s t Ht ] using bt_rect'; intros HP.
      + exists ∅; intros s; btm simpl.
      + destruct Ht as (t' & H').
        * intros x Hx; apply HP; btm simpl.
        * destruct (HP s) as [ H | H ]; btm simpl; auto.
          - exists (s⪧t'); intros x; btm simpl.
            rewrite H'.
            split; try tauto.
            intros [ H1 | (H1 & H2) ]; auto.
            split; auto.
            revert H; apply HP0; auto.
          - exists t'; intros x; rewrite H'; btm simpl.
            split; try tauto.
            intros ([H1|H1] & H2); split; auto.
            contradict H; revert H2; apply HP0; auto.
    Qed.

    (** When x ∈ s, one can compute t st s = {x} U t /\ x ∉ t *)
  
    Definition btm_partition x s : x ∈ s -> { t | s ≈ x⪧t /\ x ∉ t }.
    Proof.
      induction s as [ | y s IHs ] using bt_rect'.
      + intros H; exfalso; revert H; btm simpl.
      + intros H; rewrite btm_inv in H.
        destruct (bte_dec x y) as [ H1 | H1 ]; 
        destruct (btm_dec x s) as [ H2 | H2 ]; try (exfalso; tauto). 
        * destruct (IHs H2) as (t & H3 & H4).
          exists t; split; auto.
          rewrite <- H1, H3; auto.
        * exists s; auto.
        * destruct (IHs H2) as (t & H3 & H4).
          exists (y⪧t); split; auto.
          - apply bte_trans with (y⪧x⪧t); auto.
          - contradict H4; revert H4; btm simpl.
    Qed.

  End more_decidability.

  Notation "∈-chain" := (chain (fun s t => s ∈ t)).
  Notation "∈-chain_list" := (chain_list (fun s t => s ∈ t)).

  Section bte_depth_and_chains.

    Opaque max.

    (** Well-foundness *)

    Fact bte_depth_eq s t : s ≈ t -> ⌞s⌟ = ⌞t⌟.
    Proof.
      induction 1; simpl; auto.
      + transitivity ⌞s⌟; auto.
      + rewrite max_assoc, max_idempotent; auto.
      + rewrite max_assoc, (max_comm (S _)), max_assoc; auto.
    Qed.

    Fact btm_depth s t : s ∈ t -> ⌞s⌟ < ⌞t⌟.
    Proof.
      intros H; apply bte_depth_eq in H. 
      rewrite <- H; simpl.
      apply lt_le_trans with (1 := lt_n_Sn _).
      apply le_max_l.
    Qed.

    (** bt is well-founded for ∈ *)

    Theorem btm_wf : well_founded (fun s t => s ∈ t).
    Proof.
      apply wf_incl with (1 := btm_depth),
            wf_inverse_image, lt_wf.
    Qed.

    Fact btm_chain_depth n s t : ∈-chain n s t -> n+⌞s⌟ <= ⌞t⌟.
    Proof.
      induction 1 as [ | n s t u H1 H2 IH2 ]; auto.
      apply le_trans with (2 := IH2).
      apply btm_depth in H1; lia.
    Qed.

    Fact btm_chain_congr_r n s t t' : t ≈ t' -> ∈-chain (S n)  s t -> ∈-chain (S n) s t'.
    Proof.
      intros H1 H2.
      apply chain_snoc_inv in H2.
      destruct H2 as (y & H2 & H3).
      apply chain_snoc with y; auto.
      revert H3; apply btm_congr_r; auto.
    Qed.

    Fact btm_chain_list_comp u l s t : l <> nil
                              -> ∈-chain_list l s t
                              -> ∈-chain_list l s (u⪧t).
    Proof.
      rewrite <- (rev_involutive l).
      generalize (rev l); clear l; intros l Hl.
      destruct l as [ | x l ].
      { destruct Hl; auto. }
      clear Hl.
      simpl; intros H.
      apply chain_list_app_inv in H.
      destruct H as (v & H1 & H2).
      apply chain_list_app with v; auto.
      apply chain_list_cons_inv in H2.
      destruct H2 as (-> & k & H2 & H3).
      apply chain_list_nil_inv in H3; subst k.
      constructor 2 with (u⪧t); auto.
      + btm simpl.
      + constructor.
    Qed.

    Fact btm_chain_comp n u s t : ∈-chain (S n) s t -> ∈-chain (S n) s (u⪧t).
    Proof.
      intros H.
      apply chain_chain_list in H.
      destruct H as (l & H1 & H2).
      rewrite H2. 
      apply chain_list_chain.
      apply btm_chain_list_comp; auto.
      destruct l; discriminate.
    Qed.

    Fact btm_depth_chain t : { l | ∈-chain_list l ∅ t /\ length l = ⌞t⌟ }.
    Proof.
      induction t as [ | s (ls & H1 & H2) t (lt & H3 & H4) ].
      + exists nil; simpl; split; auto; constructor.
      + destruct (le_lt_dec (S ⌞s⌟) ⌞t⌟) as [ H | H ].
        * exists lt; simpl; split.
          - apply btm_chain_list_comp; auto.
            destruct lt; try discriminate; simpl in *; lia.
          - rewrite max_r; auto.
        * exists (ls++s::nil); split.
          - apply chain_list_app with (1 := H1).
            constructor 2 with (s⪧t); auto; btm simpl.
            constructor; auto.
          - rewrite app_length; simpl.
            rewrite max_l; lia.
    Qed.

    Fact bt_chain_inv_0 n x : ∈-chain n x ∅ -> n = 0 /\ x = ∅.
    Proof.
      assert (forall y, ∈-chain n x y -> y = ∅ -> n = 0 /\ x = ∅) as H.
      { induction 1 as [ | n x y z H1 H2 IH2 ]; auto.
        intros ->; destruct IH2 as (_ & ->); auto.
        apply bte_discr in H1; tauto. }
      intros G; apply (H _ G); auto.
    Qed.

  End bte_depth_and_chains.

  (** Very important to build the finite HF-model 

      Up to ≈, membership in t is finite *)

  Theorem btm_finite_t t : { l | forall s, s ∈ t <-> exists s', s ≈ s' /\ In s' l }.
  Proof.
    induction t as [ | s (ls & Hs) t (lt & Ht) ].
    + exists nil; intros s; btm simpl; simpl; firstorder.
    + exists (s::lt); intros u; btm simpl; simpl.
      rewrite Ht; split.
      * intros [ H | (s' & H1 & H2) ].
        - exists s; auto.
        - exists s'; auto.
      * intros (s' & H1 & [ H2 | H2 ]); subst; auto.
        right; exists s'; auto.
  Qed.

  Notation "x ⊆ y" := (forall u, u ∈ x -> u ∈ y) (*at level 70*).

  Add Parametric Morphism: (fun x y => x ⊆ y) with signature 
       (bt_equiv) ==> (bt_equiv) ==> (iff) as bti_congr.
  Proof.
    intros x y H1 a b H2; split; intros H z.
    + rewrite <- H2, <- H1; apply H.
    + rewrite H1, H2; apply H.
  Qed.

  Fact bti_inv_0 x : x ⊆ ∅ <-> x = ∅.
  Proof.
    split; intros H; subst; auto.
    destruct x as [ | s t ]; auto.
    specialize (H s); revert H; btm simpl.
    intros []; auto.
  Qed.

  Fact bti_refl x : x ⊆ x.
  Proof. auto. Qed.

  Fact bti_trans x y z : x ⊆ y -> y ⊆ z -> x ⊆ z.
  Proof. intros H1 H2 k Hx; apply H2, H1; auto. Qed.

  Fact bti_comp s t : t ⊆ s⪧t.
  Proof. intro; rewrite btm_inv; auto. Qed.

  Fact bti_mono_r x s t : s ⊆ t -> x⪧s ⊆ x⪧t.
  Proof. intros ? ?; btm simpl; intros []; auto. Qed.

  Fact bte_bti s t : s ≈ t -> s ⊆ t.
  Proof. intros ? ?; apply btm_congr_r; auto. Qed.

  Fact btm_bti x s : x ∈ s -> x⪧s ⊆ s.
  Proof. intro; apply bte_bti; auto. Qed.

  Fact bti_congr_l x y t : x ≈ y -> x ⊆ t-> y ⊆ t.
  Proof.
    intros H1 H2 z Hz.
    apply H2; revert Hz; apply btm_congr_r; auto.
  Qed.

  Fact bti_congr_r x s t : s ≈ t -> x ⊆ s -> x ⊆ t.
  Proof.
    intros H1 H2 z Hz.
    generalize (H2 _ Hz); apply btm_congr_r; auto.
  Qed.

  Hint Resolve bti_refl bti_comp bti_mono_r.

  Lemma bti_dec s t : { s ⊆ t } + { ~ s ⊆ t }.
  Proof.
    destruct btm_fa_dec with (P := fun x => x ∈ t) (t := s)
      as [ (x & H1 & H2) | H1 ]; auto.
    + intros ? ?; apply btm_congr_l.
    + intros ? ?; apply btm_dec.
  Qed.

  (* I wonder whether the proof of this important result could
     be split 

     The proof can be done by generalising seteq.v
     to contraction under an equivalence (instead of @eq)
     This would avoid using decidable equality and would
     allow for the development of HF-Sets with UR-elements
     over a non-decidable type

   *)

  Lemma bti_equiv s t : s ⊆ t -> t ⊆ s -> s ≈ t.
  Proof.
    revert t; induction s as [ | x s Hs ] using bt_rect'.
    + intros t _ Ht.
      destruct t as [ | y t ]; auto.
      generalize (Ht y); btm simpl.
      intros []; auto.
    + induction t as [ | y _ t Ht ].
      * intros H _; generalize (H x).
        btm simpl; intros []; auto.
      * intros H1 H2.
        destruct (btm_dec x s) as [ H3 | H3 ].
        - apply bte_trans with s; auto.
          apply Hs.
          ++ apply bti_trans with (2 := H1); auto.
          ++ apply bti_trans with (1 := H2), btm_bti; auto.
        - assert (x ∈ y⪧t) as H4 by (apply H1; auto; btm simpl).
          destruct btm_partition with (1 := H4)
            as (u & H5 & H6).
          assert (s ≈ u) as H7.
          { apply Hs.
            + intros z Hz.
              assert (z ∈ x⪧u) as H7.
              { apply btm_congr_r with (1 := H5), H1, btm_inv; auto. }
              apply btm_inv in H7; destruct H7 as [ H7 | ]; auto.
              contradict H3; revert Hz; apply btm_congr_l; auto.
            + intros z Hz.
              assert (z ∈ x⪧s) as H7.
              { apply H2, btm_congr_r with (1 := in_bte_sym H5), btm_inv; auto. }
              apply btm_inv in H7; destruct H7 as [ H7 | ]; auto.
              contradict H6; revert Hz; apply btm_congr_l; auto. }
          apply bte_trans with (x⪧u); auto.
  Qed.

  Fact bte_incl_equiv s t : s ≈ t <-> s ⊆ t /\ t ⊆ s.
  Proof.
    split.
    + intro; split; apply bte_bti; auto.
    + intros []; apply bti_equiv; auto.
  Qed.

  Fact bte_ext s t : s ≈ t <-> forall x, x ∈ s <-> x ∈ t.
  Proof. rewrite bte_incl_equiv; firstorder. Qed.

  Fact bti_inv x s t : x ⊆ s⪧t <-> x ⊆ t \/ exists y, y ⊆ t /\ x ≈ s⪧y.
  Proof.
    split.
    + intros H.
      destruct (btm_dec s x) as [ H1 | H1 ].
      * destruct btm_partition with (1 := H1)
          as (y & H2 & H3).
        right; exists y; split; auto.
        intros z Hz.
        assert (z ∈ s⪧t) as C.
        { apply H.
          apply btm_congr_r with (1 := in_bte_sym H2), btm_inv; auto. }
        apply btm_inv in C; destruct C as [C|]; auto.
        contradict H3; revert Hz; apply btm_congr_l; auto.
      * left.
        intros y Hy.
        specialize (H _ Hy).
        apply btm_inv in H.
        destruct H as [ H | ]; auto.
        contradict H1.
        revert Hy; apply btm_congr_l; auto.
    + intros [ H | (y & H1 & H2) ].
      * apply bti_trans with (1 := H); auto.
      * intros z Hz.
        apply bti_congr_r with (1 := H2) in Hz; auto.
        revert Hz; btm simpl; intros []; auto.
  Qed.

  (** Set union *)

  Fixpoint bt_cup s t := 
    match s with 
      | ∅   => t
      | x⪧s => x⪧(s ∪ t)
    end
  where "s ∪ t" := (bt_cup s t).

  Theorem bt_cup_spec x s t : x ∈ s ∪ t <-> x ∈ s \/ x ∈ t.
  Proof.
    revert x; induction s as [ | y s Hs ] using bt_rect'; 
      intros x; simpl; btm simpl.
    rewrite Hs; tauto.
  Qed.

  Fact bt_cup_left s t : s ⊆ s ∪ t.
  Proof. intro; rewrite bt_cup_spec; auto. Qed.

  Fact bt_cup_right s t : t ⊆ s ∪ t.
  Proof. intro; rewrite bt_cup_spec; auto. Qed.

  Hint Resolve bt_cup_left bt_cup_right.

  Fact bt_cup_mono s s' t t' : s ≈ s' -> t ≈ t' -> s ∪ t ≈ s' ∪ t'.
  Proof.
    do 3 rewrite bte_ext; intros H1 H2 x.
    do 2 rewrite bt_cup_spec.
    rewrite H1, H2; tauto.
  Qed.

  Add Parametric Morphism: (bt_cup) with signature 
       (bt_equiv) ==> (bt_equiv) ==> (bt_equiv) as bt_cup_congr.
  Proof.
    intros; apply bt_cup_mono; auto.
  Qed.
 
  Fact bt_cup_incl s t x : s ∪ t ⊆ x <-> s ⊆ x /\ t ⊆ x.
  Proof.
    split.
    + intros H; split; apply bti_trans with (2 := H); auto.
    + intros [] z; rewrite bt_cup_spec; intros []; auto.
  Qed.
   
  (** We compute the transitive closure *)

  Definition bt_transitive t := forall u v, u ∈ v -> v ∈ t -> u ∈ t.

  Fixpoint bt_tc t := 
    match t with 
      | ∅   => ∅
      | s⪧t => s⪧(↓s ∪ ↓t)
    end
  where "↓ t" := (bt_tc t).

  Fact bt_tc_congr_l u v t : u ≈ v -> u ∈ ↓t -> v ∈ ↓t.
  Proof.
    revert u v; induction t using bt_rect'; simpl; intros ? ? ?; apply btm_congr_l; auto.
  Qed.

  Fact bt_tc_congr_r u s t : s ≈ t -> u ∈ ↓s <-> u ∈ ↓t.
  Proof.
    intros H; revert H u. 
    induction 1 as [ | s t | r s t H1 IH1 H2 IH2 | s t | s t u 
                   | s s' t t' H1 IH1 H2 IH2 ]; intros v; try tauto.
    + symmetry; auto.
    + rewrite IH1; auto.
    + simpl; repeat (btm simpl || rewrite bt_cup_spec); tauto.
    + simpl; repeat (btm simpl || rewrite bt_cup_spec); tauto.
    + simpl; repeat (btm simpl || rewrite bt_cup_spec).
      rewrite IH1, IH2; split; intros [ H | [] ]; auto; left.
      * apply bte_trans with s; auto.
      * apply bte_trans with s'; auto.
  Qed.

  Add Parametric Morphism: (bt_tc) with signature 
       (bt_equiv) ==> (bt_equiv) as bt_tc_congr.
  Proof.
    intros; apply bte_ext; intro; apply bt_tc_congr_r; auto.
  Qed.
 
  (** The transitive closure is composed of the x st x ∈ ... ∈ t *)

  Theorem bt_tc_spec t x : x ∈ ↓t <-> exists n, ∈-chain (S n) x t.
  Proof.
    revert x; induction t as [ | s Hs t Ht ]; intros x; simpl.
    + btm simpl; split; try tauto.
      intros (n & Hn).
      apply chain_inv_S in Hn.
      destruct Hn as (y & H1 & H2).
      apply bt_chain_inv_0 in H2.
      destruct H2 as (_ & ->).
      apply bte_discr in H1; tauto.
    + rewrite btm_inv, bt_cup_spec, Hs, Ht.
      split.
      * intros [ H | [ (n & H) | (n & H) ] ].
        - exists 0.
          constructor 2 with (s⪧t).
          ++ btm simpl.
          ++ constructor.
        - exists (S n).
          apply chain_snoc with s; auto; btm simpl.
        - exists n; apply btm_chain_comp; auto.
      * intros (n & H).
        apply chain_snoc_inv in H.
        destruct H as (y & H1 & H2).
        apply btm_inv in H2.
        destruct H2 as [ H2 | H2 ].
        - destruct n as [ | n ].
          ++ apply chain_inv_0 in H1; subst; auto.
          ++ right; left; exists n.
             revert H1; apply btm_chain_congr_r; auto.
        - right; right; exists n.
          apply chain_snoc with y; auto.
  Qed.

  Fact bt_tc_incr t : t ⊆ ↓t.
  Proof.
    intro; induction t; simpl; auto; btm simpl.
    rewrite bt_cup_spec; tauto.
  Qed.

  Fact bt_tc_mono s t : s ⊆ t -> ↓s ⊆ ↓t.
  Proof.
    intros H x.
    do 2 rewrite bt_tc_spec.
    intros (n & Hn).
    apply chain_snoc_inv in Hn.
    destruct Hn as (y & H1 & H2).
    exists n; apply chain_snoc with y; auto.
  Qed.

  Hint Resolve bt_tc_incr bt_tc_mono.
 
  Theorem bt_tc_trans t : bt_transitive ↓t.
  Proof.
    induction t as [ | s Hs t Ht ]; simpl; intros u v H1; btm simpl; intros H2.
    rewrite bt_cup_spec in H2.
    rewrite bt_cup_spec.
    destruct H2 as [ H2 | [ H2 | H2 ] ].
    + right; left; apply bt_tc_congr_r with (1 := H2); auto.
    + right; left; revert H2; apply Hs; auto.
    + right; right; revert H2; apply Ht; auto.
  Qed.

  Hint Resolve bt_tc_trans.

  Fact bt_trans_chain n x y t : bt_transitive t -> ∈-chain n x y -> y ∈ t -> x ∈ t. 
  Proof.
    intros Ht; induction 1 as [ | n x y z H1 H2 IH2 ]; auto.
    intros H; apply Ht with (1 := H1); auto.
  Qed.

  Hint Resolve bt_trans_chain.

  Fact bt_tc_idem t : ↓(↓t) ⊆ ↓t.
  Proof.
    intros x; rewrite bt_tc_spec.
    intros (n & Hn).
    apply chain_snoc_inv in Hn.
    destruct Hn as (y & H1 & H2).
    revert H1 H2.
    apply bt_trans_chain; auto.
  Qed.

  (*  (** Is this really needed *)
 
  Fixpoint bt_bcup x t :=
    match t with
      | ∅   => ∅ 
      | s⪧t => (x⪧s) ∪ (bt_bcup x t)
    end.

  Fact bt_bcup_spec x t u : u ∈ bt_bcup x t <-> exists k, u ∈ x⪧k /\ k ∈ t.
  Proof.
    revert u; induction t as [ | s t Ht ] using bt_rect'; intros u; simpl.
    + rewrite btm_inv_0; split; try tauto.
      intros (k & _ & Hk); revert Hk; rewrite btm_inv_0; auto.
    + rewrite btm_inv, bt_cup_spec; split.
      * intros [ H | [ H | H ] ].
        - exists s; split; auto.
          apply btm_congr_l with x; auto.
        - exists s; split; auto.
        - rewrite Ht in H.
          destruct H as (k & ? & ?).
          exists k; split; auto.
      * intros (k & H1 & H2); revert H1 H2.
        rewrite btm_inv, btm_inv.
        intros [H1|H1] [H2|H2]; auto.
        - right; left; revert H1; apply btm_congr_r; auto.
        - right; right; apply Ht; exists k.
          rewrite btm_inv; auto.
  Qed.

  *)

  (** Computes x {t1,...,tk} => {{x} ∪ t1,...,{x} ∪ tk **)

  Fixpoint bt_mcomp x t :=
    match t with
      | ∅   => ∅ 
      | s⪧t => (x⪧s) ⪧ (bt_mcomp x t)
    end.

  Fact bt_mcomp_spec x t u : u ∈ bt_mcomp x t <-> exists k, k ∈ t /\ u ≈ x⪧k.
  Proof.
    revert u; induction t as [ | s t Ht ] using bt_rect'; intros u; simpl.
    + rewrite btm_inv_0; split; try tauto.
      intros (k & Hk & _); revert Hk; rewrite btm_inv_0; auto.
    + rewrite btm_inv; split.
      * intros [ H | H ].
        - exists s; split; auto; btm simpl.
        - rewrite Ht in H.
          destruct H as (k & ? & ?).
          exists k; split; auto.
      * intros (k & H1 & H2); revert H1 H2.
        rewrite btm_inv, Ht.
        intros [H2|H2] H1; auto.
        - left; apply bte_trans with (1 := H1); auto.
        - right; exists k; auto.
  Qed.

  (** Powerset bti_inv x ⊆ s⪧t <-> x ⊆ t \/ exists y, y ⊆ t /\ x ≈ s⪧y *)

  Fixpoint bt_pow t :=
    match t with
      | ∅   => ∅⪧∅ 
      | x⪧t => bt_pow t ∪ bt_mcomp x (bt_pow t)
    end.

  Fact bt_pow_spec t x : x ∈ bt_pow t <-> x ⊆ t.
  Proof.
    revert x; induction t as [ | s t Ht ] using bt_rect'; intros x; simpl.
    + rewrite btm_inv, btm_inv_0, bti_inv_0, bte_inv_0; tauto.
    + rewrite bti_inv, bt_cup_spec, bt_mcomp_spec, Ht.
      split; intros [ | (y & H) ]; auto; right; exists y; 
        revert H; rewrite Ht; auto.
  Qed.

  (** Powerset of transitive is transitive *)

  Fact bt_pow_transitive t : bt_transitive t -> bt_transitive (bt_pow t).
  Proof.
    intros H x y H1.
    do 2 rewrite bt_pow_spec.
    intros H2 z Hz.
    apply H2 in H1.
    revert Hz H1; apply H.
  Qed.

  Fact bt_pow_trans_incl t : bt_transitive t -> t ⊆ bt_pow t.
  Proof.
    intros Ht.
    intros x Hx.
    apply bt_pow_spec; intros y Hy.
    revert Hx; apply Ht; auto.
  Qed.

  Fact bt_pow_iter_trans t n : bt_transitive t -> bt_transitive (iter bt_pow t n)
                                               /\ t ⊆ iter bt_pow t n.
  Proof.
    revert t; induction n as [ | n IHn ]; simpl; intros t Ht; auto; split.
    + apply IHn, bt_pow_transitive; auto.
    + destruct (IHn _ (bt_pow_transitive Ht)) as [ _ H ].
      apply bti_trans with (2 := H), bt_pow_trans_incl; auto.
  Qed.

  Fact bt_pow_iter_mono t t' n : t ⊆ t' -> iter bt_pow t n ⊆ iter bt_pow t' n.
  Proof.
    revert t t'; induction n as [ | n IHn ]; simpl; auto; intros t t' H.
    apply IHn; intro; do 2 rewrite bt_pow_spec.
    intro; apply bti_trans with t; auto.
  Qed.
 
  Fact bt_pow_iter_le t n m : n <= m -> bt_transitive t -> iter bt_pow t n ⊆ iter bt_pow t m.
  Proof.
    intros H; revert H t.
    induction 1 as [ | m Hm IHm ]; auto; intros t Ht.
    apply bti_trans with (1 := IHm _ Ht); simpl.
    apply bt_pow_iter_mono, bt_pow_trans_incl; auto.
  Qed.

  (** We start workin with pairs *)

  Fact bt_sg_inv x y : x⪧∅ ≈ y⪧∅ <-> x ≈ y.
  Proof.
    split; auto.
    rewrite bte_ext.
    intros H; specialize (H x).
    do 2 rewrite btm_inv, btm_inv_0 in H.
    apply proj1 in H; destruct H; try tauto; auto.
  Qed.

  Fact bt_sg_db_inv a x y : a⪧∅ ≈ x⪧y⪧∅ <-> a ≈ x /\ a ≈ y.
  Proof.
    split.
    + intros H.
      rewrite bte_ext in H.
      generalize (proj2 (H x)) (proj2 (H y)).
      btm simpl; intros [|[]] [|[]]; auto.
    + intros [].
      apply bte_trans with (a⪧a⪧∅); auto.
  Qed.

  Fact bt_db_inv a b x y : a⪧b⪧∅ ≈ x⪧y⪧∅ <-> a ≈ x /\ b ≈ x /\ x ≈ y
                                          \/ a ≈ x /\ b ≈ y
                                          \/ a ≈ y /\ b ≈ x.
  Proof.
    split.
    + intros H.
      rewrite bte_ext in H.
      generalize (proj1 (H a)) (proj1 (H b)) (proj2 (H x)) (proj2 (H y)).
      btm simpl; intros [|[|[]]] [|[|[]]] [|[|[]]] [|[|[]]]; auto.
    + intros [ (H1&H2&H3) | [ (H1&H2) | (H1&H2) ] ]; auto.
      * do 2 (apply in_bte_cngr; auto).
        apply bte_trans with x; auto.
      * apply bte_trans with (1 := in_bte_comm _ _ _).
        do 2 (apply in_bte_cngr; auto).
  Qed.

  (** pairs   (x,y) = { {x},{x,y} } *)

  Definition bt_pair s t := (s⪧∅)⪧(s⪧t⪧∅)⪧∅.

  Notation "⟬ s , t ⟭" := (bt_pair s t).

  Fact bt_pair_spec x s t : x ∈ ⟬ s,t⟭ <-> x ≈ s⪧∅ \/ x ≈ s⪧t⪧∅.
  Proof. unfold bt_pair; btm simpl. Qed.

  Fact bt_pair_equiv s t s' t' : ⟬s,t⟭ ≈⟬s',t'⟭  <-> s≈s' /\ t≈t'.
  Proof.
    split.
    2: intros []; unfold bt_pair; auto.
    intros H; rewrite bte_ext in H.
    assert (forall x, (x ≈ s⪧∅ \/ x ≈ s⪧t⪧∅) <-> (x ≈ s'⪧∅ \/ x ≈ s'⪧t'⪧∅)) as H'.
    { intros x; generalize (H x); do 2 rewrite bt_pair_spec; tauto. }
    clear H; revert H'; intros H.
    generalize (proj1 (H _) (or_introl (in_bte_refl _))) 
               (proj1 (H _) (or_intror (in_bte_refl _)))
               (proj2 (H _) (or_introl (in_bte_refl _))) 
               (proj2 (H _) (or_intror (in_bte_refl _))).
    repeat rewrite bt_db_inv.
    do 2 rewrite (bte_sym (_⪧_⪧_)).
    repeat rewrite bt_sg_inv.
    repeat rewrite bt_sg_db_inv.
    intros.
    repeat match goal with 
      | H : _ /\ _ |- _ => destruct H
      | H : _ \/ _ |- _ => destruct H
    end; split; auto; 
    try (apply bte_trans with s); auto;
    try (apply bte_trans with s'); auto.
  Qed.

  Add Parametric Morphism: (bt_pair) with signature 
       (bt_equiv) ==> (bt_equiv) ==> (bt_equiv) as bt_pair_congr.
  Proof.
    intros; apply bt_pair_equiv; auto.
  Qed.

  (** FOL encoding a triples belonging to a set *)
 
  Fact bt_enc_equiv s t : s ≈ t <-> forall x, x ∈ s <-> x ∈ t.
  Proof. apply bte_ext. Qed.

  Fact bt_enc_empty s : s ≈ ∅ <-> forall x, ~ x ∈ s.
  Proof.
    rewrite bte_ext; apply forall_equiv; intro; btm simpl.
  Qed.

  Fact bt_enc_sg s t : s ≈ t⪧∅ <-> forall x, x ∈ s <-> x ≈ t.
  Proof.
    rewrite bte_ext; apply forall_equiv; intro; btm simpl.
  Qed.

  Fact bt_enc_db u s t : u ≈ s⪧t⪧∅ <-> forall x, x ∈ u <-> x ≈ s \/ x ≈ t.
  Proof.
    rewrite bte_ext; apply forall_equiv; intros; btm simpl.
  Qed.
 
  Fact bt_enc_pair p s t : p ≈ ⟬s,t⟭  <-> (forall x, x ∈ p <-> x ≈ s⪧∅ \/ x ≈ s⪧t⪧∅).
  Proof.
    rewrite bte_ext; apply forall_equiv; intro.
    rewrite bt_pair_spec; tauto.
  Qed.

  Fact bt_enc_triple p r s t : p ≈ ⟬r,⟬s,t⟭⟭   <-> exists a, p ≈ ⟬r,a⟭ /\ a ≈ ⟬s,t⟭ .
  Proof.
    split.
    + exists ⟬s,t⟭; auto.
    + intros (a & H1 & H2).
      apply bte_trans with (1 := H1).
      apply bt_pair_equiv; auto.
  Qed.

  Fact bt_enc_rel3 a b c t : ⟬a,⟬b,c⟭⟭  ∈ t <-> exists p, p ≈ ⟬a,⟬b,c⟭⟭ /\ p ∈ t.
  Proof.
    split.
    + exists ⟬a,⟬b,c⟭⟭ ; auto.
    + intros (p & H1 & H2).
      revert H2; apply btm_congr_l; auto.
  Qed.

  Fixpoint tuple (l : list bt) :=
    match l with 
      | nil  => ∅ 
      | x::l => ⟬x,tuple l⟭
    end.

  Fact bt_enc_tuple_0 p : p ≈ tuple nil <-> p ≈ ∅.
  Proof. simpl; tauto. Qed.

  Fact bt_enc_tuple p x l : p ≈ tuple (x::l) <-> exists a, p ≈ ⟬x,a⟭ /\ a ≈ tuple l.
  Proof.
    simpl; split.
    + exists (tuple l); auto; split; auto.
    + intros (a & H1 & H2).
      apply bte_trans with (1 := H1).
      apply bt_pair_equiv; auto.
  Qed.

  Fact btm_pair_PP x y t : x ∈ t -> y ∈ t -> ⟬x,y⟭  ∈ bt_pow (bt_pow t).
  Proof.
    rewrite bt_pow_spec.
    intros Hx Hy p.
    rewrite bt_pair_spec.
    intros [H|H]; apply bte_sym in H;
    apply btm_congr_l with (1 := H); apply bt_pow_spec.
    + intros z; btm simpl; intros [ Hz | [] ].
      revert Hx; apply btm_congr_l; auto.
    + intros z; btm simpl; intros [ Hz | [ Hz | [] ] ];
        [ revert Hx | revert Hy ]; apply btm_congr_l; auto.
  Qed.

  Fixpoint bt_level (t : bt) :=
    match t with
      | ∅   => ∅
      | a⪧t => (a⪧∅)⪧(bt_level t)
    end.

  Fact bt_level_spec x t : x ∈ bt_level t <-> exists a, a ∈ t /\ x ≈ a⪧∅.
  Proof.
    revert x; induction t as [ | a t IHt ] using bt_rect'; intros x; simpl; btm simpl.
    + split; try tauto; intros (a & H & _); revert H; btm simpl.
    + rewrite IHt; split.
      * intros [ H | (b & H1 & H2) ].
        - exists a; auto; btm simpl.
        - exists b; auto.
      * intros (b & H1 & H2); revert H1; btm simpl.
        intros [ H | H ].
        - left; apply bte_trans with (1 := H2); auto.
        - right; exists b; auto.
  Qed.

  Fact bt_level_empty t : ∅ ∉ bt_level t.
  Proof.
    rewrite bt_level_spec.
    intros (a & _ & H).
    apply bte_sym, bte_discr in H; auto.
  Qed.

  Fact bt_level_inv_incl t1 t2 : bt_level t1 ⊆ bt_level t2 -> t1 ⊆ t2.
  Proof.
    intros H x Hx.
    specialize (H (x⪧∅)).
    do 2 rewrite bt_level_spec in H.
    destruct H as (a & H1 & H2).
    { exists x; auto. }
    rewrite bt_sg_inv in H2.
    revert H1; apply btm_congr_l; auto.
  Qed.

  Fact bt_level_inj t1 t2 : bt_level t1 ≈ bt_level t2 -> t1 ≈ t2.
  Proof.
    do 2 rewrite bte_incl_equiv.
    intros []; split; apply bt_level_inv_incl; auto.
  Qed.

  Fixpoint pos_embed_bt n (p : pos n) : bt :=
    match p with
      | pos0      => ∅
      | pos_nxt q => ∅⪧(bt_level (pos_embed_bt q))
    end.

  Fact pos_embed_bt_inj n (p q : pos n) : pos_embed_bt p ≈ pos_embed_bt q -> p = q.
  Proof.
    revert q; induction p as [ n | n p Hp ]; intros q; invert pos q; auto.
    + intros H; apply bte_sym, bte_discr in H; tauto.
    + intros H; apply bte_discr in H; tauto.
    + intros H.
      f_equal; apply Hp, bt_level_inj.
      apply bte_ext.
      rewrite bte_ext in H.
      intros x; split; intros Hx.
      * specialize (proj1 (H x)); btm simpl.
        intros [ H1 | H1 ]; auto.
        contradict Hx.
        generalize (bt_level_empty (pos_embed_bt p)).
        intros G1 G2; apply G1; revert G2.
        apply btm_congr_l; auto.
      * specialize (proj2 (H x)); btm simpl.
        intros [ H1 | H1 ]; auto.
        contradict Hx.
        generalize (bt_level_empty (pos_embed_bt q)).
        intros G1 G2; apply G1; revert G2.
        apply btm_congr_l; auto.
  Qed.

  (** We have an embedding of pos n into bt *)

  Theorem pos_embed_bt_spec n (p q : pos n) : pos_embed_bt p ≈ pos_embed_bt q <-> p = q.
  Proof.
    split.
    + apply pos_embed_bt_inj.
    + intros []; auto.
  Qed.

  Check t.

  Definition list2bt := fold_right (fun x y => x⪧y) ∅.

  Fact list2bt_spec l x : x ∈ list2bt l <-> exists y, x ≈ y /\ In y l.
  Proof.
    revert x; induction l as [ | x l IHl ]; intros y; simpl; btm simpl.
    + split; try tauto; intros (_ & _ & []).
    + rewrite IHl; split.
      * intros [ H | (z & H1 & H2) ].
        - exists x; auto.
        - exists z; split; auto.
      * intros (z & H1 & [ -> | H2 ]); auto.
        right; exists z; auto.
  Qed.
  
  Definition bt_card n := list2bt (map (@pos_embed_bt _) (pos_list n)).

  Fact bt_card_spec n x : x ∈ bt_card n <-> exists p, x ≈ @pos_embed_bt n p.
  Proof.
    unfold bt_card; rewrite list2bt_spec; split.
    + intros (y & H1 & H2); revert H2; rewrite in_map_iff.
      intros (p & <- & _); exists p; auto.
    + intros (p & Hp).
      exists (pos_embed_bt p); split; auto.
      apply in_map_iff; exists p; split; auto.
      apply pos_list_prop.
  Qed.

  Fact bt_card_spec_t n x : x ∈ bt_card n -> { p | x ≈ @pos_embed_bt n p }.
  Proof.
    intros Hx; generalize (proj1 (bt_card_spec _ _) Hx).
    apply pos_dec_reif.
    intro; apply bte_dec.
  Qed.

  Definition bt_card_surj n x Hx := proj1_sig (@bt_card_spec_t n x Hx).
 
  Fact bt_card_surj_spec n x Hx : x ≈ pos_embed_bt (@bt_card_surj n x Hx).
  Proof. apply (proj2_sig (@bt_card_spec_t n x Hx)). Qed.

  Definition hfs : Set := sig (fun t => bt_norm t = t).

  Definition bt_cls (t : bt) : hfs.
  Proof. exists (bt_norm t); apply bt_norm_idem. Defined.

  Arguments bt_cls t /.

  Definition hfs_repr (s : hfs) := proj1_sig s.

  Fact bt_norm_exist x y (E : x = y) (H1 : bt_norm x = x) (H2 : bt_norm y = y) : exist _ x H1 = exist _ y H2 :> hfs.
  Proof. subst; f_equal; apply bt_eq_pirr. Qed.

  Fact bt_cls_hfs_repr s : bt_cls (hfs_repr s) = s.
  Proof.
    destruct s as (t & Ht); simpl.
    apply bt_norm_exist, Ht.
  Qed.
  
  Fact hfs_repr_bt_cls t : hfs_repr (bt_cls t) ≈ t.
  Proof. apply bt_norm_eq. Qed.

  Notation cls := bt_cls.
  Notation repr := hfs_repr.

  Fact bt_cls_eq_norm s t : bt_cls s = bt_cls t <-> bt_norm s = bt_norm t.
  Proof.
    simpl; split.
    + inversion 1; auto.
    + intro; apply bt_norm_exist; auto.
  Qed.

  Fact bt_cls_equiv s t : bt_cls s = bt_cls t <-> s ≈ t.
  Proof.
    rewrite bt_cls_eq_norm; split; apply bte_norm_iff.
  Qed.

  Fact bt_cls_hfs_repr_iff t s : cls t = s <-> t ≈ repr s.
  Proof.
    rewrite <- (bt_cls_hfs_repr s) at 1.
    apply bt_cls_equiv.
  Qed.

  Definition hfs_eq_dec : forall (s t : hfs), { s = t } + { s <> t }.
  Proof.
    intros (s & Hs) (t & Ht).
    destruct (bt_eq_dec s t) as [ H | H ].
    + left; subst; f_equal; apply bt_eq_pirr.
    + right; contradict H; inversion H; auto.
  Qed.

  Definition hfs_mem s t := bt_mem (repr s) (repr t). 
 
  Infix "∈" := hfs_mem.

  Arguments hfs_mem s t /.

  Fact btm_cls_repr t s : cls t ∈ s <-> bt_mem t (repr s).
  Proof.
    generalize (bt_norm_eq t). 
    simpl; split; apply btm_congr_l; auto.
  Qed.

  Fact btm_repr_cls t s : t ∈ cls s <-> bt_mem (repr t) s.
  Proof.
    generalize (bt_norm_eq s). 
    simpl; split; apply btm_congr_r; auto.
  Qed.

  Fact hfs_mem_btm s t : cls s ∈ cls t <-> bt_mem s t.
  Proof. rewrite btm_repr_cls, hfs_repr_bt_cls; tauto. Qed.

  Fact hfs_mem_repr s t : s ∈ t <-> bt_mem (repr s) (repr t).
  Proof. tauto. Qed.
   
  Fact hfs_mem_ext s t : s = t <-> forall x, x ∈ s <-> x ∈ t.
  Proof.
    rewrite <- (bt_cls_hfs_repr s), <- (bt_cls_hfs_repr t), bt_cls_equiv; simpl.
    rewrite bte_ext; split; intros H.
    + revert s t H; intros (s & Hs) (t & Ht) H (x & Hx); simpl in *.
      rewrite Hs, Ht; auto.
    + revert s t H; intros (s & Hs) (t & Ht) H x; simpl in *.
      rewrite Hs, Ht in H.
      specialize (H (bt_cls x)).
      rewrite (hfs_repr_bt_cls x) in H; auto.
  Qed.

  Fact hfs_mem_fin_t t : fin_t (fun s => s ∈ t).
  Proof.
    destruct (btm_finite_t (repr t)) as (l & Hl).
    exists (map cls l).
    intros x; simpl; rewrite Hl, in_map_iff; split.
    + intros (s & H1 & H2).
      exists s; split; auto.
      rewrite bt_cls_hfs_repr_iff; auto.
    + intros (s & H1 & H2).
      exists s; split; auto.
      rewrite bt_cls_hfs_repr_iff in H1; auto.
  Qed.

  Fact hfs_mem_dec : forall s t, { s ∈ t } + { ~ s ∈ t }.
  Proof.
    intros (s & ?) (t & ?); simpl; apply btm_dec.
  Qed.

  Definition hfs_empty : hfs := exist _ ∅ eq_refl.

  Fact hfs_empty_prop : forall x, ~ x ∈ hfs_empty.
  Proof. 
    intros (x & ?); simpl; btm simpl.
  Qed.

  Fact hfs_empty_spec x : x ∈ hfs_empty <-> False.
  Proof.
    split; try tauto; apply hfs_empty_prop.
  Qed.

  Definition hfs_cons x t := cls ((repr x)⪧(repr t)).
  
  Fact hfs_cons_spec y x t : y ∈ hfs_cons x t <-> y = x \/ y ∈ t.
  Proof.
    unfold hfs_cons.
    rewrite btm_repr_cls; btm simpl.
    apply (fol_bin_sem_ext fol_disj).
    + rewrite <- bt_cls_hfs_repr_iff, bt_cls_hfs_repr; tauto.
    + tauto.
  Qed.

  Opaque hfs_empty hfs_cons hfs_mem.

  Theorem hfs_comprehension X (P : X -> Prop) (f : X -> hfs) : 
            fin_t P 
         -> { s | forall a, a ∈ s <-> exists x, P x /\ f x = a }.
  Proof.
    intros (l & Hl).
    assert { s | forall a, a ∈ s <-> exists x, In x l /\ f x = a } as H.
    { exists (fold_right (fun x => hfs_cons (f x)) hfs_empty l).
      clear Hl; intros a.
      induction l as [ | x l IHl ]; simpl.
      + rewrite hfs_empty_spec; split; try tauto.
        intros (? & [] & _).
      + rewrite hfs_cons_spec, IHl; split.
        * intros [ -> | (y & ? & <-) ].
          - exists x; auto.
          - exists y; auto.
        * intros (y & [ -> | ? ] & <-); auto.
          right; exists y; auto. }
    destruct H as (s & Hs).
    exists s; intro a; rewrite Hs.
    apply exists_equiv; intro; rewrite Hl; tauto.
  Qed.

  (** This is the decidable comprehension *)  

  Fact hfs_select t (P : hfs -> Prop) : 
           (forall x, x ∈ t -> { P x } + { ~ P x })
        -> { s | forall x, x ∈ s <-> x ∈ t /\ P x }.
  Proof.
    intros H.
    destruct btm_select with (P := fun x => P (cls x)) (t := repr t)
      as (s & Hs).
    + intros x y E.
      apply bt_cls_equiv in E.
      rewrite E; auto.
    + intros x Hx.
      apply H, btm_cls_repr; auto.
    + exists (bt_cls s); intros x.
      rewrite btm_repr_cls, Hs, bt_cls_hfs_repr; tauto.
  Qed.

  Check t.

  Definition hfs_pow t := cls (bt_pow (repr t)).

  Notation "x ⊆ y" := (forall u, u ∈ x -> u ∈ y).

  Fact hfs_incl_refl r : r ⊆ r.
  Proof. apply m2_incl_refl. Qed.

  Fact hfs_incl_trans r s t : r ⊆ s -> s ⊆ t -> r ⊆ t.
  Proof. apply m2_incl_trans. Qed.

  Fact hfs_incl_ext s t : s = t <-> s ⊆ t /\ t ⊆ s.
  Proof.
    split.
    + intros []; auto.
    + rewrite hfs_mem_ext; intros []; split; auto.
  Qed.
   
  Fact hfs_pow_spec s x : x ∈ hfs_pow s <-> x ⊆ s.
  Proof.
    unfold hfs_pow.
    rewrite btm_repr_cls, bt_pow_spec.
    split.
    + intros H z Hz. 
      rewrite <- (bt_cls_hfs_repr z).
      apply btm_cls_repr, H; auto.
    + intros H z.
      specialize (H (cls z)).
      do 2 rewrite btm_cls_repr in H; auto.
  Qed.

  Definition hfs_transitive t := forall u v, u ∈ v -> v ∈ t -> u ∈ t.

  Fact bt_hfs_transitive t : hfs_transitive t <-> bt_transitive (repr t).
  Proof.
    split.
    + intros H u v G.
      do 2 rewrite <- btm_cls_repr.
      apply H.
      rewrite btm_cls_repr, hfs_repr_bt_cls; auto.
    + intros H u v G.
      do 2 rewrite hfs_mem_repr.
      apply H; auto.
  Qed.
  
  Definition hfs_tc t := cls (bt_tc (repr t)).

  Fact hfs_tc_trans t : hfs_transitive (hfs_tc t).
  Proof.
    intros u v; unfold hfs_tc.
    do 2 rewrite btm_repr_cls.
    rewrite hfs_mem_repr.
    apply bt_tc_trans.
  Qed.

  Fact hfs_tc_incl t : t ⊆ hfs_tc t.
  Proof.
    unfold hfs_tc.
    intros x Hx.
    rewrite btm_repr_cls.
    apply bt_tc_incr; auto.
  Qed.

  Fact hfs_pow_trans t : hfs_transitive t -> hfs_transitive (hfs_pow t).
  Proof.
    unfold hfs_pow; intros H u v.
    do 2 rewrite btm_repr_cls.
    rewrite hfs_mem_repr.
    apply bt_pow_transitive.
    apply bt_hfs_transitive; auto.
  Qed.

  Definition hfs_card n := cls (bt_card n).

  Definition hfs_pos n (p : pos n) := cls (pos_embed_bt p).
  
  Fact hfs_pos_card n x : x ∈ hfs_card n <-> exists p, x = @hfs_pos n p.
  Proof.
    unfold hfs_pos, hfs_card.
    rewrite btm_repr_cls, bt_card_spec.
    apply exists_equiv; intros p.
    rewrite <- bt_cls_equiv, bt_cls_hfs_repr; tauto.
  Qed.

  Definition hfs_card_pos n x : x ∈ hfs_card n -> pos n.
  Proof.
    intros H.
    apply (@bt_card_surj n (repr x)).
    rewrite <- btm_repr_cls; assumption.
  Defined.

  Fact hfs_card_pos_spec n x Hx : x = hfs_pos (@hfs_card_pos n x Hx).
  Proof.
    unfold hfs_card_pos, hfs_pos.
    symmetry; rewrite bt_cls_hfs_repr_iff.
    rewrite <- bt_card_surj_spec; auto.
  Qed.

  Fact hfs_pos_inj n p q : @hfs_pos n p = hfs_pos q -> p = q.
  Proof.
    unfold hfs_pos.
    rewrite bt_cls_equiv.
    apply pos_embed_bt_inj.
  Qed.

  Fact hfs_card_pos_pirr n x H1 H2 : @hfs_card_pos n x H1 = @hfs_card_pos n x H2.
  Proof. apply hfs_pos_inj; do 2 rewrite <- hfs_card_pos_spec; auto. Qed.

  (** There is a surjective map from some t to pos n *)

  Fact hfs_surj_t n : { t & { s : forall x, x ∈ t -> pos n | 
                             (forall p, exists x Hx, p = s x Hx)
                          /\ (forall x H1 H2, s x H1 = s x H2) } }.
  Proof.
    exists (hfs_card n), (@hfs_card_pos n); split.
    + intros p; exists (hfs_pos p).
      assert (hfs_pos p ∈ hfs_card n) as H.
      { apply hfs_mem_btm, bt_card_spec; exists p; auto. }
      exists H.
      apply hfs_pos_inj.
      rewrite <- hfs_card_pos_spec; auto.
    + intros; apply hfs_card_pos_pirr.
  Qed.

  (** Given a finite set type, there is a surjective map from a hfs to that type *)

  Theorem hfs_surj_finite_t X : 
           finite_t X 
        -> { t & { s : forall x, x ∈ t -> X | 
                (forall p, exists x Hx, p = s x Hx)
             /\ (forall x H1 H2, s x H1 = s x H2) } }.
  Proof.
    intros HX.
    apply finite_t_pos_equiv in HX.
    destruct HX as (n & Hn).
    destruct (hfs_surj_t n) as (t & s & Hs & H).
    destruct Hn as (s' & Hs').
    exists t.
    exists (fun x Hx => s' (s x Hx)); split.
    + intros x.
      destruct (Hs' x) as (p & Hp).
      destruct (Hs p) as (u & Hu & H').
      subst; exists u, Hu; auto.
    + intros; f_equal; auto.
  Qed.

  Theorem hfs_finite_t_transitive X : 
        X -> finite_t X -> { l : hfs & { s : hfs -> X | hfs_transitive l /\ forall x, exists a, a ∈ l /\ x = s a } }.
  Proof.
    intros x0 HX.
    destruct (hfs_surj_finite_t HX) as (u & s & Hs1 & Hs2).
    set (s' a  :=
      match hfs_mem_dec a u with
        | left  H => @s a H
        | right _ => x0
      end).
    exists (hfs_tc u), s'; split.
    + apply  hfs_tc_trans.
    + intros x.
      unfold s'.
      destruct (Hs1 x) as (a & Ha & E).
      exists a.
      destruct (hfs_mem_dec a u) as [ H | H ]; try tauto; split.
      * revert H; apply hfs_tc_incl.
      * rewrite E; apply Hs2.
  Qed.

  Opaque hfs_pow.

  Fact hfs_pow_trans_incr t : hfs_transitive t -> t ⊆ hfs_pow t.
  Proof.
    intros Ht z H; apply hfs_pow_spec.
    intros u Hu; revert Hu H; apply Ht.
  Qed.

  Fact hfs_pow_mono s t : s ⊆ t -> hfs_pow s ⊆ hfs_pow t.
  Proof. 
    intros H x; do 2 rewrite hfs_pow_spec.
    intros G z Hz; apply H, G; auto.
  Qed.

  Fact hfs_iter_pow_mono s t n : s ⊆ t -> iter hfs_pow s n ⊆ iter hfs_pow t n.
  Proof.
    revert s t; induction n as [ | n IHn ]; simpl; intros s t Hst; auto.
    apply IHn, hfs_pow_mono, Hst.
  Qed.

  Fact hfs_iter_pow_trans s n : hfs_transitive s -> hfs_transitive (iter hfs_pow s n).
  Proof.
    revert s; induction n as [ | n IHn ]; intros s Hs; simpl; auto.
    apply IHn, hfs_pow_trans; auto.
  Qed.
 
  Fact hfs_iter_pow_le t n m : n <= m -> hfs_transitive t -> iter hfs_pow t n ⊆ iter hfs_pow t m.
  Proof.
    intros H; revert H t.
    induction 1 as [ | m H IH ]; auto; intros t Ht.
    apply hfs_incl_trans with (1 := IH _ Ht); simpl.
    apply hfs_iter_pow_mono, hfs_pow_trans_incr, Ht.
  Qed.

  Opaque hfs_cons.

  Definition hfs_pair (r s : hfs) : hfs := hfs_cons r (hfs_cons s hfs_empty).

  Fact hfs_pair_spec r s x : x ∈ hfs_pair r s <-> x = r \/ x = s.
  Proof.
    unfold hfs_pair.
    do 2 rewrite hfs_cons_spec.
    rewrite hfs_empty_spec; tauto.
  Qed.

  Opaque hfs_pair.

  Fact hfs_pair_pow r s t : r ∈ t -> s ∈ t -> hfs_pair r s ∈ hfs_pow t.
  Proof.
    rewrite hfs_pow_spec.
    intros H1 H2 x.
    rewrite hfs_pair_spec.
    intros [ -> | -> ]; auto.
  Qed.

  Fact hfs_pair_mem_l a b : a ∈ hfs_pair a b.
  Proof. apply hfs_pair_spec; auto. Qed.
  
  Fact hfs_pair_mem_r a b : b ∈ hfs_pair a b.
  Proof. apply hfs_pair_spec; auto. Qed.
 
  Fact hfs_pair_inj a b x y : hfs_pair a b = hfs_pair x y 
                           -> a = x /\ b = y
                           \/ a = y /\ b = x.
  Proof.
    intros E.
    generalize (hfs_pair_mem_l a b) (hfs_pair_mem_r a b)
               (hfs_pair_mem_l x y) (hfs_pair_mem_r x y).
    rewrite <- E, E at 1 2.
    do 4 rewrite hfs_pair_spec.
    do 4 intros [[]|[]]; auto.
  Qed.

  Definition hfs_opair r s := hfs_pair (hfs_pair r r) (hfs_pair r s).

  Notation "⟬ x , y ⟭" := (hfs_opair x y).

  Fact hfs_opair_inj a b x y : ⟬a,b⟭ = ⟬x,y⟭ -> a = x /\ b = y.
  Proof.
    unfold hfs_opair.
    intros H.
    apply hfs_pair_inj in H.
    destruct H as [ (H1 & H2) | (H1 & H2) ];
      apply hfs_pair_inj in H1; apply hfs_pair_inj in H2; 
      revert H1 H2;
      do 2 intros [ [] | [] ]; subst; auto.
  Qed.

  Fact hfs_opair_spec a b x y : ⟬a,b⟭ = ⟬x,y⟭ <-> a = x /\ b = y.
  Proof.
    split.
    + apply hfs_opair_inj.
    + intros [ [] [] ]; auto.
  Qed.

End btree.

Section bt_model3.

  Variable (X : Type) (HX : finite_t X) (psy : nat -> X). 

  Let x0 : X. Proof. exact(psy 0). Qed.

  Infix "∈" := hfs_mem.
  Notation "x ⊆ y" := (forall u, u ∈ x -> u ∈ y).
  Notation "⟬ x , y ⟭" := (hfs_opair x y).

  (** First a surjective map from some transitive set l to X *)

  Let l := projT1 (hfs_finite_t_transitive x0 HX).
  Let s := proj1_sig (projT2 (hfs_finite_t_transitive x0 HX)).
  Let Hl : hfs_transitive l.                     
  Proof. apply (proj2_sig (projT2 (hfs_finite_t_transitive x0 HX))). Qed.
  Let Hs : forall x, exists a, a ∈ l /\ x = s a. 
  Proof. apply (proj2_sig (projT2 (hfs_finite_t_transitive x0 HX))). Qed.

  (** Now we build P^5 l that contains all the set of triples of l *)

  Let p := iter hfs_pow l 5.

  Let Hp1 : hfs_transitive p.
  Proof. apply hfs_iter_pow_trans; auto. Qed.

  Let Hp2 : l ∈ p.
  Proof.
    apply hfs_iter_pow_le with (n := 1); simpl; auto.
    apply hfs_pow_spec; auto.
  Qed.

  Let Hp3 x y : x ∈ l -> y ∈ l -> ⟬x,y⟭  ∈ iter hfs_pow l 2.
  Proof.
    intros Hx Hy.
    do 2 apply hfs_pair_pow; auto.
  Qed.

  Let Hp4 x y : x ∈ l -> y ∈ l -> ⟬x,y⟭  ∈ p.
  Proof.
    intros Hx Hy.
    generalize (Hp3 Hx Hy).
    apply hfs_iter_pow_le; auto.
  Qed.
   
  Let Hp5 x y z : x ∈ l -> y ∈ l -> z ∈ l -> ⟬⟬x,y⟭,z⟭  ∈ iter hfs_pow l 4.
  Proof.
    intros Hx Hy Hz.
    repeat apply hfs_pair_pow; auto.
    apply hfs_iter_pow_le with (n := 0) (m := 2); auto.
  Qed.

  Let Hp6 x y z : x ∈ l -> y ∈ l -> z ∈ l -> ⟬⟬x,y⟭,z⟭  ∈ p.
  Proof.
    intros Hx Hy Hz.
    generalize (Hp5 Hx Hy Hz).
    apply hfs_iter_pow_le; auto.
  Qed.

  Variable (R : X -> X -> X -> Prop).
  Hypothesis HR : forall x y z, { R x y z } + { ~ R x y z }.

  Hint Resolve finite_t_prod hfs_mem_fin_t.

  Let encode_R : { r | r ∈ p /\ forall x y z, R x y z 
                            <-> exists a b c, x = s a /\ a ∈ l
                                           /\ y = s b /\ b ∈ l
                                           /\ z = s c /\ c ∈ l
                                           /\ ⟬⟬a,b⟭,c⟭  ∈ r }.
  Proof.
    set (P t := let a := fst (fst t) in
                let b := snd (fst t) in
                let c := snd t
                in R (s a) (s b) (s c) /\ ((a ∈ l /\ b ∈ l) /\ c ∈ l)).
    set (f t := match t with ((a,b),c) => ⟬⟬a,b⟭,c⟭  end).
    destruct hfs_comprehension with (P := P) (f := f) as (r & Hr).
    + apply fin_t_dec.
      * intros; apply HR.
      * apply fin_t_prod with (P := fun t => fst t ∈ l /\ snd t ∈ l) (Q := fun x => x ∈ l); auto.
        apply fin_t_prod with (P := fun x => x ∈ l) (Q := fun x => x ∈ l); auto.
    + exists r; split.
      * apply hfs_pow_spec; intros x; rewrite Hr.
        intros (((a,b),c) & (H1 & (H2 & H3) & H4) & <-).
        unfold f; apply Hp5; auto.
      * intros x y z; split.
        - intros H.
          destruct (Hs x) as (a & H1 & H2).
          destruct (Hs y) as (b & H3 & H4).
          destruct (Hs z) as (c & H5 & H6).
          exists a, b, c; msplit 6; auto.
          apply Hr.
          exists ((a,b),c); split; auto.
          red; simpl; subst; tauto.
        - intros (a & b & c & -> & ? & -> & ? & -> & ? & G).
          apply Hr in G.
          destruct G as (((u,v),w) & (G1 & _) & G2).
          unfold f in G2.
          do 2 rewrite hfs_opair_spec in G2.
          destruct G2 as ((->&->)&->); auto.
  Qed.

  Let r := proj1_sig encode_R.
  
  Let Hr1 : r ∈ p.
  Proof. apply (proj2_sig encode_R). Qed.

  Let Hr2 x y z : R x y z <-> exists a b c, x = s a /\ a ∈ l
                                         /\ y = s b /\ b ∈ l
                                         /\ z = s c /\ c ∈ l
                                         /\ ⟬⟬a,b⟭,c⟭  ∈ r.
  Proof. apply (proj2_sig encode_R). Qed.

  Let p_bool x := if hfs_mem_dec x p then true else false.

  Let p_bool_spec x : x ∈ p <-> p_bool x = true.
  Proof.   
    unfold p_bool.
    destruct (hfs_mem_dec x p); split; try tauto; discriminate.
  Qed.

  Let Y := sig (fun x => p_bool x = true).

  Let HY : finite_t Y.
  Proof. 
    apply fin_t_finite_t.
    + intros; apply UIP_dec, bool_dec.
    + generalize (hfs_mem_fin_t p); apply fin_t_equiv.
      intros x; auto.
  Qed.
 
  Let mem (x y : Y) := proj1_sig x ∈ proj1_sig y.

  Let xl : Y.
  Proof. 
    exists l; apply p_bool_spec, Hp2.
  Defined.

  Let xr : Y.
  Proof. 
    exists r; apply p_bool_spec, Hr1.
  Defined.

  Check psy.

  Check s.

  Let phi (y : Y) := s (proj1_sig y).
(*

  Theorem bt_m3_m2 : exists (Y : Type) (_ : finite_t Y) (mem : Y -> Y -> Prop) (xl xr : Y) 
                             (phi : X -> Y) 
                             (_ : forall x y, { mem x y } + { ~ mem x y }),
                             m2_member_ext mem
                          /\ m2_has_otriples mem xl
                          /\ (forall a, mem (phi a) xl)
                          /\ (forall a b c, R a b c <-> m2_is_otriple_in mem xr (phi a) (phi b) (phi c)).
    Proof.
      destruct (btm_finite_t p) as (ll & Hll).
      set (K x y := x ≈ y /\ y ∈ p).
      destruct (@decibable_PER_fp_quotient _ ll K) as [ m cls repr G1 G2 G3 ]; unfold K.
      + intros x; rewrite Hll; split.
        * intros (_ & y & H1 & H2).
          exists y; rewrite Hll. 
          msplit 2; auto; exists y; auto.
        * intros (y & H1 & H2 & _); split; auto.
          exists y; auto.
      + split.
        * intros x y (H1 & H2); split; auto.
          revert H2; apply btm_congr_l; auto.
        * intros x y z (H1 & H2) (H3 & H4); split; auto.
          apply bte_trans with y; auto.
      + intros x y; destruct (bte_dec x y); destruct (btm_dec y p); tauto.
      + assert (forall t, t ∈ p -> { j | cls t = Some j }) as G4.
        1: { intros t Ht; case_eq (cls t).
             + intros j Hj; exists j; auto.
             + intros H; exfalso; revert H; rewrite <- G2; intros []; split; auto. }
        destruct (G4 _ Hp1) as (xl & Hxl).
        destruct (G4 _ Hr1) as (xr & Hxr).
        exists (pos m), (finite_t_pos _), (fun x y => repr x ∈ repr y), xl, xr.
        set (phi x := proj1_sig (G4 _ (Hi2 x))).
        assert (Hphi : forall x, cls (i x) = Some (phi x)).
        1: { intro; apply (proj2_sig (G4 _ _)). }
        generalize phi Hphi; clear phi Hphi; intros phi Hphi.
        assert (Hrepr : forall x, repr x ∈ p).
        1: { intros x. 
             generalize (proj2 (G3 (repr x) (repr x))).
             rewrite G1.
             intros []; auto; split; auto; discriminate. }
        assert (G5 : forall u c, cls u = Some c <-> u ≈ repr c).
        { intros u c; split.
          + intros H; apply G3; rewrite G1, H; split; auto; discriminate.
          + intros H; rewrite <- G1; apply G3; red; split; auto. }
        exists phi, (fun x y => bte_dec _ _); msplit 3.
        * intros x y z H.
          red in H.
          apply btm_congr_l, bte_ext.
          intros u; split; intros F.
          - destruct (G4 u) as (j & Hj).
            { apply Hp0 with (1 := F); auto. }
            rewrite G5, bte_sym in Hj.
            apply btm_congr_l with (1 := Hj), H.
            revert F; apply btm_congr_l; auto.
          - destruct (G4 u) as (j & Hj).
            { apply Hp0 with (1 := F); auto. }
            rewrite G5, bte_sym in Hj.
            apply btm_congr_l with (1 := Hj), H.
            revert F; apply btm_congr_l; auto.
        * intros x y z Hx Hy Hz.
          admit.
        * intros x.
          generalize (Hphi x).
          rewrite G5; intros H.
          rewrite G5 in Hxl.
          apply btm_congr_l with (1 := H).
          apply btm_congr_r with (1 := Hxl); auto.
        * intros a b c; rewrite Hr2.
          generalize (Hphi a) (Hphi b) (Hphi c).
          repeat rewrite G5.
          intros H1 H2 H3.
          split.
          - intros H.
            destruct (G4 _ (Hp0 H Hr1)) as (t & Ht).
            rewrite G5 in Ht.
            apply G5 in Hxr.
            exists t; rewrite <- Ht, <- Hxr; split; auto.
            destruct (G4 _ (Hp2' (Hi1 a) (Hi1 b))) as (u & Hu).
            rewrite G5 in Hu.
            exists u; split.
            ++ red.
            
          

            red.
            Check (Hp2 (Hi1 a) (Hi1 b) (Hi1 c)).
          rewrite H1, H2, H3.
          generalize (phi a) (phi b) (phi c); clear a b c H1 H2 H3.
          intros a b c.
          split.
          - intros H.
            exists (⟬repr a,⟬repr b,repr c⟭⟭).

            assert (u = repr j) as Hu.
            { generalize Hj; intros F1.
              rewrite <- G1 in Hj.
               
              apply G3 in Hj.
          Check (repr
          Check (proj1 (bte_ext _ _)).
 unfold m2_equiv. rewrite <- bte_ext.
    

               .
        
          
 exists x.
              


 


  
  Definition *)

  (** Now how to encode the model given by k-ary relation over a finite
      set of cardinal n

      A finite set (pos n) and a k-ary relation R : (pos n)^k -> Prop
      
      1) Find a transitive btree t such that pos n injects into t
         For this, it is enough that its depth is greater that n
    
      2) forall x, y in t, both {x} and {x,y} belong to P(t)
         hence <x,y> belongs to P(P(t))

      3) and <x1,...,xk> belongs to P^2k(t) for any x1,...,xk in t 
         So P^2k(t) contains any k-ary tuple if the image of (pos n).
        
      4) Hence X = P^{2k+1}(t) contains all unary relations over k-ary 
         tuple hence all the k-ary relations over t.

      5) So we can encode R into the transitive set X = P^{2k+1}(t). 
         
      6) In the logic, we have a globally existentially quantified X_R 
         and we replace any 
      
               R (v1,...,vk) by <x1,...,xk> in X_R

         encoded according to the above description

         Perhaps follow the H10 technique to establish FOL encodability 
         into the Σ(0,2) signature

      *)

  (** We have computed the transitive closure, spec'ed and proved finite *)  


  Check btm_depth.
  Check btm_finite_t.
  Print bt_transitive.
  Check bt_tc_trans.
  Check bt_pow_transitive.

  Check bt_enc_equiv.
  Check bt_enc_empty.
  Check bt_enc_sg.
  Check bt_enc_db.
  Check bt_pair_equiv. 
  Check bt_enc_pair.
  Check bt_enc_triple.
  Check bt_enc_rel3. 
 
  Print tuple.
  Check bt_enc_tuple_0.
  Check bt_enc_tuple.

End bt_model3.
