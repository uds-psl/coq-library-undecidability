(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Max Lia Setoid.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import wf_finite wf_chains.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops btree.

Set Implicit Arguments.

Local Notation "∅" := bt_leaf.
Local Infix "⪧" := bt_node.
Local Infix "≈" := bt_equiv.
Local Notation "s ≉ t" := (~ s ≈ t).
Local Infix "∈" := bt_mem.
Local Notation "s ∉ t" := (~ s ∈ t).
Local Infix "⊆" := bt_incl.
Local Notation "⟬ s , t ⟭" := (bt_opair s t).

Local Notation "∈-chain" := (chain (fun s t => s ∈ t)).
Local Notation "∈-chain_list" := (chain_list (fun s t => s ∈ t)).

Section bte_chains.

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

  Fact btm_chain_list_comp u l s t : 
             l <> nil
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

  Opaque max.

  Fact btm_depth_chain t : { l | ∈-chain_list l ∅ t /\ length l = ⌞t⌟ }.
  Proof.
    induction t as [ | s (ls & H1 & H2) t (lt & H3 & H4) ].
    + exists nil; simpl; split; auto; constructor.
    + destruct (le_lt_dec (S ⌞s⌟) ⌞t⌟) as [ H | H ].
      * exists lt; split.
        - apply btm_chain_list_comp; auto.
          destruct lt; try discriminate; simpl in *; lia.
        - simpl; rewrite max_r; auto.
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

End bte_chains.

Fact bt_tc_mono s t : s ⊆ t -> ↓s ⊆ ↓t.
Proof.
  intros H x.

  do 2 rewrite bt_tc_spec.
  intros (n & Hn).
  apply chain_snoc_inv in Hn.
  destruct Hn as (y & H1 & H2).
  exists n; apply chain_snoc with y; auto.
Qed.

Hint Resolve bt_tc_incr bt_tc_mono bt_tc_trans.

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

Section bt_level.

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
        - exists b; auto; btm simpl.
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


  (** We have our bijection ... the later one is another
      but do not give a transitive set *)
 
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

End bt_level.
