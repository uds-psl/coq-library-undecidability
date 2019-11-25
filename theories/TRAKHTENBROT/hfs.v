(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Max Wellfounded Setoid Eqdep_dec Bool.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import wf_finite wf_chains.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops membership btree.

Set Implicit Arguments.

Local Infix "⪧" := bt_node.

Section hfs.

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

  Fact hfs_mem_wf : well_founded hfs_mem.
  Proof. unfold hfs_mem; apply wf_inverse_image, btm_wf. Qed.

  Definition hfs_rect := well_founded_induction_type hfs_mem_wf.

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

  Definition hfs_empty : hfs := exist _ bt_leaf eq_refl.

  Notation "∅" := hfs_empty.

  Fact hfs_empty_prop : forall x, ~ x ∈ ∅.
  Proof. 
    intros (x & ?); simpl; btm simpl.
  Qed.

  Fact hfs_empty_spec x : x ∈ ∅ <-> False.
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

  Definition hfs_pow t := cls (bt_pow (repr t)).

  Notation "x ⊆ y" := (forall u, u ∈ x -> u ∈ y).

  Fact hfs_incl_refl r : r ⊆ r.
  Proof. apply mb_incl_refl. Qed.

  Fact hfs_incl_trans r s t : r ⊆ s -> s ⊆ t -> r ⊆ t.
  Proof. apply mb_incl_trans. Qed.

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

  Definition hfs_card n := cls (nat2bt n).

  Fact hfs_card_transitive n : hfs_transitive (hfs_card n).
  Proof. 
    unfold hfs_card.
    apply bt_hfs_transitive.
    intros ? ?.
    rewrite hfs_repr_bt_cls.
    apply nat2bt_transitive.
  Qed.

  Definition hfs_pos n (p : pos n) := cls (pos2bt p).

  Fact hfs_pos_card n x : x ∈ hfs_card n <-> exists p, x = @hfs_pos n p.
  Proof.
    unfold hfs_pos, hfs_card.
    rewrite btm_repr_cls; split.
    + intros Hx.
      exists (bt2pos _ Hx).
      symmetry; apply bt_cls_hfs_repr_iff.
      rewrite bt2pos_fix; auto.
    + intros (p & ->).
      rewrite hfs_repr_bt_cls.
      apply pos2bt_in.
  Qed.
 
  Fact hfs_pos_prop n p : @hfs_pos n p ∈ hfs_card n.
  Proof.
    apply hfs_pos_card; exists p; auto.
  Qed.
  
  Definition hfs_card_pos n x : x ∈ hfs_card n -> pos n.
  Proof.
    intros H.
    apply btm_repr_cls in H.
    apply (bt2pos _ H).
  Defined.

  Fact hfs_card_pos_spec n x Hx : x = hfs_pos (@hfs_card_pos n x Hx).
  Proof.
    unfold hfs_card_pos, hfs_pos.
    symmetry; apply bt_cls_hfs_repr_iff.
    rewrite bt2pos_fix; auto.
  Qed.

  Fact hfs_pos_inj n p q : @hfs_pos n p = hfs_pos q -> p = q.
  Proof.
    unfold hfs_pos.
    rewrite bt_cls_equiv.
    apply pos2bt_inj.
  Qed.

  Fact hfs_card_pos_pirr n x H1 H2 : @hfs_card_pos n x H1 = @hfs_card_pos n x H2.
  Proof. apply hfs_pos_inj; do 2 rewrite <- hfs_card_pos_spec; auto. Qed.

  (** There is a bijective map from pos n <-> _ ∈ t where t is transitive *)

  Fact hfs_bij_t n : { t : hfs & 
                       { f : pos n -> hfs & 
                         { g : forall x, x ∈ t -> pos n |
                                hfs_transitive t
                             /\ (forall p, f p ∈ t)
                             /\ (forall p H, g (f p) H = p) 
                             /\ forall x H, f (g x H) = x } } }.
  Proof.
    exists (hfs_card n), (@hfs_pos _), 
           (@hfs_card_pos _); msplit 3.
    + apply hfs_card_transitive.
    + apply hfs_pos_prop.
    + intros p H; apply hfs_pos_inj; rewrite <- hfs_card_pos_spec; auto.
    + intros; rewrite <- hfs_card_pos_spec; auto.
  Qed.

  (** For the non-empty finite type pos (S n), there is a computably
      surjective map from a transitive set l onto pos (S n) 

      The case of the empty model is rules out in our case
      because we always need to be able to interpret some variable
      in unscoped De Bruijn syntax
    *)

  Theorem hfs_pos_n_transitive n :
        { l : hfs & { f : hfs -> pos (S n) & 
                    { g : pos (S n) -> hfs |
                      hfs_transitive l
                   /\ (forall p, g p ∈ l)
                   /\ (forall x, x ∈ l -> exists p, x = g p)
                   /\ (forall p, f (g p) = p) } } }.
  Proof.
    destruct (hfs_bij_t (S n)) as (u & i & j & H1 & H2 & H3 & H4).
    set (f x  := 
      match hfs_mem_dec x u with
        | left  H => @j _ H
        | right _ => pos0
      end).
    exists u, f, i; msplit 3; auto.
    + intros x Hx.
      exists (j x Hx); rewrite H4; auto.
    + intros p; unfold f.
      destruct (hfs_mem_dec (i p) u) as [ H | H ].
      * rewrite H3; auto.
      * destruct H; auto.
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

  Variable (p : hfs) (Hp : hfs_transitive p).

  Fact hfs_trans_pair_inv x y : hfs_pair x y ∈ p -> x ∈ p /\ y ∈ p.
  Proof.
    intros H; split; apply Hp with (2 := H); apply hfs_pair_spec; auto.
  Qed.

  Fact hfs_trans_opair_inv x y : ⟬x,y⟭ ∈ p -> hfs_pair x x ∈ p /\ hfs_pair x y ∈ p.
  Proof. apply hfs_trans_pair_inv. Qed.

  Fact hfs_trans_otriple_inv x y z : ⟬⟬x,y⟭,z⟭  ∈ p -> ⟬x,y⟭  ∈ p /\ z ∈ p.
  Proof.
    intros H.
    apply hfs_trans_opair_inv, proj2, hfs_trans_pair_inv in H.
    auto.
  Qed.

End hfs.
