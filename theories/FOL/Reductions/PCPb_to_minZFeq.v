(* ** Variant allowing intensional models *)

Require Import Undecidability.FOL.ZF.
Require Import Undecidability.FOL.Syntax.Facts.
Require Import Undecidability.FOL.Semantics.Tarski.FullFacts.
From Undecidability.FOL.Sets Require Import minZF ZF.
Require Import Undecidability.FOL.Sets.ZF.
From Undecidability.FOL.Reductions Require Import PCPb_to_ZF PCPb_to_ZFeq PCPb_to_minZF.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations ListAutomationHints ListAutomationInstances.
Local Set Implicit Arguments.
Local Unset Strict Implicit.

From Stdlib Require Import Morphisms.


Local Notation vec := Vector.t.

#[local] Notation term' := (term sig_empty).
#[local] Notation form' := (form sig_empty _ _ falsity_on).

(* ** Semantics *)

Section Model.

  Open Scope ZFsem.

  Context {V : Type} {I : interp V}.

  Hypothesis M_ZF : forall rho, rho ⊫ ZFeq'.

  Instance min_model : interp sig_empty _ V.
  Proof using I.
    split.
    - intros [].
    - now apply i_atom.
  Defined.

  Lemma min_embed_eval (rho : nat -> V) (t : term') :
    eval rho (embed_t t) = eval rho t.
  Proof.
    destruct t as [|[]]. reflexivity.
  Qed.

  Lemma min_embed (rho : nat -> V) (phi : form')  :
    sat I rho (embed phi) <-> sat min_model rho phi.
  Proof.
    induction phi in rho |- *; try destruct b0; try destruct q; cbn.
    1,3-7: firstorder. erewrite Vector.map_map, Vector.map_ext.
    reflexivity. apply min_embed_eval.
  Qed.

  Lemma embed_subst_t (sigma : nat -> term') (t : term') :
    embed_t t`[sigma] = (embed_t t)`[sigma >> embed_t].
  Proof.
    induction t; cbn; trivial. destruct F.
  Qed.

  Lemma embed_subst (sigma : nat -> term') (phi : form') :
    embed phi[sigma] = (embed phi)[sigma >> embed_t].
  Proof.
    induction phi in sigma |- *; cbn; trivial.
    - f_equal. erewrite !Vector.map_map, Vector.map_ext. reflexivity. apply embed_subst_t.
    - firstorder congruence.
    - rewrite IHphi. f_equal. apply subst_ext. intros []; cbn; trivial.
      unfold funcomp. cbn. unfold funcomp. now destruct (sigma n) as [x|[]].
  Qed.

  Lemma embed_sshift n (phi : form') :
    embed phi[sshift n] = (embed phi)[sshift n].
  Proof.
    rewrite embed_subst. apply subst_ext. now intros [].
  Qed.

  Lemma sat_sshift1 (rho : nat -> V) x y (phi : form) :
    (y .: x .: rho) ⊨ phi[sshift 1] <-> (y .: rho) ⊨ phi.
  Proof.
    erewrite sat_comp, sat_ext. reflexivity. now intros [].
  Qed.

  Lemma sat_sshift2 (rho : nat -> V) x y z (phi : form) :
    (z .: y .: x .: rho) ⊨ phi[sshift 2] <-> (z .: rho) ⊨ phi.
  Proof.
    erewrite sat_comp, sat_ext. reflexivity. now intros [].
  Qed.

  Lemma inductive_sat (rho : nat -> V) x :
    (x .: rho) ⊨ is_inductive $0 -> M_inductive x.
  Proof using M_ZF.
    cbn. split.
    - destruct H as [[y Hy] _]. enough (H : ∅ ≡ y).
      { eapply set_equiv_elem; eauto. now apply set_equiv_equiv. apply Hy. }
      apply M_ext; trivial; intros z Hz; exfalso.
      + now apply M_eset in Hz.
      + firstorder easy.
    - intros y [z Hz] % H. enough (Hx : σ y ≡ z).
      { eapply set_equiv_elem; eauto. now apply set_equiv_equiv. apply Hz. }
      apply M_ext; trivial.
      + intros a Ha % sigma_el; trivial. now apply Hz.
      + intros a Ha % Hz. now apply sigma_el.
  Qed.

  Lemma inductive_sat_om (rho : nat -> V) :
    (ω .: rho) ⊨ is_inductive $0.
  Proof using M_ZF.
    cbn. split.
    - exists ∅. split; try apply M_eset; trivial. now apply M_om1.
    - intros d Hd. exists (σ d). split; try now apply M_om1. intros d'. now apply sigma_el.
  Qed.

  Instance set_equiv_equiv' :
    Equivalence set_equiv.
  Proof using M_ZF.
    now apply set_equiv_equiv.
  Qed.

  Instance set_equiv_elem' :
    Proper (set_equiv ==> set_equiv ==> iff) set_elem.
  Proof using M_ZF.
    now apply set_equiv_elem.
  Qed.

  Instance set_equiv_sub' :
    Proper (set_equiv ==> set_equiv ==> iff) set_sub.
  Proof using M_ZF.
    now apply set_equiv_sub.
  Qed.

  Instance equiv_union' :
    Proper (set_equiv ==> set_equiv) union.
  Proof using M_ZF.
    now apply equiv_union.
  Qed.

  Instance equiv_power' :
    Proper (set_equiv ==> set_equiv) power.
  Proof using M_ZF.
    now apply equiv_power.
  Qed.

  Lemma rm_const_tm_sat (rho : nat -> V) (t : term) x :
    (x .: rho) ⊨ embed (rm_const_tm t) <-> set_equiv x (eval rho t).
  Proof using M_ZF.
    induction t in x |- *; try destruct F; cbn; split;
    try rewrite (vec_inv1 v); try rewrite (vec_inv2 v); cbn.
    - tauto.
    - tauto.
    - rewrite (vec_nil_eq (Vector.map (eval rho) v)).
      intros H. apply M_ext; trivial; intros y Hy; exfalso.
      + firstorder easy.
      + now apply M_eset in Hy. 
    - rewrite (vec_nil_eq (Vector.map (eval rho) v)).
      change (set_equiv x ∅ -> forall d : V, set_elem d x -> False).
      intros H d. rewrite H. now apply M_eset.
    - intros (y & Hy & z & Hz & H).
      rewrite embed_sshift, sat_sshift1, IH in Hy; try apply in_hd.
      rewrite embed_sshift, sat_sshift2, IH in Hz; try apply in_hd_tl.
      apply M_ext; trivial.
      + intros a Ha % H. apply M_pair; trivial.
        rewrite <- Hy, <- Hz. tauto.
      + intros a Ha % M_pair; trivial. apply H.
        rewrite <- Hy, <- Hz in Ha. tauto.
    - exists (eval rho (Vector.hd v)).
      rewrite embed_sshift, sat_sshift1, IH; try apply in_hd. split; try reflexivity.
      exists (eval rho (Vector.hd (Vector.tl v))).
      rewrite embed_sshift, sat_sshift2, IH; try apply in_hd_tl. split; try reflexivity.
      change (forall d, (set_elem d x -> d ≡ eval rho (Vector.hd v) \/ d ≡ eval rho (Vector.hd (Vector.tl v))) /\ 
              (d ≡ eval rho (Vector.hd v) \/ d ≡ eval rho (Vector.hd (Vector.tl v)) -> set_elem d x)).
      intros d. rewrite H. now apply M_pair.
    - intros (y & Hy & H). rewrite embed_sshift, sat_sshift1, IH in Hy; try apply in_hd.
      change (set_equiv x (union (eval rho (Vector.hd v)))). rewrite <- Hy. apply M_ext; trivial.
      + intros z Hz % H. now apply M_union.
      + intros z Hz % M_union; trivial. now apply H.
    - exists (eval rho (Vector.hd v)). rewrite embed_sshift, sat_sshift1, IH; try apply in_hd. split; try reflexivity.
      change (forall d, (set_elem d x -> exists d0 : V, d0 ∈ eval rho (Vector.hd v) /\ d ∈ d0) /\
              ((exists d0 : V, d0 ∈ eval rho (Vector.hd v) /\ d ∈ d0) -> set_elem d x)).
      intros d. rewrite H. now apply M_union.
    - intros (y & Hy & H). rewrite embed_sshift, sat_sshift1, IH in Hy; try apply in_hd.
      change (set_equiv x (power (eval rho (Vector.hd v)))). rewrite <- Hy. apply M_ext; trivial.
      + intros z Hz. apply M_power; trivial. unfold set_sub. now apply H.
      + intros z Hz. now apply H, M_power.
    - exists (eval rho (Vector.hd v)).
      rewrite embed_sshift, sat_sshift1, IH; try apply in_hd. split; try reflexivity.
      change (forall d, (set_elem d x -> d ⊆ eval rho (Vector.hd v)) /\ (d ⊆ eval rho (Vector.hd v) -> set_elem d x)).
      intros d. rewrite H. now apply M_power.
    - rewrite (vec_nil_eq (Vector.map (eval rho) v)). intros [H1 H2]. apply M_ext; trivial.
      + unfold set_sub. apply H2. apply (inductive_sat_om rho).
      + unfold set_sub. apply M_om2; trivial. apply inductive_sat with rho. apply H1.
    - rewrite (vec_nil_eq (Vector.map (eval rho) v)). split.
      + change ((exists d : V, (forall d0 : V, d0 ∈ d -> False) /\ set_elem d x) /\ (forall d : V, set_elem d x
            -> exists d0 : V, (forall d1 : V, (d1 ∈ d0 -> d1 ∈ d \/ d1 ≡ d) /\ (d1 ∈ d \/ d1 ≡ d -> d1 ∈ d0)) /\ set_elem d0 x)).
        setoid_rewrite H. apply (inductive_sat_om rho).
      + intros d Hd. change (set_sub x d). rewrite H. unfold set_sub.
        apply M_om2; trivial. apply inductive_sat with rho. apply Hd.
  Qed.

  Lemma rm_const_sat (rho : nat -> V) (phi : form) :
    rho ⊨ phi <-> rho ⊨ embed (rm_const_fm phi).
  Proof using M_ZF.
    induction phi in rho |- *; try destruct P; try destruct b0; try destruct q; cbn.
    1: firstorder easy.
    3-5: specialize (IHphi1 rho); specialize (IHphi2 rho); intuition easy.
    - rewrite (vec_inv2 t). cbn. split.
      + intros H. exists (eval rho (Vector.hd t)). rewrite rm_const_tm_sat. split; try reflexivity.
        exists (eval rho (Vector.hd (Vector.tl t))). now rewrite embed_sshift, sat_sshift1, rm_const_tm_sat.
      + intros (x & Hx & y & Hy & H). apply rm_const_tm_sat in Hx.
        change (set_elem (eval rho (Vector.hd t)) (eval rho (Vector.hd (Vector.tl t)))).
        rewrite embed_sshift, sat_sshift1, rm_const_tm_sat in Hy. now rewrite <- Hx, <- Hy.
    - rewrite (vec_inv2 t). cbn. split.
      + intros H. exists (eval rho (Vector.hd t)). rewrite rm_const_tm_sat. split; try reflexivity.
        exists (eval rho (Vector.hd (Vector.tl t))). rewrite embed_sshift, sat_sshift1, rm_const_tm_sat.
        split; trivial. reflexivity.
      + intros (x & Hx & y & Hy & H). apply rm_const_tm_sat in Hx.
        change (set_equiv (eval rho (Vector.hd t)) (eval rho (Vector.hd (Vector.tl t)))).
        rewrite embed_sshift, sat_sshift1, rm_const_tm_sat in Hy. now rewrite <- Hx, <- Hy.
    - split; intros; apply IHphi, H.
    - firstorder eauto.
  Qed.

  Theorem min_correct (rho : nat -> V) (phi : form) :
    sat I rho phi <-> sat min_model rho (rm_const_fm phi).
  Proof using M_ZF.
    rewrite <- min_embed. apply rm_const_sat.
  Qed.

  Lemma min_axioms' (rho : nat -> V) :
    rho ⊫ minZFeq'.
  Proof using M_ZF.
    intros A [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn.
    - now apply set_equiv_equiv.
    - now apply set_equiv_equiv.
    - now apply set_equiv_equiv.
    - intros x x' y y' Hx Hy. now apply set_equiv_elem.
    - intros x y H1 H2. now apply M_ext.
    - exists ∅. apply (@M_ZF rho ax_eset). firstorder.
    - intros x y. exists ({x; y}). apply (@M_ZF rho ax_pair). firstorder.
    - intros x. exists (⋃ x). apply (@M_ZF rho ax_union). firstorder.
    - intros x. exists (PP x). apply (@M_ZF rho ax_power). firstorder.
    - exists ω. split. split.
      + exists ∅. split. apply (@M_ZF rho ax_eset). firstorder. apply (@M_ZF rho ax_om1). firstorder.
      + intros x Hx. exists (σ x). split. 2: apply (@M_ZF rho ax_om1); firstorder.
        intros y. now apply sigma_el.
      + intros x [H1 H2]. apply (@M_ZF rho ax_om2); cbn. auto 12. split.
        * destruct H1 as (e & E1 & E2). change (set_elem ∅ x).
          enough (set_equiv ∅ e) as -> by assumption.
          apply M_ext; trivial. all: intros y Hy; exfalso; try now apply E1 in Hy.
          apply (@M_ZF rho ax_eset) in Hy; trivial. unfold ZFeq', ZF'. auto 8.
        * intros d (s & S1 & S2) % H2. change (set_elem (σ d) x).
          enough (set_equiv (σ d) s) as -> by assumption.
          apply M_ext; trivial. all: intros y; rewrite sigma_el; trivial; apply S1.
  Qed.

End Model.
