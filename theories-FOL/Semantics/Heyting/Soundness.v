From Equations Require Import Equations.
From Coq Require Import Arith Lia List Program.Equality.
From FOL Require Import FullSyntax Heyting.Heyting.
Import ListNotations.

(** ** Heyting Soundness *)

Section Soundness.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {eq_dec_Funcs : EqDec Σ_funcs}.
  Context {eq_dec_Preds : EqDec Σ_preds}.

  Context { HA : CompleteHeytingAlgebra }.

  Lemma Meet_hsat_L A phi ( HP : forall (P : Σ_preds), Vector.t term (ar_preds P) -> HA) :
    Meet (hsat_L HP A) (hsat HP phi) <= hsat_L HP (phi :: A).
  Proof.
    apply Inf1. intros x [psi[[->|H1] ->]].
    - apply Meet3.
    - rewrite Meet2. apply Inf2. now exists psi.
  Qed.

  Lemma map_subst t A sigma :
    map (subst_form sigma) A = map (subst_form (t.:sigma)) (map (subst_form ↑) A).
  Proof.
    induction A; cbn; trivial.
    rewrite IHA. now asimpl.
  Qed.

  Context { HP : forall (P : Σ_preds), Vector.t term (ar_preds P) -> HA}.
  Theorem Soundness' A phi :
    A ⊢I phi -> forall sigma, hsat_L HP (map (subst_form sigma) A) <= hsat HP phi[sigma].
  Proof.
    remember intu as b. intros H.
    dependent induction H; intros sigma; asimpl; simp hsat in *; fold subst_form in *.
    all: try specialize (IHprv eq_dec_Funcs eq_dec_Preds HP _ _ eq_refl eq_refl JMeq_refl JMeq_refl);
         try specialize (IHprv1 eq_dec_Funcs eq_dec_Preds HP _ _ eq_refl eq_refl JMeq_refl JMeq_refl);
         try specialize (IHprv2 eq_dec_Funcs eq_dec_Preds HP _ _ eq_refl eq_refl JMeq_refl JMeq_refl);
         try specialize (IHprv3 eq_dec_Funcs eq_dec_Preds HP _ _ eq_refl eq_refl JMeq_refl JMeq_refl);
         cbn.
    - apply Impl1. rewrite <- IHprv. apply Meet_hsat_L.
    - specialize (IHprv1 sigma). specialize (IHprv2 sigma). cbn in IHprv1.
      simp hsat in *. apply Impl1 in IHprv1.
      rewrite <- IHprv1, <- Meet1. now split.
    - apply Inf1. intros x [t ->]. asimpl. rewrite <- IHprv.
      setoid_rewrite map_subst with (t:=t) at 1. reflexivity.
    - rewrite IHprv. cbn. simp hsat. apply Inf2. exists (t`[sigma]). now asimpl.
    - rewrite IHprv. apply Sup2. exists (t`[sigma]). now asimpl.
    - specialize (IHprv1 sigma). cbn in IHprv1. simp hsat in IHprv1.
      rewrite (meet_sup_expansion IHprv1). apply Sup1. intros x [t ->].
      rewrite Meet_hsat_L. setoid_rewrite map_subst with (t:=t) at 1.
      asimpl. rewrite (IHprv2 (t.:sigma)). now asimpl.
    - rewrite IHprv. cbn. simp hsat. apply Bot1.
    - apply Inf2. exists phi[sigma]. split; trivial. apply in_map_iff. now exists phi.
    - now apply Meet1.
    - rewrite IHprv. cbn. simp hsat. apply Meet2.
    - rewrite IHprv. cbn. simp hsat. apply Meet3.
    - rewrite IHprv. apply Join2.
    - rewrite IHprv. apply Join3.
    - specialize (IHprv1 sigma). cbn. simp hsat in IHprv1. cbn in IHprv1. simp hsat in IHprv1. rewrite (meet_join_expansion IHprv1). 
      apply Join1. cbn in *. split; rewrite Meet_hsat_L; eauto.
  Qed.

  Theorem Soundness A phi :
    A ⊢I phi -> hsat_L HP A <= hsat HP phi.
  Proof.
    intros H. apply Soundness' with (sigma:=var) in H. asimpl in H.
    erewrite map_ext, map_id in H. 1:easy. now intros a; cbn; asimpl.
  Qed.

End Soundness.

      

(* ** Boolean Soundness ***)

Section BSoundness.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {eq_dec_Funcs : EqDec Σ_funcs}.
  Context {eq_dec_Preds : EqDec Σ_preds}.

  Context { HA : CompleteHeytingAlgebra }.
  Context { HP : forall (P : Σ_preds), Vector.t term (ar_preds P) -> HA}.

  Theorem BSoundness' A phi :
    boolean HA -> A ⊢C phi -> forall sigma, hsat_L HP (map (subst_form sigma) A) <= hsat HP phi[sigma].
  Proof. intros HB.
    intros H.
    dependent induction H; intros sigma; asimpl; simp hsat in *; fold subst_form in *.
    all: try specialize (IHprv eq_dec_Funcs eq_dec_Preds HP _ _ HB eq_refl eq_refl JMeq_refl JMeq_refl);
         try specialize (IHprv1 eq_dec_Funcs eq_dec_Preds HP _ _ HB eq_refl eq_refl JMeq_refl JMeq_refl);
         try specialize (IHprv2 eq_dec_Funcs eq_dec_Preds HP _ _ HB eq_refl eq_refl JMeq_refl JMeq_refl);
         try specialize (IHprv3 eq_dec_Funcs eq_dec_Preds HP _ _ HB eq_refl eq_refl JMeq_refl JMeq_refl);
         cbn.
    - apply Impl1. rewrite <- IHprv. apply Meet_hsat_L.
    - specialize (IHprv1 sigma). specialize (IHprv2 sigma). cbn in IHprv1.
      simp hsat in *. apply Impl1 in IHprv1.
      rewrite <- IHprv1, <- Meet1. now split.
    - apply Inf1. intros x [t ->]. asimpl. rewrite <- IHprv.
      setoid_rewrite map_subst with (t:=t) at 1. reflexivity.
    - rewrite IHprv. cbn. simp hsat. apply Inf2. exists (t`[sigma]). now asimpl.
    - rewrite IHprv. apply Sup2. exists (t`[sigma]). now asimpl.
    - specialize (IHprv1 sigma). cbn in IHprv1. simp hsat in IHprv1.
      rewrite (meet_sup_expansion IHprv1). apply Sup1. intros x [t ->].
      rewrite Meet_hsat_L. setoid_rewrite map_subst with (t:=t) at 1.
      asimpl. rewrite (IHprv2 (t.:sigma)). now asimpl.
    - rewrite IHprv. cbn. simp hsat. apply Bot1.
    - apply Inf2. exists phi[sigma]. split; trivial. apply in_map_iff. now exists phi.
    - now apply Meet1.
    - rewrite IHprv. cbn. simp hsat. apply Meet2.
    - rewrite IHprv. cbn. simp hsat. apply Meet3.
    - rewrite IHprv. apply Join2.
    - rewrite IHprv. apply Join3.
    - specialize (IHprv1 sigma). cbn. simp hsat in IHprv1. cbn in IHprv1. simp hsat in IHprv1. rewrite (meet_join_expansion IHprv1). 
      apply Join1. cbn in *. split; rewrite Meet_hsat_L; eauto.
    - apply Impl1. eapply Rtra; try apply Meet3. apply HB.
  Qed.

  Theorem BSoundness A phi :
    boolean HA -> A ⊢C phi -> hsat_L HP A <= hsat HP phi.
  Proof.
    intros HB H. apply BSoundness' with (sigma:=var) in H; asimpl in H.
    erewrite map_ext, map_id in H. 1:easy. now intros a; cbn; asimpl. apply HB.
  Qed.

End BSoundness.
