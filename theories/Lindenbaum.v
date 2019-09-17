(** * Heyting Semantics *)

From Equations Require Import Equations.
From Undecidability.FOLC Require Export FullND Heyting.

(** ** Heyting Evaluation *)

Section Lindenbaum.

Context {Sigma : Signature}.

Section CHAEval.

  Context { HA : CompleteHeytingAlgebra }.

  Variable hinter_Pr : forall (P : Preds), Vector.t term (pred_ar P) -> HA.

  Obligation Tactic := intros; subst; cbn; try lia.

  Axiom todo : forall {A}, A.
  
  Equations hsat (phi : form) : HA by wf (size phi) lt :=
    hsat (Pred P v) := hinter_Pr v ;
    hsat ⊥ := Bot ;
    hsat (phi --> psi) := Impl (hsat phi) (hsat psi) ;
    hsat (phi ∧ psi) := Meet (hsat phi) (hsat psi) ;
    hsat (phi ∨ psi) := Join (hsat phi) (hsat psi) ;
    hsat (∀ phi) := Inf_indexed (fun t => hsat (phi [t..])) ;
    hsat (∃ phi) := Sup_indexed (fun t => hsat (phi [t..])).
  Next Obligation.
    rewrite subst_size. lia.
  Qed.
  Next Obligation.
    rewrite subst_size. lia.
  Qed.

  Definition hsat_L A : HA :=
    Inf (fun x => exists phi, phi el A /\ x = hsat phi).

  Lemma top_hsat_L :
    Top <= hsat_L nil.
  Proof.
    apply Inf1. intros v [phi [[] _]].
  Qed.

End CHAEval.



(** ** Soundness *)

Section Soundness.

  Context { HA : CompleteHeytingAlgebra }.
  Context { HP : forall (P : Preds), Vector.t term (pred_ar P) -> HA }.

  Lemma Meet_hsat_L A phi :
    Meet (hsat_L HP A) (hsat HP phi) <= hsat_L HP (phi :: A).
  Proof.
    apply Inf1. intros x [psi[[->|H1] ->]].
    - apply Meet3.
    - rewrite Meet2. apply Inf2. now exists psi.
  Qed.

  Lemma map_subst t A sigma :
    [phi[sigma] | phi ∈ A] = [phi[t.:sigma] | phi ∈ [phi[↑] | phi ∈ A]].
  Proof.
    induction A; cbn; trivial.
    rewrite IHA. now asimpl.
  Qed.

  Theorem Soundness' A phi :
    A ⊢IE phi -> forall sigma, hsat_L HP ([p[sigma] | p ∈ A]) <= hsat HP phi[sigma].
  Proof.
    remember intu as b.
    induction 1; intros sigma; asimpl in *; simp hsat in *; fold subst_form in *.
    all: try specialize (IHprv Heqb); try specialize (IHprv1 Heqb); try specialize (IHprv2 Heqb).
    - apply Impl1. rewrite <- IHprv. apply Meet_hsat_L.
    - specialize (IHprv1 sigma). specialize (IHprv2 sigma).
      simp hsat in *. apply Impl1 in IHprv1.
      rewrite <- IHprv1, <- Meet1. now split.
    - apply Inf1. intros x [t ->]. asimpl. rewrite <- IHprv.
      rewrite map_subst with (t:=t). reflexivity.
    - rewrite IHprv. simp hsat. apply Inf2. exists t[sigma]. now asimpl.
    - rewrite IHprv. apply Sup2. exists t[sigma]. now asimpl.
    - specialize (IHprv1 sigma). simp hsat in IHprv1.
      rewrite (meet_sup_expansion IHprv1). apply Sup1. intros x [t ->].
      rewrite Meet_hsat_L. rewrite map_subst with (t:=t).
      asimpl. rewrite (IHprv2 (t.:sigma)). now asimpl.
    - rewrite IHprv. apply Bot1.
    - apply Inf2. exists phi[sigma]. split; trivial. apply in_map_iff. now exists phi.
    - now apply Meet1.
    - rewrite IHprv. simp hsat. apply Meet2.
    - rewrite IHprv. simp hsat. apply Meet3.
    - rewrite IHprv. apply Join2.
    - rewrite IHprv. apply Join3.
    - specialize (IHprv1 sigma). simp hsat in IHprv1. rewrite (meet_join_expansion IHprv1). 
      apply Join1. cbn in *. split; rewrite Meet_hsat_L; eauto.
    - discriminate Heqb.
  Qed.

  Lemma var_subst phi :
    phi[var_term] = phi.
  Proof.
    now asimpl.
  Qed.

  Lemma var_subst_L A :
    [phi[var_term] | phi ∈ A] = A.
  Proof.
    induction A; cbn; trivial.
    now rewrite var_subst, IHA.
  Qed.

  Theorem Soundness A phi :
    A ⊢IE phi -> hsat_L HP A <= hsat HP phi.
  Proof.
    intros H. apply Soundness' with (sigma:=var_term) in H.
    now rewrite var_subst, var_subst_L in H.
  Qed.

End Soundness.

      

(** ** Lindenbaum Algebra *)

Instance lb_alg : HeytingAlgebra.
Proof.
  unshelve eapply (@Build_HeytingAlgebra (@form Sigma)).
  - intros phi psi. exact ([phi] ⊢IE psi).
  - exact ⊥.
  - intros phi psi. exact (phi ∧ psi).
  - intros phi psi. exact (phi ∨ psi).
  - intros phi psi. exact (phi --> psi).
  - intros phi. now apply Ctx.
  - intros phi psi theta H1 H2. apply IE with (phi0:=psi); trivial.
    apply Weak with (A:=[]); auto.
  - intros phi. cbn. now apply Exp, Ctx.
  - intros phi psi theta. cbn. split.
    + intros [H1 H2]. now apply CI.
    + intros H. split; [apply (CE1 H) | apply (CE2 H)].
  - intros phi psi theta. cbn. split.
    + intros [H1 H2]. eapply DE. apply Ctx; auto.
      eapply Weak. exact H1. firstorder.
      eapply Weak. exact H2. firstorder.
    + intros H; split.
      * apply (IE (phi := phi ∨ psi)); try now apply DI1, Ctx.
        apply II. eapply Weak; eauto.
      * apply (IE (phi := phi ∨ psi)); try now apply DI2, Ctx.
        apply II. eapply Weak; eauto.
  - intros phi psi theta. cbn. split.
    + intros H. apply II. apply (IE (phi := theta ∧ phi)).
      * apply II. eapply Weak; eauto.
      * apply CI; apply Ctx; auto.
    + intros H. apply (IE (phi:=phi)); try now eapply CE2, Ctx.
      apply (IE (phi:=theta)); try now eapply CE1, Ctx.
      apply II. eapply Weak; eauto.
Defined.

Lemma lb_alg_iff phi :
  Top <= phi <-> [] ⊢IE phi.
Proof.
  cbn. split; intros H.
  - apply (IE (phi := ¬ ⊥)); apply II; eauto using Ctx.
  - eapply Weak; eauto.
Qed.

Instance lb_calg : CompleteHeytingAlgebra :=
  @completion_calgebra lb_alg.

Definition lb_Pr P v : lb_calg :=
  embed (Pred P v).

  


(** ** Completeness *)

Lemma nameless_equiv_all' A phi :
  exists t, A ⊢IE phi[t..] <-> [p[↑] | p ∈ A] ⊢IE phi.
Proof.
  destruct (find_unused_L (phi::A)) as [n HN].
  exists (var_term n). apply nameless_equiv_all.
  - intros psi H. apply HN; auto.
  - apply HN; auto.
Qed.

Lemma nameless_equiv_ex' A phi psi :
  exists t, (psi[t..]::A) ⊢IE phi <-> (psi::[p[↑] | p ∈ A]) ⊢IE phi[↑].
Proof.
  destruct (find_unused_L (phi::psi::A)) as [n HN].
  exists (var_term n). apply nameless_equiv_ex.
  - intros theta H. apply HN; auto.
  - apply HN; auto.
  - apply HN; auto.
Qed.

Lemma lindenbaum_hsat phi :
  down phi ≡ proj1_sig (hsat lb_Pr phi).
Proof.
  induction phi using form_ind_subst; simp hsat in *.
  - rewrite down_bot. reflexivity.
  - cbn. reflexivity.
  - rewrite (@down_impl lb_alg phi psi), IHphi, IHphi0. now destruct hsat, hsat.
  - rewrite (@down_meet lb_alg phi psi), IHphi, IHphi0. now destruct hsat, hsat.
  - rewrite (@down_join lb_alg phi psi), IHphi, IHphi0. now destruct hsat, hsat.
  - cbn. split; intros psi H'.
    + intros X [HX [t Ht]]. change (psi ∈ proj1_sig (exist normal X HX)).
      eapply Ht. rewrite <- H. apply AllE, H'.
    + apply AllI. destruct (@nameless_equiv_all' ([psi]) phi) as [t <-].
      apply H, H'. exists (proj2_sig (hsat lb_Pr phi[t..])), t. now destruct hsat.
  - cbn. split; intros psi H'.
    + intros X [XD HX]. apply XD. intros theta HT. apply (ExE H').
      destruct (@nameless_equiv_ex' ([psi]) theta phi) as [t <-].
      assert (exists i : term, equiv_HA (hsat lb_Pr phi[t..]) (hsat lb_Pr phi[i..])) by now eexists.
      specialize (HX (hsat lb_Pr phi[t..]) H0).
      apply Weak with (A:=[phi[t..]]); auto.
      apply HT, HX. rewrite <- H. now apply Ctx.
    + specialize (H' (down (∃ phi))). apply H'.
      exists (@down_normal lb_alg (∃ phi)). intros X [t ?].
      intros ? ?. eapply H0 in H1.
      revert x H1. fold (hset_sub (proj1_sig (hsat lb_Pr phi[t..])) (down (∃ phi))).
      rewrite <- H. apply down_mono. eapply ExI, Ctx; eauto.
Qed.

Lemma lindenbaum_eqH phi :
  eqH (embed phi) (hsat lb_Pr phi).
Proof.
  unfold eqH. cbn. now rewrite <- lindenbaum_hsat.
Qed.

Lemma lb_calg_iff phi :
  Top <= hsat lb_Pr phi <-> nil ⊢IE phi.
Proof.
  cbn. rewrite <- lindenbaum_hsat.
  rewrite <- down_top, <- lb_alg_iff. split.
  - apply down_inj.
  - apply down_mono.
Qed.

(*Lemma lbcompleteness A phi :
  hsat_L lb_Pr A <= hsat lb_Pr phi -> A ⊢IE phi.
Proof.
  intros H. unfold hsat_L in H.
Admitted.*)



(** ** Summary *)

Definition hentail A phi :=
  forall (HA : CompleteHeytingAlgebra) (HP : forall P, Vector.t term (pred_ar P) -> HA), hsat_L HP A <= hsat HP phi.

Definition hvalid phi :=
  forall (HA : CompleteHeytingAlgebra) (HP : forall P, Vector.t term (pred_ar P) -> HA), Top <= hsat HP phi.

Theorem hcompleteness phi :
  hvalid phi -> nil ⊢IE phi.
Proof.
  intros H.
  specialize (H lb_calg lb_Pr).
  now apply lb_calg_iff.
Qed.

Theorem hsoundness phi :
  nil ⊢IE phi -> hvalid phi.
Proof.
  intros H HA HP. rewrite (@top_hsat_L _ HP). now apply Soundness.
Qed.



(*** Boolean algebras ***)

Definition boolean' (HA : HeytingAlgebra) :=
  forall x : HA, Impl (Impl x Bot) Bot <= x.

Lemma boolean_completion' HA :
  boolean' HA -> boolean' (@completion_calgebra HA).
Proof.
  intros H. intros [X HX]; cbn. intros a Ha.
  unfold hset_impl in Ha. apply HX.
  intros b Hb. specialize (Ha (Impl b Bot)).
  eapply Rtra; try apply H. apply Impl1, Ha.
  intros c Hc. unfold hset_bot, hset_elem.
  rewrite Meet_com, Impl1. eapply Rtra; try now apply Hb.
  apply Impl1. assert (H' : Meet b (Impl b Bot) <= Impl b Bot) by apply Meet3.
  apply Impl1 in H'. eapply Rtra; try eassumption. now repeat rewrite <- Meet1.
Qed.

Definition boolean (HA : HeytingAlgebra) :=
  forall x y : HA, Impl (Impl x y) x <= x.

Lemma boolean_completion HA :
  boolean HA -> boolean (@completion_calgebra HA).
Proof.
  intros H. intros [X HX] [Y HY]; cbn. intros a Ha.
  unfold hset_impl in Ha. apply HX.
  intros b Hb. specialize (Ha (Impl b Bot)).
  eapply Rtra; try apply H. apply Impl1, Hb, Ha.
  intros c Hc. apply HY. intros d Hd. apply Rtra with Bot; try apply Bot1.
  assert (H' : Meet (Impl b Bot) c <= Impl b Bot) by apply Meet2.
  apply Impl1 in H'. eapply Rtra; try eassumption. repeat rewrite <- Meet1.
  repeat split; auto. eapply Rtra; try apply Meet3. now apply Hb.
Qed.

Instance clb_alg : HeytingAlgebra.
Proof.
  unshelve eapply (@Build_HeytingAlgebra (@form Sigma)).
  - intros phi psi. exact ([phi] ⊢CE psi).
  - exact ⊥.
  - intros phi psi. exact (phi ∧ psi).
  - intros phi psi. exact (phi ∨ psi).
  - intros phi psi. exact (phi --> psi).
  - intros phi. now apply Ctx.
  - intros phi psi theta H1 H2. apply IE with (phi0:=psi); trivial.
    apply Weak with (A:=[]); auto.
  - intros phi. cbn. now apply Exp, Ctx.
  - intros phi psi theta. cbn. split.
    + intros [H1 H2]. now apply CI.
    + intros H. split; [apply (CE1 H) | apply (CE2 H)].
  - intros phi psi theta. cbn. split.
    + intros [H1 H2]. eapply DE. apply Ctx; auto.
      eapply Weak. exact H1. firstorder.
      eapply Weak. exact H2. firstorder.
    + intros H; split.
      * apply (IE (phi := phi ∨ psi)); try now apply DI1, Ctx.
        apply II. eapply Weak; eauto.
      * apply (IE (phi := phi ∨ psi)); try now apply DI2, Ctx.
        apply II. eapply Weak; eauto.
  - intros phi psi theta. cbn. split.
    + intros H. apply II. apply (IE (phi := theta ∧ phi)).
      * apply II. eapply Weak; eauto.
      * apply CI; apply Ctx; auto.
    + intros H. apply (IE (phi:=phi)); try now eapply CE2, Ctx.
      apply (IE (phi:=theta)); try now eapply CE1, Ctx.
      apply II. eapply Weak; eauto.
Defined.

Lemma clb_alg_boolean :
  boolean clb_alg.
Proof.
  intros phi psi. cbn. eapply IE; try apply Pc. now apply Ctx.
Qed.

Lemma clb_alg_iff phi :
  Top <= phi <-> [] ⊢CE phi.
Proof.
  cbn. split; intros H.
  - apply (IE (phi := ¬ ⊥)); apply II; eauto using Ctx.
  - eapply Weak; eauto.
Qed.

Instance clb_calg : CompleteHeytingAlgebra :=
  @completion_calgebra clb_alg.

Definition clb_Pr P v : clb_calg :=
  embed (Pred P v).

Lemma cnameless_equiv_all' A phi :
  exists t, A ⊢CE phi[t..] <-> [p[↑] | p ∈ A] ⊢CE phi.
Proof.
  destruct (find_unused_L (phi::A)) as [n HN].
  exists (var_term n). apply nameless_equiv_all.
  - intros psi H. apply HN; auto.
  - apply HN; auto.
Qed.

Lemma cnameless_equiv_ex' A phi psi :
  exists t, (psi[t..]::A) ⊢CE phi <-> (psi::[p[↑] | p ∈ A]) ⊢CE phi[↑].
Proof.
  destruct (find_unused_L (phi::psi::A)) as [n HN].
  exists (var_term n). apply nameless_equiv_ex.
  - intros theta H. apply HN; auto.
  - apply HN; auto.
  - apply HN; auto.
Qed.

Lemma clindenbaum_hsat phi :
  down phi ≡ proj1_sig (hsat clb_Pr phi).
Proof.
  induction phi using form_ind_subst; simp hsat in *.
  - rewrite down_bot. reflexivity.
  - cbn. reflexivity.
  - rewrite (@down_impl clb_alg phi psi), IHphi, IHphi0. now destruct hsat, hsat.
  - rewrite (@down_meet clb_alg phi psi), IHphi, IHphi0. now destruct hsat, hsat.
  - rewrite (@down_join clb_alg phi psi), IHphi, IHphi0. now destruct hsat, hsat.
  - cbn. split; intros psi H'.
    + intros X [HX [t Ht]]. change (psi ∈ proj1_sig (exist normal X HX)).
      eapply Ht. rewrite <- H. apply AllE, H'.
    + apply AllI. destruct (@cnameless_equiv_all' ([psi]) phi) as [t <-].
      apply H, H'. exists (proj2_sig (hsat clb_Pr phi[t..])), t. now destruct hsat.
  - cbn. split; intros psi H'.
    + intros X [XD HX]. apply XD. intros theta HT. apply (ExE H').
      destruct (@cnameless_equiv_ex' ([psi]) theta phi) as [t <-].
      assert (exists i : term, equiv_HA (hsat clb_Pr phi[t..]) (hsat clb_Pr phi[i..])) by now eexists.
      specialize (HX (hsat clb_Pr phi[t..]) H0).
      apply Weak with (A:=[phi[t..]]); auto.
      apply HT, HX. rewrite <- H. now apply Ctx.
    + specialize (H' (down (∃ phi))). apply H'.
      exists (@down_normal clb_alg (∃ phi)). intros X [t ?].
      intros ? ?. eapply H0 in H1.
      revert x H1. fold (hset_sub (proj1_sig (hsat clb_Pr phi[t..])) (down (∃ phi))).
      rewrite <- H. apply down_mono. eapply ExI, Ctx; eauto.
Qed.

Lemma clb_calg_iff phi :
  Top <= hsat clb_Pr phi <-> nil ⊢CE phi.
Proof.
  cbn. rewrite <- clindenbaum_hsat.
  rewrite <- down_top, <- clb_alg_iff. split.
  - apply down_inj.
  - apply down_mono.
Qed.

Definition bvalid phi :=
  forall (HA : CompleteHeytingAlgebra) (HP : forall P, Vector.t term (pred_ar P) -> HA), boolean HA -> Top <= hsat HP phi.

Theorem bcompleteness phi :
  bvalid phi -> nil ⊢CE phi.
Proof.
  intros H.
  specialize (H clb_calg clb_Pr (boolean_completion clb_alg_boolean)).
  now apply clb_calg_iff.
Qed.

End Lindenbaum.
