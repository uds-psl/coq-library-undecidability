From Equations Require Import Equations.
From Undecidability.FOLC Require Export FullND Heyting.

(* ** Heyting Evaluation *)

Section Lindenbaum.

Context {Sigma : Signature}.
Context {eq_dec_Funcs : eq_dec Funcs}.
Context {eq_dec_Preds : eq_dec Preds}.

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
    setoid_rewrite subst_size. lia.
  Qed.
  Next Obligation.
    setoid_rewrite subst_size. lia.
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
      setoid_rewrite map_subst with (t:=t) at 1. reflexivity.
    - rewrite IHprv. simp hsat. apply Inf2. exists t[sigma]. now asimpl.
    - rewrite IHprv. apply Sup2. exists t[sigma]. now asimpl.
    - specialize (IHprv1 sigma). simp hsat in IHprv1.
      rewrite (meet_sup_expansion IHprv1). apply Sup1. intros x [t ->].
      rewrite Meet_hsat_L. setoid_rewrite map_subst with (t:=t) at 1.
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

  Theorem Soundness A phi :
    A ⊢IE phi -> hsat_L HP A <= hsat HP phi.
  Proof.
    intros H. apply Soundness' with (sigma:=var_term) in H.
    now rewrite var_subst, var_subst_L in H.
  Qed.

End Soundness.

      

(** ** Lindenbaum Algebra *)

Section Completeness.

  (*Context { b : peirce }.*)

  Notation "A ⊢E phi" := (@prv Sigma intu expl A phi) (at level 30).

  Instance lb_alg : HeytingAlgebra.
  Proof.
    unshelve eapply (@Build_HeytingAlgebra (@form Sigma)).
    - intros phi psi. exact ([phi] ⊢E psi).
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
    Top <= phi <-> [] ⊢E phi.
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
      + apply AllI. destruct (@nameless_equiv_all' _ intu expl _ _ ([psi]) phi) as [t <-].
        apply H, H'. exists (proj2_sig (hsat lb_Pr phi[t..])), t. now destruct hsat.
    - cbn. split; intros psi H'.
      + intros X [XD HX]. apply XD. intros theta HT. apply (ExE H').
        destruct (@nameless_equiv_ex' _ intu expl _ _ ([psi]) theta phi) as [t <-].
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
    Top <= hsat lb_Pr phi <-> nil ⊢E phi.
  Proof.
    cbn. rewrite <- lindenbaum_hsat.
    rewrite <- down_top, <- lb_alg_iff. split.
    - apply down_inj.
    - apply down_mono.
  Qed.

End Completeness.



(* ** Intuitionistic ND *)

Definition hvalid phi :=
  forall (HA : CompleteHeytingAlgebra) HP, Top <= hsat HP phi.

Theorem hcompleteness phi :
  hvalid phi -> nil ⊢IE phi.
Proof.
  intros H.
  specialize (H lb_calg lb_Pr).
  now eapply lb_calg_iff.
  Unshelve.
Qed.

Theorem hsoundness phi :
  nil ⊢IE phi -> hvalid phi.
Proof.
  intros H HA HP. rewrite (@top_hsat_L _ HP). now apply Soundness.
Qed.



(** ** Boolean algebras ***)

Definition boolean (HA : HeytingAlgebra) :=
  forall x y : HA, Impl (Impl x y) x <= x.

Section BSoundness.

  Context { HA : CompleteHeytingAlgebra }.
  Context { HP : forall (P : Preds), Vector.t term (pred_ar P) -> HA }.

  Theorem BSoundness' A phi :
    boolean HA -> A ⊢CE phi -> forall sigma, hsat_L HP ([p[sigma] | p ∈ A]) <= hsat HP phi[sigma].
  Proof.
    intros HB. remember class as b.
    induction 1; intros sigma; asimpl in *; simp hsat in *; fold subst_form in *.
    all: try specialize (IHprv Heqb); try specialize (IHprv1 Heqb); try specialize (IHprv2 Heqb).
    - apply Impl1. rewrite <- IHprv. apply Meet_hsat_L.
    - specialize (IHprv1 sigma). specialize (IHprv2 sigma).
      simp hsat in *. apply Impl1 in IHprv1.
      rewrite <- IHprv1, <- Meet1. now split.
    - apply Inf1. intros x [t ->]. asimpl. rewrite <- IHprv.
      setoid_rewrite map_subst with (t:=t) at 1. reflexivity.
    - rewrite IHprv. simp hsat. apply Inf2. exists t[sigma]. now asimpl.
    - rewrite IHprv. apply Sup2. exists t[sigma]. now asimpl.
    - specialize (IHprv1 sigma). simp hsat in IHprv1.
      rewrite (meet_sup_expansion IHprv1). apply Sup1. intros x [t ->].
      rewrite Meet_hsat_L. setoid_rewrite map_subst with (t:=t) at 1.
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
    - apply Impl1. eapply Rtra; try apply Meet3. apply HB.
  Qed.

  Theorem BSoundness A phi :
    boolean HA -> A ⊢CE phi -> hsat_L HP A <= hsat HP phi.
  Proof.
    intros HB H. apply BSoundness' with (sigma:=var_term) in H; trivial.
    now rewrite var_subst, var_subst_L in H.
  Qed.

End BSoundness.



(** ** Generalised Lindenbaum Algebras *)

Section Completeness.

  Variable gprv : list form -> form -> Prop.

  Notation "A ⊢ phi" := (gprv A phi) (at level 30).

  Hypothesis gCtx : forall A phi, phi el A -> A ⊢ phi.
  Hypothesis gIE : forall A phi psi, A ⊢ (phi --> psi) -> A ⊢ phi -> A ⊢ psi.
  Hypothesis gII : forall A phi psi, (phi::A) ⊢ psi -> A ⊢ (phi --> psi).
  Hypothesis gExp : forall A phi, A ⊢ ⊥ -> A ⊢ phi.
  Hypothesis gCI : forall A phi psi, A ⊢ phi -> A ⊢ psi -> A ⊢ (phi ∧ psi).
  Hypothesis gCE1 : forall A phi psi, A ⊢ (phi ∧ psi) -> A ⊢ phi.
  Hypothesis gCE2 : forall A phi psi, A ⊢ (phi ∧ psi) -> A ⊢ psi.
  Hypothesis gDI1 : forall A phi psi, A ⊢ phi -> A ⊢ (phi ∨ psi).
  Hypothesis gDI2 : forall A phi psi, A ⊢ psi -> A ⊢ (phi ∨ psi).
  Hypothesis gDE : forall A phi psi theta, A ⊢ (phi ∨ psi) -> (phi :: A) ⊢ theta -> (psi :: A) ⊢ theta -> A ⊢ theta.
  Hypothesis gWeak : forall A B phi, A ⊢ phi -> A <<= B -> B ⊢ phi.

  Instance glb_alg : HeytingAlgebra.
  Proof.
    unshelve eapply (@Build_HeytingAlgebra (@form Sigma)).
    - intros phi psi. exact ([phi] ⊢ psi).
    - exact ⊥.
    - intros phi psi. exact (phi ∧ psi).
    - intros phi psi. exact (phi ∨ psi).
    - intros phi psi. exact (phi --> psi).
    - intros phi. now apply gCtx.
    - intros phi psi theta H1 H2. apply gIE with (phi:=psi); trivial.
      apply gWeak with (A:=[]); auto.
    - intros phi. cbn. now apply gExp, gCtx.
    - intros phi psi theta. cbn. split.
      + intros [H1 H2]. now apply gCI.
      + intros H. split; [apply (gCE1 H) | apply (gCE2 H)].
    - intros phi psi theta. cbn. split.
      + intros [H1 H2]. eapply gDE. apply gCtx; auto.
        eapply gWeak. exact H1. firstorder.
        eapply gWeak. exact H2. firstorder.
      + intros H; split.
        * apply (gIE (phi := phi ∨ psi)); try now apply gDI1, gCtx.
          apply gII. eapply gWeak; eauto.
        * apply (gIE (phi := phi ∨ psi)); try now apply gDI2, gCtx.
          apply gII. eapply gWeak; eauto.
    - intros phi psi theta. cbn. split.
      + intros H. apply gII. apply (gIE (phi := theta ∧ phi)).
        * apply gII. eapply gWeak; eauto.
        * apply gCI; apply gCtx; auto.
      + intros H. apply (gIE (phi:=phi)); try now eapply gCE2, gCtx.
        apply (gIE (phi:=theta)); try now eapply gCE1, gCtx.
        apply gII. eapply gWeak; eauto.
  Defined.

  Lemma glb_alg_iff phi :
    Top <= phi <-> [] ⊢ phi.
  Proof.
    cbn. split; intros H.
    - apply (gIE (phi := ¬ ⊥)); apply gII; eauto using gCtx.
    - eapply gWeak; eauto.
  Qed.

  Instance glb_calg : CompleteHeytingAlgebra :=
    @completion_calgebra glb_alg.

  Definition glb_Pr P v : glb_calg :=
    embed (Pred P v). 

  (** ** Completeness *)

  Hypothesis gAllI : forall A phi, [psi[form_shift] | psi ∈ A] ⊢ phi -> A ⊢ (∀ phi).
  Hypothesis gAllE : forall A t phi, A ⊢ (∀ phi) -> A ⊢ phi[t..].
  Hypothesis gExI : forall A t phi, A ⊢ phi[t..] -> A ⊢ (∃ phi).
  Hypothesis gExE : forall A phi psi, A ⊢ (∃ phi) -> (phi :: [theta[form_shift] | theta ∈ A]) ⊢ psi[form_shift] -> A ⊢ psi.
  Hypothesis gnameless_equiv_all' : forall A phi, exists t, A ⊢ phi[t..] <-> [p[form_shift] | p ∈ A] ⊢ phi.
  Hypothesis gnameless_equiv_ex' : forall A phi psi, exists t, (psi[t..] :: A) ⊢ phi <-> (psi :: [p[form_shift] | p ∈ A]) ⊢ phi[form_shift].

  Lemma glindenbaum_hsat phi :
    down phi ≡ proj1_sig (hsat glb_Pr phi).
  Proof.
    induction phi using form_ind_subst; simp hsat in *.
    - rewrite down_bot. reflexivity.
    - cbn. reflexivity.
    - rewrite (@down_impl glb_alg phi psi), IHphi, IHphi0. now destruct hsat, hsat.
    - rewrite (@down_meet glb_alg phi psi), IHphi, IHphi0. now destruct hsat, hsat.
    - rewrite (@down_join glb_alg phi psi), IHphi, IHphi0. now destruct hsat, hsat.
    - cbn. split; intros psi H'.
      + intros X [HX [t Ht]]. change (psi ∈ proj1_sig (exist normal X HX)).
        eapply Ht. rewrite <- H. apply gAllE, H'.
      + apply gAllI. destruct (@gnameless_equiv_all' ([psi]) phi) as [t <-].
        apply H, H'. exists (proj2_sig (hsat glb_Pr phi[t..])), t. now destruct hsat.
    - cbn. split; intros psi H'.
      + intros X [XD HX]. apply XD. intros theta HT. apply (gExE H').
        destruct (@gnameless_equiv_ex' ([psi]) theta phi) as [t <-].
        assert (exists i : term, equiv_HA (hsat glb_Pr phi[t..]) (hsat glb_Pr phi[i..])) by now eexists.
        specialize (HX (hsat glb_Pr phi[t..]) H0).
        apply gWeak with (A:=[phi[t..]]); auto.
        apply HT, HX. rewrite <- H. now apply gCtx.
      + specialize (H' (down (∃ phi))). apply H'.
        exists (@down_normal glb_alg (∃ phi)). intros X [t ?].
        intros ? ?. eapply H0 in H1.
        revert x H1. fold (hset_sub (proj1_sig (hsat glb_Pr phi[t..])) (down (∃ phi))).
        rewrite <- H. apply down_mono. eapply gExI, gCtx; eauto.
  Qed.

  Lemma glindenbaum_eqH phi :
    eqH (embed phi) (hsat glb_Pr phi).
  Proof.
    unfold eqH. cbn. now rewrite <- glindenbaum_hsat.
  Qed.

  Lemma glb_calg_iff phi :
    Top <= hsat glb_Pr phi <-> nil ⊢ phi.
  Proof.
    cbn. rewrite <- glindenbaum_hsat.
    rewrite <- down_top, <- glb_alg_iff. split.
    - apply down_inj.
    - apply down_mono.
  Qed.

End Completeness.



(** ** Completeness for Boolean algebras *)

Instance clb_alg : HeytingAlgebra.
Proof.
  apply (@glb_alg (@prv _ class expl)); eauto 2. apply Weak.
Defined.

Instance clb_calg : CompleteHeytingAlgebra.
Proof.
  apply (@glb_calg (@prv _ class expl)); eauto 2. apply Weak.
Defined.

Definition clb_Pr P (v : vector term (pred_ar P)) : clb_calg.
Proof.
  apply glb_Pr with P. exact v.
Defined.

Lemma clb_alg_boolean :
  boolean clb_alg.
Proof.
  intros phi psi. cbn. eapply IE; try apply Pc. now apply Ctx.
Qed.

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

Definition bvalid phi :=
  forall (HA : CompleteHeytingAlgebra) HP, boolean HA -> Top <= hsat HP phi.

Theorem bcompleteness phi :
  bvalid phi -> nil ⊢CE phi.
Proof.
  intros H.
  specialize (H clb_calg clb_Pr (boolean_completion clb_alg_boolean)).
  apply glb_calg_iff in H; eauto 2; clear H0.
  - apply nameless_equiv_all'.
  - apply nameless_equiv_ex'.
Qed.

Theorem bsoundness phi :
  nil ⊢CE phi -> bvalid phi.
Proof.
  intros H HA HP HB. rewrite (@top_hsat_L _ HP). now apply BSoundness.
Qed.

End Lindenbaum.
