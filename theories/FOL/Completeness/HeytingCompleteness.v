From Equations Require Import Equations.
From Coq Require Import Arith Lia List Program.Equality.
From Undecidability.FOL Require Import FullSyntax Heyting.Heyting Completeness.HeytingMacNeille.
Import ListNotations.

Section Lindenbaum.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
Context {eq_dec_Funcs : EqDec Σ_funcs}.
Context {eq_dec_Preds : EqDec Σ_preds}.


(** ** Lindenbaum Algebra *)

Section Completeness.

  (*Context { b : peirce }.*)

  Notation "A ⊢E phi" := (A ⊢I phi) (at level 30).

  Instance lb_alg : HeytingAlgebra.
  Proof.
    unshelve eapply (@Build_HeytingAlgebra (@form _ _ _ falsity_on)).
    - intros phi psi. exact ([phi] ⊢E psi).
    - exact ⊥.
    - intros phi psi. exact (phi ∧ psi).
    - intros phi psi. exact (phi ∨ psi).
    - intros phi psi. exact (phi → psi).
    - intros phi. apply Ctx. now left.
    - intros phi psi theta H1 H2. apply IE with (phi:=psi); trivial.
      apply Weak with (A:=[]); auto. 2: firstorder. econstructor. apply H2.
    - intros phi. cbn. apply Exp, Ctx. now left.
    - intros phi psi theta. cbn. split.
      + intros [H1 H2]. now apply CI.
      + intros H. split; [apply (CE1 H) | apply (CE2 H)].
    - intros phi psi theta. cbn. split.
      + intros [H1 H2]. eapply DE. apply Ctx; auto. 1: now left.
        eapply Weak. exact H1. firstorder.
        eapply Weak. exact H2. firstorder.
      + intros H; split.
        * apply (IE (phi := phi ∨ psi)). 2: try apply DI1, Ctx. 2: now left.
          apply II. eapply Weak; eauto. 1: firstorder. 
        * apply (IE (phi := phi ∨ psi)); try apply DI2, Ctx; try now left.
          apply II. eapply Weak; eauto. firstorder.
    - intros phi psi theta. cbn. split.
      + intros H. apply II. apply (IE (phi := theta ∧ phi)).
        * apply II. eapply Weak. 1: apply H. firstorder.
        * apply CI; apply Ctx; firstorder.
      + intros H. eapply IE. 2: eapply CE2, Ctx; now left.
        eapply IE. 1: eapply II, Weak. 1: apply H. 2: eapply CE1, Ctx; now left. firstorder.
  Defined.

  Lemma lb_alg_iff phi :
    Top <= phi <-> [] ⊢E phi.
  Proof.
    cbn. split; intros H.
    - apply (IE (phi := ¬ ⊥)); apply II; eauto using Ctx. apply Ctx. now left.
    - eapply Weak; eauto; firstorder.
  Qed.

  Instance lb_calg : CompleteHeytingAlgebra :=
    @completion_calgebra lb_alg.

  Definition lb_Pr P v : lb_calg :=
    embed (atom P v).

  (** ** Heyting Completeness *)

  Lemma lindenbaum_hsat phi :
    down phi ≡ proj1_sig (hsat lb_Pr phi).
  Proof.
    induction phi  as [| |[]|[]] using form_ind_subst; simp hsat in *.
    - rewrite down_bot. reflexivity.
    - cbn. reflexivity.
    - rewrite (@down_meet lb_alg f1 f2), IHphi, IHphi0. now destruct hsat, hsat.
    - rewrite (@down_join lb_alg f1 f2), IHphi, IHphi0. now destruct hsat, hsat.
    - rewrite (@down_impl lb_alg f1 f2), IHphi, IHphi0. now destruct hsat, hsat.
    - cbn. split; intros psi H'.
      + intros X [HX [t Ht]]. change (psi ∈ proj1_sig (exist normal X HX)).
        eapply Ht. rewrite <- H. apply AllE, H'. 
      + apply AllI. destruct (@nameless_equiv_all _ _ _ intu ([psi]) f2) as [t Ht]. apply Ht.
        apply H, H'. exists (proj2_sig (hsat lb_Pr f2[t..])), t. now destruct hsat.
    - cbn. split; intros psi H'.
      + intros X [XD HX]. apply XD. intros theta HT. apply (ExE H').
        destruct (@nameless_equiv_ex _ _ _ intu ([psi]) f2 theta) as [t Ht]. apply Ht.
        assert (exists i : term, equiv_HA (hsat lb_Pr f2[t..]) (hsat lb_Pr f2[i..])) by now eexists.
        specialize (HX (hsat lb_Pr f2[t..]) H0).
        apply Weak with (A:=[f2[t..]]); auto. 2: now apply ListAutomation.incl_shift.
        apply HT, HX. rewrite <- H. apply Ctx. now left.
      + specialize (H' (down (∃ f2))). apply H'.
        exists (@down_normal lb_alg (∃ f2)). intros X [t ?].
        intros ? ?. eapply H0 in H1.
        revert x H1. fold (hset_sub (proj1_sig (hsat lb_Pr f2[t..])) (down (∃ f2))).
        rewrite <- H. apply down_mono. eapply ExI, Ctx; eauto. now left.
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
  hvalid phi -> nil ⊢I phi.
Proof.
  intros H.
  specialize (H lb_calg lb_Pr).
  now eapply lb_calg_iff.
  Unshelve.
Qed.



(* ** Generalised Lindenbaum Algebras *)

Section Completeness.

  Variable gprv : list form -> form -> Prop.

  Notation "A ⊢ phi" := (gprv A phi) (at level 55).

  Hypothesis gCtx : forall A phi, In phi A -> A ⊢ phi.
  Hypothesis gIE : forall A phi psi, A ⊢ (phi → psi) -> A ⊢ phi -> A ⊢ psi.
  Hypothesis gII : forall A phi psi, (phi::A) ⊢ psi -> A ⊢ (phi → psi).
  Hypothesis gExp : forall A phi, A ⊢ ⊥ -> A ⊢ phi.
  Hypothesis gCI : forall A phi psi, A ⊢ phi -> A ⊢ psi -> A ⊢ (phi ∧ psi).
  Hypothesis gCE1 : forall A phi psi, A ⊢ (phi ∧ psi) -> A ⊢ phi.
  Hypothesis gCE2 : forall A phi psi, A ⊢ (phi ∧ psi) -> A ⊢ psi.
  Hypothesis gDI1 : forall A phi psi, A ⊢ phi -> A ⊢ (phi ∨ psi).
  Hypothesis gDI2 : forall A phi psi, A ⊢ psi -> A ⊢ (phi ∨ psi).
  Hypothesis gDE : forall A phi psi theta, A ⊢ (phi ∨ psi) -> (phi :: A) ⊢ theta -> (psi :: A) ⊢ theta -> A ⊢ theta.
  Hypothesis gWeak : forall A B phi, A ⊢ phi -> incl A B -> B ⊢ phi.

  Instance glb_alg : HeytingAlgebra.
  Proof.
    unshelve eapply (@Build_HeytingAlgebra (form)).
    - intros phi psi. exact ([phi] ⊢ psi).
    - exact ⊥.
    - intros phi psi. exact (phi ∧ psi).
    - intros phi psi. exact (phi ∨ psi).
    - intros phi psi. exact (phi → psi).
    - intros phi. apply gCtx. now left.
    - intros phi psi theta H1 H2. apply gIE with (phi:=psi); trivial.
      apply gWeak with (A:=[]); auto. firstorder.
    - intros phi. cbn. apply gExp, gCtx. now left.
    - intros phi psi theta. cbn. split.
      + intros [H1 H2]. now apply gCI.
      + intros H. split; [apply (gCE1 H) | apply (gCE2 H)].
    - intros phi psi theta. cbn. split.
      + intros [H1 H2]. eapply gDE. apply gCtx; auto. 1: now left.
        eapply gWeak. exact H1. firstorder.
        eapply gWeak. exact H2. firstorder.
      + intros H; split.
        * apply (gIE (phi := phi ∨ psi)); try apply gDI1, gCtx.
          apply gII. eapply gWeak; eauto. 1: firstorder. now left.
        * apply (gIE (phi := phi ∨ psi)); try apply gDI2, gCtx.
          apply gII. eapply gWeak; eauto. 1: firstorder. now left.
    - intros phi psi theta. cbn. split.
      + intros H. apply gII. apply (gIE (phi := theta ∧ phi)).
        * apply gII. eapply gWeak; eauto. firstorder.
        * apply gCI; apply gCtx; auto. 1: right; now left. now left.
      + intros H. apply (gIE (phi:=phi)). 2: eapply gCE2, gCtx; now left.
        eapply gIE. 1: eapply gII, gWeak. 1: apply H. 2: eapply gCE1, gCtx; now left.
        firstorder.
  Defined.

  Lemma glb_alg_iff phi :
    Top <= phi <-> [] ⊢ phi.
  Proof.
    cbn. split; intros H.
    - apply (gIE (phi := ¬ ⊥)); apply gII. 2: apply gCtx; now left. apply H.
    - eapply gWeak; eauto. firstorder.
  Qed.

  Instance glb_calg : CompleteHeytingAlgebra :=
    @completion_calgebra glb_alg.

  Definition glb_Pr P v : glb_calg :=
    embed (atom P v). 

  Hypothesis gAllI : forall A phi, map (subst_form ↑) A ⊢ phi -> A ⊢ (∀ phi).
  Hypothesis gAllE : forall A t phi, A ⊢ (∀ phi) -> A ⊢ phi[t..].
  Hypothesis gExI : forall A t phi, A ⊢ phi[t..] -> A ⊢ (∃ phi).
  Hypothesis gExE : forall A phi psi, A ⊢ (∃ phi) -> (phi :: map (subst_form ↑) A) ⊢ psi[↑] -> A ⊢ psi.
  Hypothesis gnameless_equiv_all' : forall A phi, exists t, A ⊢ phi[t..] <-> map (subst_form ↑) A ⊢ phi.
  Hypothesis gnameless_equiv_ex' : forall A phi psi, exists t, (psi[t..] :: A) ⊢ phi <-> (psi :: map (subst_form ↑) A) ⊢ phi[↑].

  Lemma glindenbaum_hsat phi :
    down phi ≡ proj1_sig (hsat glb_Pr phi).
  Proof.
    induction phi as [| |[]phi ? psi ?|[] phi ?] using form_ind_subst; simp hsat in *.
    - rewrite down_bot. reflexivity.
    - cbn. reflexivity.
    - rewrite (@down_meet glb_alg phi psi), IHphi, IHphi0. now destruct hsat, hsat.
    - rewrite (@down_join glb_alg phi psi), IHphi, IHphi0. now destruct hsat, hsat.
    - rewrite (@down_impl glb_alg phi psi), IHphi, IHphi0. now destruct hsat, hsat.
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
        apply HT, HX. rewrite <- H. apply gCtx. now left. apply ListAutomation.incl_shift. easy.
      + specialize (H' (down (∃ phi))). apply H'.
        exists (@down_normal glb_alg (∃ phi)). intros X [t ?].
        intros ? ?. eapply H0 in H1.
        revert x H1. fold (hset_sub (proj1_sig (hsat glb_Pr phi[t..])) (down (∃ phi))).
        rewrite <- H. apply down_mono. eapply gExI, gCtx; eauto. now left.
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



(** ** Boolean Completeness *)
#[local] Hint Constructors prv : core.
Instance clb_alg : HeytingAlgebra.
Proof.
  apply (@glb_alg (@prv _ _ _ class)); eauto 2.
  apply Weak.
Defined.

Instance clb_calg : CompleteHeytingAlgebra.
Proof.
  apply (@glb_calg (@prv _ _ _ class)); eauto 2. apply Weak.
Defined.

Definition clb_Pr P (v : Vector.t term (ar_preds P)) : clb_calg.
Proof.
  apply glb_Pr with P. exact v.
Defined.

Lemma clb_alg_boolean :
  boolean clb_alg.
Proof.
  intros phi psi. cbn. eapply IE; try apply Pc. apply Ctx. now left.
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
  bvalid phi -> nil ⊢C phi.
Proof.
  intros H.
  specialize (H clb_calg clb_Pr (boolean_completion clb_alg_boolean)).
  apply glb_calg_iff in H; eauto 2; clear H0.
  - intros A psi. edestruct (nameless_equiv_all (p:=class) A psi) as (x & Hx).
    exists x. now rewrite Hx.
  - intros A psi chi. edestruct (nameless_equiv_ex (p:=class) A chi psi) as (x & Hx).
    exists x. now rewrite Hx.
Qed.

End Lindenbaum.
