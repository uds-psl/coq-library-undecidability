From Undecidability.FOL.Util Require Import Syntax Syntax_facts FullDeduction FullDeduction_facts FullTarski.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec.
From Equations Require Import Equations.
Require Import ConstructiveEpsilon.
Require Import List.

Section Post.
  
  Definition mu (p : nat -> Prop) :
    (forall x, dec (p x)) -> ex p -> sig p.
  Proof.
    apply constructive_indefinite_ground_description_nat_Acc.
  Qed.

  Definition ldecidable {X} (p : X -> Prop) :=
    forall x, p x \/ ~ p x.

  Lemma weakPost X (p : X -> Prop) :
    discrete X -> ldecidable p -> enumerable p -> enumerable (fun x => ~ p x) -> decidable p.
  Proof.
    intros [E] % discrete_iff Hl [f Hf] [g Hg].
    eapply decidable_iff. econstructor. intros x.
    assert (exists n, f n = Some x \/ g n = Some x) by (destruct (Hl x); firstorder).
    destruct (mu (fun n => f n = Some x \/ g n = Some x)) as [n HN]; trivial.
    - intros n. exact _.
    - decide (f n = Some x); decide (g n = Some x); firstorder.
  Qed.

End Post.


Notation "T ⊢TC phi" := (@tprv _ _ _ class T phi) (at level 55).




Section FixSignature.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Instance ff : falsity_flag := falsity_on.


  Lemma class_from_intu' Gamma phi :  Gamma ⊢I phi -> Gamma ⊢C phi.
  Proof.
    induction 1; try now constructor.
    - eapply IE; eauto.
    - eapply ExI; eauto.
    - eapply ExE; eauto.
    - eapply CE; eauto.
    - eapply CE; eauto.
    - eapply DE; eauto.
  Qed.
  
  
  Lemma class_from_intu Gamma phi : Gamma ⊢TI phi -> Gamma ⊢TC phi.
  Proof.
    intros [A H]. exists A. split; intuition.
    now apply class_from_intu'.
  Qed.

  

  Definition Tvalid (T : form -> Prop) phi :=
    forall D (I : interp D) rho, (forall psi, T psi -> rho ⊨ psi) -> rho ⊨ phi.

  Definition complete A := forall phi, A ⊢TC phi \/ A ⊢TC ¬ phi.

  
  Section Axiomatisations.

    Hypothesis eq_dec_Funcs : eq_dec syms.
    Hypothesis eq_dec_Preds : eq_dec preds.

    Variable A : form -> Prop.

    Context {X : Type}.
    Variable P : X -> Prop.

    
    Definition reduction_both f :=
      (forall x, P x <-> Tvalid A (f x) )
      /\ (forall x, P x <-> A ⊢TI (f x) /\ A ⊢TC (f x)).
    Definition reduction2 :=
      exists f : X -> form, reduction_both f.


    Fact Fact7 : reduction2 -> (exists x, ~ P x) -> ~ A ⊢TI ⊥.
    Proof.
      intros [f (H1 & H2)] [x Hx] [Gamma []].
      apply Hx, H2. split. 2: apply class_from_intu. all: exists Gamma; auto. 
    Qed.

    Lemma TC_enum :
      enumerable (fun phi : form => A ⊢TC phi).
    Admitted.

    Definition stripneg `{falsity_flag} (phi : form) : option form :=
      match phi with 
      | bin Impl phi ⊥ => Some phi
      | _ => None
      end.

    Instance eq_dec_ff :
      eq_dec falsity_flag.
    Proof.
      intros ff ff'. unfold dec. decide equality.
    Qed.

    Lemma stripneg_spec `{falsity_flag} {phi psi} :
      stripneg phi = Some psi -> phi = ¬ psi.
    Proof.
      depelim phi; cbn; try destruct b0; try discriminate.
      - inversion H0. apply inj_pair2_eq_dec' in H2 as ->; eauto. cbn. discriminate.
      - depelim phi2; cbn; try destruct b0; try discriminate.
        inversion H0. apply inj_pair2_eq_dec' in H2 as ->; eauto. congruence.
    Qed.
    
    Fact Fact9 : (~ A ⊢TC ⊥) -> complete A -> decidable (fun phi => A ⊢TC phi).
    Proof.
      intros H1 H2.
      assert (H : forall phi, ~ A ⊢TC phi <-> A ⊢TC ¬ phi).
      - intros phi. split; intros H.
        + destruct (H2 phi) as [H3|H3]; tauto.
        + intros [B[HB1 HB2]]. destruct H as [C[HC1 HC2]].
          apply H1. exists (B ++ C). split.
          * intros psi. rewrite in_app_iff. intuition.
          * eapply IE; eapply Weak; eauto.
      - apply weakPost.
        + apply discrete_iff. constructor. apply dec_form; trivial.
          all: intros ? ?; unfold dec; decide equality.
        + intros phi. rewrite H. apply H2.
        + apply TC_enum.
        + destruct TC_enum as [f Hf].
          exists (fun n => match f n with Some phi => stripneg phi | _ => None end).
          intros phi. rewrite H. rewrite (Hf (¬ phi)).
          split; intros [n Hn]; exists n.
          * now rewrite Hn.
          * destruct (f n) as [psi|]; try discriminate. now rewrite (stripneg_spec Hn).
    Qed.


    
  End Axiomatisations.

  
  Section Model.

    Variable A : form -> Prop.

    Variable X : Type.
    Variable P : X -> Prop.
    Variable f : X -> form.
    

    Implicit Type T S : form -> Prop.
    Definition Tincl T S := forall phi, T phi -> S phi .

    Notation "I ⊨ phi" := (forall rho, sat I rho phi) (at level 20). 
    Notation "I ⊨= T" := (forall phi rho, T phi -> sat I rho phi) (at level 20).
    Notation "T <<= S" := (Tincl T S) (at level 10).
    
    Variable standard : forall {D : Type}(I : interp D), Prop.

    Definition reconstruct T :=
      forall D (I : interp D), standard I -> I ⊨= T -> (forall x, I ⊨ (f x) -> P x). 

    

    Fact model_trans {T1 T2 D}{I : interp D} : T1 <<= T2 -> I ⊨= T2 -> (I ⊨= T1).
    Proof. intros ??. intuition. Qed.
    
    Fact valid_trans {T1 T2 phi} : T1 <<= T2 -> Tvalid T1 phi -> Tvalid T2 phi.
    Proof. intros ?????. intuition. Qed.

    Fact Help T {D} (I : interp D):
      (forall rho psi, T psi -> sat I rho psi) <-> I ⊨= T.
    Proof. split; intuition. Qed.



    Theorem Theorem10 :
      (forall x, P x -> A ⊢TI (f x) ) -> reconstruct A -> 
      forall T, A <<= T -> (exists D I, @standard D I /\ I ⊨= T) -> reduction2 T P.
    Proof.
      intros H1 recon T incl (D & I & [std MT]).
      specialize (model_trans incl MT) as MA.
      
      exists f. repeat split.
      - intros H%H1. apply (valid_trans incl); trivial.
        unfold Tvalid. now apply tsoundness.
      - intros H. eapply recon; trivial.
        intros rho. apply (H D I rho). revert rho.
        now apply Help.
      - revert H. intros [Gamma ]%H1. exists Gamma. split; intuition.
      - apply class_from_intu.
        revert H. intros [Gamma ]%H1. exists Gamma. split; intuition.
      - intros [H _]. eapply recon; trivial.
        specialize (tsoundness H) as S.
        intros rho. apply (S D I rho).
        now apply Help.
    Qed.

    
  End Model.
  

End FixSignature.
