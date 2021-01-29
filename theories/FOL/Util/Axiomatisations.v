Require Export Undecidability.Synthetic.Definitions.
From Undecidability.FOL.Util Require Import Syntax Syntax_facts FullDeduction FullDeduction_facts FullTarski.

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

  Definition consistent A := ~ A ⊢TI falsity.
  Definition complete A := forall phi, A ⊢TI phi \/ ~ A ⊢TI phi.

  
  Section Axiomatisations.

    Variable A : form -> Prop.

    Context {X : Type}.
    Variable P : X -> Prop.

    
    Definition reduction_both f :=
      (forall x, P x <-> Tvalid A (f x) )
      /\ (forall x, P x <-> A ⊢TI (f x) /\ A ⊢TC (f x)).
    Definition reduction2 :=
      exists f : X -> form, reduction_both f.


    Fact Fact7 : reduction2 -> (exists x, ~ P x) -> consistent A.
    Proof.
      intros [f (H1 & H2)] [x Hx] [Gamma []].
      apply Hx, H2. split. 2: apply class_from_intu.
      all: exists Gamma; auto.
    Qed.

    
    Fact Fact9 : consistent A -> complete A -> decidable (fun phi => A ⊢TI phi).
    Proof.
    Admitted.


    
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
