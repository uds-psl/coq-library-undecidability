Require Export Undecidability.Synthetic.Definitions.
From Undecidability.FOL.Util Require Import Syntax Syntax_facts FullDeduction FullDeduction_facts FullTarski.


Section FixSignature.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Instance ff : falsity_flag := falsity_on.

  
  Definition axiomatisaion (A : form -> Prop) := decidable A.
  Definition Tvalid (T : form -> Prop) phi :=
    forall D (I : interp D) rho, (forall psi, T psi -> rho ⊨ psi) -> rho ⊨ phi.

  Definition consistent A := ~ A ⊢TI falsity.
  Definition complete A := forall phi, A ⊢TI phi \/ ~ A ⊢TI phi.

  
  Section Axiomatisations.

    Variable A : form -> Prop.
    Hypothesis HA : axiomatisaion A.

    Context {X : Type}.
    Variable P : X -> Prop.

    Definition reduction_both f :=
      (forall x, P x <-> Tvalid A (f x) ) /\ (forall x, P x <-> A ⊢TI (f x)).
    Definition reduction2 :=
      exists f : X -> form, reduction_both f.


    Fact Fact7 : reduction2 -> (exists x, ~ P x) -> consistent A.
    Proof.
      intros [f [H1 H2]] [x Hx] [Gamma []].
      apply Hx, H2. exists Gamma. auto.
    Qed.

    
    Fact Fact9 : consistent A -> complete A -> decidable (fun phi => A ⊢TI phi).
    Proof.
    Admitted.
    
  End Axiomatisations.

  
  Section Model.

    Variable A : form -> Prop.
    Hypothesis HA : axiomatisaion A.
    
    Variable X : Type.
    Variable P : X -> Prop.

    Variable f : X -> form.
    Hypothesis Hf : reduction_both A P f.


    Implicit Type T S : form -> Prop.
    Definition Tincl T S := forall phi, T phi -> S phi .

    Notation "I ⊨ phi" := (forall rho, sat I rho phi) (at level 20). 
    Notation "I ⊨= T" := (forall phi rho, T phi -> sat I rho phi) (at level 20).
    Notation "T <<= S" := (Tincl T S) (at level 10).
    
    Variable standard : forall (T : form -> Prop){D : Type}(I : interp D), Prop.
    Hypothesis std_is_model :
      forall T D (I : interp D), standard T I -> I ⊨= T. 
    Hypothesis std_trans :
      forall T1 T2 D (I : interp D), T1 <<= T2 -> standard T2 I -> standard T1 I.
    
    Definition reconstruct T :=
      forall D (I : interp D), standard T I -> (forall x, I ⊨ (f x) -> P x). 

    

    Fact model_trans T1 T2 : T1 <<= T2 -> forall D (I : interp D), I ⊨= T2 -> I ⊨= T1.
    Proof.
      intros ???????. intuition.
    Qed.
    
    Fact valid_trans T1 T2 phi : T1 <<= T2 -> Tvalid T1 phi -> Tvalid T2 phi.
    Proof.
      intros ?????. intuition.
    Qed.

    Fact Help T {D} (I : interp D):
      (forall rho psi, T psi -> sat I rho psi) <-> I ⊨= T.
    Proof.
      split; intuition.
    Qed.
    


    Theorem Theorem10 :
      (forall x, P x -> A ⊢TI (f x) ) -> reconstruct A -> 
      forall T, A <<= T -> (exists D I, @standard T D I) -> reduction2 T P.
    Proof.
      intros H1 recon T incl (D & I & stdT).
      pose (stdA := stdT).
      apply (std_trans A), recon in stdA; trivial.
      exists f. split; intros x; split.
      - intros H%H1. apply (valid_trans A); trivial.
        unfold Tvalid. now apply tsoundness.
      - intros H. apply stdA. intros rho.
        apply (H D I rho). revert rho.
        now apply Help, std_is_model. 
      - intros [Gamma H]%H1. exists Gamma. intuition.
      - intros H. apply stdA. intros rho.
        specialize (tsoundness H) as S.
        apply (S D I rho).
        now apply Help, std_is_model.         
    Qed.
    

    
  End Model.
  

End FixSignature.
