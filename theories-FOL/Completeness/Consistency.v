(* ** Consistency *)

From FOL Require Import FragmentSyntax Theories.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation Shared.Dec.
From Undecidability Require Import Shared.Libs.PSL.Vectors.Vectors Shared.Libs.PSL.Vectors.VectorForall.
Import ListAutomationNotations.


Section Consistency.
  Context {Σf : funcs_signature} {Σp : preds_signature}.
  Context {HdF : eq_dec Σf} {HdP : eq_dec Σp}.
  Context {HeF : enumerable__T Σf} {HeP : enumerable__T Σp}.

  Definition consistent (T : theory) := ~ T ⊢TC ⊥.
  Definition consistent_max T := consistent T /\ forall f, consistent (T ⋄ f) -> f ∈ T.

  Lemma consistent_prv T phi :
    consistent T -> T ⊢TC phi -> consistent (T ⋄ phi).
  Proof.
    intros HT Hphi. intros Hpsi2. now apply HT, (prv_T_remove Hphi).
  Qed.

  Lemma consistency_inheritance T1 T2 :
    consistent T2 -> T1 ⊑ T2 -> consistent T1.
  Proof.
    intros H H2 H3. now eapply H, Weak_T, H2.
  Qed.

  Fact consistent_neg T phi :
    consistent T -> (¬ phi) ∈ T -> ~ phi ∈ T.
  Proof.
    intros HT H H2. apply HT.
    use_theory [phi; ¬ phi]. 1: intros a [<-|[<-|[]]]; easy.
    eapply IE; apply Ctx; eauto.
  Qed.

  Fact consistent_neg2 T phi :
    consistent T -> (T ⋄ phi) ⊢TC ⊥ -> consistent (T ⋄ (¬ phi)).
  Proof.
    intros HT H. now apply consistent_prv, prv_T_impl.
  Qed.

  Fact consistent_max_out T phi :
    consistent_max T -> ~ phi ∈ T -> ~ consistent (T ⋄ phi).
  Proof.
    intros []; intuition.
  Qed.

  Lemma consistent_max_impl T phi psi :
    consistent_max T -> (phi → psi ∈ T <-> (phi ∈ T -> psi ∈ T)).
  Proof.
    intros; split; destruct H as [H1 H2].
    - intros H H'. apply H2. apply consistent_prv; try assumption.
      use_theory [phi; phi → psi]. 1: intros a [<-|[<-|[]]]; easy.
      eapply IE; apply Ctx; eauto.
    - intros H. apply H2. intros (A & HA1 & HA2) % prv_T_impl.
      apply H1. apply (prv_T_remove (phi := psi)).
      + apply elem_prv, H, H2, consistent_prv. assumption. use_theory A.
        eapply IE. 1: eapply Pc. apply II, Exp. eapply IE; [eapply Weak; [apply HA2| intros a Ha; now right]|]. apply Ctx; now left.
      + use_theory (psi :: A). 1: intros a [<-|Ha]; cbv; eauto.
        eapply IE; [eapply Weak; [apply HA2| intros a Ha; now right]|]. apply II,Ctx; right; now left.
  Qed.

  Section Classical.
    Hypothesis XM : forall X, X \/ ~ X.
    Ltac indirect := match goal with
                      | [ |- ?H ] => destruct (XM H); [assumption | exfalso]
                    end.

    Lemma inconsistent T phi :
      ~ consistent (T ⋄ phi) -> T ⋄ phi ⊢TC ⊥.
    Proof.
      destruct (XM (T ⋄ phi ⊢TC ⊥)); tauto.
    Qed.

    Lemma consistent_max_out2 T phi :
      consistent_max T -> ~ phi ∈ T -> (¬ phi) ∈ T.
    Proof.
      intros [HT1 HT2] H2. now apply consistent_max_out, inconsistent, consistent_neg2, HT2 in H2.
    Qed.
  End Classical.
End Consistency.
