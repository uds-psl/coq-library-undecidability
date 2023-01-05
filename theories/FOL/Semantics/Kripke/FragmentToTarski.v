(* * Kripke Semantics *)

From Undecidability Require Import FOL.Semantics.Tarski.FragmentFacts.
From Undecidability Require Import FOL.Semantics.Kripke.FragmentCore.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.


Local Set Implicit Arguments.
Local Unset Strict Implicit.

Local Notation vec := Vector.t.

#[local] Ltac comp := repeat (progress (cbn in *; autounfold in *)).

(* ** Connection to Tarski Semantics *)

Section ToTarski.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Program Instance interp_kripke {domain} (I : interp domain) : kmodel domain :=
    {| nodes := unit ; reachable u v := True |}.
  Next Obligation.
    - now apply I in X.
  Defined.

  Lemma kripke_tarski {ff : falsity_flag} domain (I : interp domain) rho phi :
    rho ⊨ phi <-> ksat (interp_kripke I) tt rho phi.
  Proof.
    revert rho. induction phi; intros rho.
    - tauto.
    - tauto.
    - destruct b0. cbn. rewrite IHphi1, IHphi2. intuition. destruct v. tauto.
    - destruct q. cbn. split; intros H; cbn in *.
      + intros i. apply IHphi, H.
      + intros i. apply IHphi, H.
  Qed.

  Lemma kvalid_valid b (phi : form b) :
    kvalid phi -> valid phi.
  Proof.
    intros H domain I rho. apply kripke_tarski, H.
  Qed.

  Lemma ksatis_satis b (phi : form b) :
    satis phi -> ksatis phi.
  Proof.
    intros (domain & I & rho & ?). eapply kripke_tarski in H.
    now exists domain, (interp_kripke I), tt, rho.
  Qed.

End ToTarski.
