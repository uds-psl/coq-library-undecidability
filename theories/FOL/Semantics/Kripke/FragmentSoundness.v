(* * Kripke Semantics *)

From Undecidability Require Import FOL.Semantics.Kripke.FragmentCore FOL.Deduction.FragmentCore.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.

Set Default Proof Using "Type".

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Local Notation vec := Vector.t.

#[local] Ltac comp := repeat (progress (cbn in *; autounfold in *)).


(* ** Soundness **)

Section KSoundness.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ff : falsity_flag}.

  Ltac clean_ksoundness :=
    match goal with
    | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
    | [ H : (?A -> ?B), H2 : (?A -> ?B) -> _ |- _] => specialize (H2 H)
    end.

  Lemma ksoundness A (phi : form) :
    A ⊢I phi -> kvalid_ctx A phi.
  Proof.
    intros Hprv D M. remember intu as s. induction Hprv; subst; cbn; intros u rho HA.
    all: repeat (clean_ksoundness + discriminate). all: (eauto || comp; eauto).
    - intros v Hr Hpi. eapply IHHprv. intros ? []; subst; eauto using ksat_mon.
    - eapply IHHprv1. 3: eapply IHHprv2. all: eauto. apply M.
    - intros d. apply IHHprv. intros psi [psi' [<- Hp]] % in_map_iff. cbn. rewrite ksat_comp. apply HA, Hp.
    - rewrite ksat_comp. eapply ksat_ext. 2: eapply (IHHprv u rho HA (eval rho t)). 
      unfold funcomp. now intros [].
    - now apply IHHprv in HA.
  Qed.

  Lemma ksoundness' (phi : form) :
    [] ⊢I phi -> kvalid phi.
  Proof.
    intros H % ksoundness. firstorder.
  Qed.

End KSoundness.

