(* * Kripke Semantics *)

From Undecidability Require Import FOL.Semantics.Kripke.FullCore FOL.Deduction.FullCore.
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
    - intros v d Hv. apply IHHprv. intros psi [psi' [<- Hp]] % in_map_iff. rewrite ksat_comp. eapply ksat_mon, HA, Hp. apply Hv.
    - rewrite ksat_comp. eapply ksat_ext. 2: eapply (IHHprv u rho HA u (eval rho t) ). 2: apply M. 
      unfold funcomp. now intros [].
    - exists (@eval Σ_funcs Σ_preds D (@k_interp _ _ _ M) rho t). eapply (ksat_ext _ (xi:=(t.. >> eval rho))).
      + now intros [|x].
      + erewrite <- ksat_comp. apply IHHprv, HA.
    - destruct (IHHprv1 u rho HA) as [j Hj].
      assert (forall psi, (j .: rho) ⊩(u,M) psi[↑] <-> rho ⊩(u,M) psi) as Hup by (eapply ksat_comp; eapply ksat_ext; now intros [|]).
      apply Hup, IHHprv2. intros psi' [<- | [psiU [<- HpsiA]]%in_map_iff].
      + apply Hj.
      + eapply Hup, HA, HpsiA.
    - exfalso. eapply IHHprv, HA.
    - edestruct IHHprv as [HL HR]. 1:apply HA. easy.
    - edestruct IHHprv as [HL HR]. 1:apply HA. easy.
    - edestruct IHHprv1 as [HL | HR]. 1: apply HA.
      + apply IHHprv2. intros phi' [-> | Hin]; intuition.
      + apply IHHprv3. intros phi' [-> | Hin]; intuition.
  Qed.


  Lemma ksoundness' (phi : form) :
    [] ⊢I phi -> kvalid phi.
  Proof.
    intros H % ksoundness. firstorder.
  Qed.

End KSoundness.

