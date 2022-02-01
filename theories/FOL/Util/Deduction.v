(* * Natural Deduction *)

From Undecidability Require Import FOL.Util.Tarski FOL.Util.Syntax FOL.Util.Syntax_facts.
Import FragmentSyntax.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Local Set Implicit Arguments.
Require Import Lia.


Ltac comp := repeat (progress (cbn in *; autounfold in *)).

Inductive peirce := class | intu.
Existing Class peirce.

Section ND_def.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Reserved Notation "A ⊢ phi" (at level 61).
  
  (* ** Definition *)

  Implicit Type p : peirce.
  Implicit Type ff : falsity_flag.

  Inductive prv : forall (ff : falsity_flag) (p : peirce), list form -> form -> Prop :=
  | II {ff} {p} A phi psi : phi::A ⊢ psi -> A ⊢ phi --> psi
  | IE {ff} {p} A phi psi : A ⊢ phi --> psi -> A ⊢ phi -> A ⊢ psi
  | AllI {ff} {p} A phi : map (subst_form ↑) A ⊢ phi -> A ⊢ ∀ phi
  | AllE {ff} {p} A t phi : A ⊢ ∀ phi -> A ⊢ phi[t..]
  | Exp {p} A phi : prv p A falsity -> prv p A phi
  | Ctx {ff} {p} A phi : phi el A -> A ⊢ phi
  | Pc {ff} A phi psi : prv class A (((phi --> psi) --> phi) --> phi)
  where "A ⊢ phi" := (prv _ A phi).

  Arguments prv {_} _ _.

  Context {ff : falsity_flag}.
  Context {p : peirce}.

  Lemma impl_prv A B phi :
    (rev B ++ A) ⊢ phi -> A ⊢ (B ==> phi).
  Proof.
    revert A; induction B; intros A; cbn; simpl_list; intros.
    - firstorder.
    - eapply II. now eapply IHB.
  Qed.

  Theorem Weak A B phi :
    A ⊢ phi -> A <<= B -> B ⊢ phi.
  Proof.
    intros H. revert B.
    induction H; intros B HB; try unshelve (solve [econstructor; intuition]); try now econstructor.
  Qed.

  Hint Constructors prv : core.

  Theorem subst_Weak A phi xi :
    A ⊢ phi -> [phi[xi] | phi ∈ A] ⊢ phi[xi].
  Proof.
    induction 1 in xi |-*; comp.
    1-7:eauto using in_map.
    - apply AllI. setoid_rewrite map_map in IHprv. erewrite map_map, map_ext.
      apply IHprv. intros ?. cbn. now rewrite up_form.
    - specialize (IHprv xi). apply AllE with (t := t`[xi]) in IHprv. rewrite subst_comp in *.
      erewrite subst_ext; try apply IHprv. intros [|]; cbn; trivial.
      unfold funcomp. now setoid_rewrite subst_term_shift.
  Qed.

  Definition cycle_shift n x :=
    if Dec (n = x) then $0 else $(S x).
  Lemma cycle_shift_shift n phi :
    bounded n phi -> phi[cycle_shift n] = phi[↑].
  Proof.
    intros H. apply (bounded_subst H). intros k. unfold cycle_shift. destruct (Dec _); trivial; lia.
  Qed.

  Lemma cycle_shift_subject n phi :
    bounded (S n) phi -> phi[$n..][cycle_shift n] = phi.
  Proof.
    intros H. erewrite subst_comp, (bounded_subst H), subst_id; trivial.
    intros []; cbn; unfold cycle_shift; destruct (Dec _); trivial; lia.
  Qed.

  Lemma nameless_equiv_all' A phi n :
    bounded_L n A -> bounded (S n) phi -> [f[↑] | f ∈ A] ⊢ phi <-> A ⊢ phi[$n..].
  Proof.
    intros H1 H2. split; intros H.
    - apply (subst_Weak ($n..)) in H. rewrite map_map in *.
      erewrite map_ext, map_id in H; try apply H. intros. apply subst_shift.
    - apply (subst_Weak (cycle_shift n)) in H. rewrite (map_ext_in _ (subst_form ↑)) in H.
      + now rewrite cycle_shift_subject in H.
      + intros psi HP. now apply cycle_shift_shift, H1.
  Qed.

  Lemma nameless_equiv_all A phi :
    { t : nat | map (subst_form ↑) A ⊢ phi <-> A ⊢ phi[$t..] }.
  Proof.
    destruct (find_bounded_L (phi::A)) as [n H].
    exists n. apply nameless_equiv_all'.
    - intros ? ?. apply H. auto.
    - eapply bounded_up; try apply H; auto.
  Qed.
    
End ND_def.


Local Hint Constructors prv : core.

Arguments prv {_ _ _ _} _ _.
Notation "A ⊢ phi" := (prv A phi) (at level 30).
Notation "A ⊢C phi" := (@prv _ _ _ class A phi) (at level 30).
Notation "A ⊢I phi" := (@prv _ _ _ intu A phi) (at level 30).
Notation "A ⊢M phi" := (@prv _ _ falsity_off intu A phi) (at level 30).

Section Soundness.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Lemma soundness {ff : falsity_flag} A phi :
    A ⊢I phi -> valid_ctx A phi.
  Proof.
    remember intu as p.
    induction 1; intros D I rho HA; comp.
    - intros Hphi. apply IHprv; trivial. intros ? []; subst. assumption. now apply HA.
    - now apply IHprv1, IHprv2.
    - intros d. apply IHprv; trivial. intros psi [psi'[<- H' % HA]] % in_map_iff.
      eapply sat_comp. now comp.
    - eapply sat_comp, sat_ext. 2: apply (IHprv Heqp D I rho HA (eval rho t)). now intros [].
    - apply (IHprv Heqp) in HA. firstorder.
    - firstorder.
    - discriminate.
  Qed.

  Lemma soundness' {ff : falsity_flag} phi :
    [] ⊢I phi -> valid phi.
  Proof.
    intros H % soundness. firstorder.
  Qed.

  Lemma intuitionistic_is_classical {ff:falsity_flag} A phi :
    A ⊢I phi -> A ⊢C phi.
  Proof.
  induction 1; comp.
  - now apply II, IHprv.
  - now eapply IE, IHprv2.
  - now eapply AllI, IHprv.
  - now eapply AllE, IHprv.
  - now eapply Exp, IHprv.
  - now eapply Ctx, H.
  - apply Pc.
  Qed.

  Lemma classical_soundness (LEM:forall P:Prop, P \/ ~P) {ff : falsity_flag} A phi :
    A ⊢C phi -> valid_ctx A phi.
  Proof.
    induction 1; intros D I rho HA; comp.
    - intros Hphi. apply IHprv; trivial. intros ? []; subst. assumption. now apply HA.
    - now apply IHprv1, IHprv2.
    - intros d. apply IHprv; trivial. intros psi [psi'[<- H' % HA]] % in_map_iff.
      eapply sat_comp. now comp.
    - eapply sat_comp, sat_ext. 2: apply (IHprv D I rho HA (eval rho t)). now intros [].
    - apply (IHprv) in HA. firstorder.
    - firstorder.
    - intros H. 
      destruct (LEM (rho ⊨ phi)) as [Ht|Hf]. 1:easy.
      destruct (LEM (rho ⊨ psi)) as [Ht2|Hf2]; tauto.
  Qed.


End Soundness.
