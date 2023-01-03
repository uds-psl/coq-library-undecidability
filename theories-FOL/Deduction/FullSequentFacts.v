(* * Natural Deduction *)

From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.

From FOL Require Import FullSyntax Theories.
From FOL.Deduction Require Export FullSequent.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Local Set Implicit Arguments.
Local Unset Strict Implicit.
Require Import Lia.


Set Default Proof Using "Type".

#[local] Ltac comp := repeat (progress (cbn in *; autounfold in *)).

Section Sequent_def.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  #[local] Existing Instance falsity_on.

  (* **** Context management and Weakening *)

  Lemma ctx_out A A' phi psi :
    (phi :: A ++ A') ⊢f psi -> (A ++ phi :: A') ⊢f psi.
  Proof.
    intros H. enough (H' : forall B B', rev B ++ B' = A -> (rev B ++ phi :: B' ++ A') ⊢f psi).
    { specialize (H' (rev A) nil). rewrite rev_involutive in H'. apply H', app_nil_r. }
    induction B; intros B' <-; cbn in *.
    - assumption.
    - rewrite <- app_assoc; cbn. apply Perm. apply (IHB (a :: B')). now rewrite <- app_assoc.
  Qed.

  Lemma ctx_in A A' phi psi :
    (A ++ phi :: A') ⊢f psi -> (phi :: A ++ A') ⊢f psi.
  Proof.
    intros H. enough (H' : forall B B', rev B' ++ B = A -> (rev B' ++ phi :: B ++ A') ⊢f psi).
    { now apply (H' A nil). }
    induction B; intros B' <-; cbn in *.
    - now rewrite <- (app_nil_r (rev B')).
    - apply Perm. specialize (IHB (a :: B')); cbn in *; repeat (rewrite <- app_assoc in IHB).
      now apply IHB.
  Qed.

  Lemma focus_el A phi psi :
    phi el A -> (phi :: A) ⊢f psi -> A ⊢f psi.
  Proof.
    intros (B & B' & ->) % in_split H. rewrite app_comm_cons in H.
    apply ctx_out, Contr. now apply ctx_in in H.
  Qed.

  Ltac focus t := refine (@focus_el _ t _ _ _); [eauto |].

  Lemma weaken A B phi :
    A ⊢f phi -> A <<= B -> B ⊢f phi.
  Proof.
    intros H; revert B; induction H; intros B H';
    lazymatch goal with
    | [ _ : (?f :: ?A) <<= ?B |- _ ] => focus f
    | _ => idtac
    end; eauto. 2,3,4,5,7: apply cons_incl in H'.
    - apply IHfprv. transitivity (A ++ phi :: psi :: A').
      intros a [? | [-> | [-> | ?]]] % in_app_or; apply in_or_app. all: eauto.
    - apply IL; [apply (IHfprv1 B) | apply (IHfprv2 (psi :: B))]; intuition.
    - apply AL, (IHfprv (phi :: psi :: B)). intuition.
    - apply OL; [apply (IHfprv1 (phi :: B)) | apply (IHfprv2 (psi :: B))]; intuition.
    - refine (AllL _ (IHfprv (phi [t..] :: B) _)). intuition.
    - apply ExL, (IHfprv (phi :: [p[↑] | p ∈ B])). now apply incl_shift, incl_map.
    - now apply AllR,IHfprv, incl_map.
  Qed.

  Theorem subst_Weak A phi xi :
    A ⊢f phi -> [phi[xi] | phi ∈ A] ⊢f phi[xi].
  Proof.
    induction 1 in xi |-*; comp; eauto using in_map.
    - specialize (IHfprv xi). rewrite map_app in *. cbn in *. now apply Perm.
    - apply AllL with (t := subst_term xi t); specialize (IHfprv xi). rewrite subst_comp in *. unfold funcomp in *.
      erewrite subst_ext. 1: apply IHfprv. intros [|n]; try easy. unfold up,funcomp. cbn. rewrite subst_term_comp.
      unfold funcomp. cbn. now rewrite subst_term_id.
    - apply AllR. setoid_rewrite map_map in IHfprv. erewrite map_map, map_ext.
      apply IHfprv. intros ?. comp. rewrite ! subst_comp. apply subst_ext. now intros [|n].
    - apply ExL. specialize (IHfprv ($0 .: (xi >> subst_term ↑))).
      rewrite subst_comp in IHfprv. cbn in IHfprv.
      rewrite map_map in *.
      erewrite !subst_comp.
      erewrite map_ext.
      erewrite subst_ext at 1. erewrite (subst_ext psi).
      1: eapply IHfprv.
      + now intros [|n]; cbn.
      + now intros [|n]; cbn.
      + intros a. cbn. do 2 rewrite subst_comp. apply subst_ext.
        now intros [|n]; cbn.
    - apply ExR with (t := subst_term xi t); specialize (IHfprv xi).
      rewrite subst_comp. rewrite subst_comp in IHfprv. erewrite subst_ext.
      1: apply IHfprv. intros [|n]; try easy. unfold up, funcomp. cbn.
      erewrite subst_term_comp. erewrite subst_term_id; easy.
  Qed.

  Definition cycle_shift n x :=
    if Dec (n = x) then $0 else $(S x).

  Lemma cycle_shift_shift n phi :
    bounded n phi -> phi[cycle_shift n] = phi[↑].
  Proof.
    intros H. apply (bounded_subst H). intros k. unfold cycle_shift. decide _; trivial; lia.
  Qed.

  Lemma cycle_shift_subject n phi :
    bounded (S n) phi -> phi[$n..][cycle_shift n] = phi.
  Proof.
    intros H. erewrite subst_comp, (bounded_subst H), subst_id; trivial.
    intros []; cbn; unfold cycle_shift; decide _; trivial; lia.
  Qed.

  Lemma nameless_equiv_all' A phi n :
    bounded_L n A -> bounded (S n) phi -> [p[↑] | p ∈ A] ⊢f phi <-> A ⊢f phi[$n ..].
  Proof.
    intros H1 H2. split; intros H.
    - apply (subst_Weak ($n..)) in H. rewrite map_map in *.
      erewrite map_ext, map_id in H; try apply H. intros. apply subst_shift.
    - apply (subst_Weak (cycle_shift n)) in H. rewrite (map_ext_in _ (subst_form ↑)) in H.
      + now erewrite cycle_shift_subject in H.
      + intros psi HP. now apply cycle_shift_shift, H1.
  Qed.

  Lemma nameless_equiv_ex' A phi psi n :
    bounded_L n A -> bounded n phi -> bounded (S n) psi -> (psi::[p0[↑] | p0 ∈ A]) ⊢f phi[↑] <-> (psi[$n..]::A) ⊢f phi.
  Proof.
    intros HL Hphi Hpsi. split.
    - intros H % (subst_Weak ($n..)). cbn in *.
      rewrite map_map, (map_ext _ id), map_id in H.
      + now rewrite subst_shift in H.
      + intros. apply subst_shift.
    - intros H % (subst_Weak (cycle_shift n)). cbn in *.
      rewrite (map_ext_in _ (subst_form ↑)) in H.
      + now rewrite cycle_shift_subject, cycle_shift_shift in H.
      + intros theta HT. now apply cycle_shift_shift, HL.
  Qed.

  Lemma nameless_equiv_all A phi :
    { t : term | map (subst_form ↑) A ⊢f phi <-> A ⊢f phi[t..] }.
  Proof.
    destruct (find_bounded_L (phi::A)) as [n H].
    exists $n. eapply nameless_equiv_all'.
    - intros ? ?. apply H. auto.
    - eapply bounded_up; try apply H; auto.
  Qed.

  Lemma nameless_equiv_ex A phi psi :
    { t : term | (phi :: map (subst_form ↑) A) ⊢f psi[↑] <-> (phi[t..]::A) ⊢f psi }.
  Proof.
    destruct (find_bounded_L (phi::psi::A)) as [n H].
    exists $n. apply nameless_equiv_ex'.
    - intros ? ?. apply H. auto.
    - apply H. auto.
    - eapply bounded_up; try apply H; auto.
  Qed.

  Fixpoint big_or (A : list form) : form :=
    match A with
    | cons phi A' => phi ∨ big_or A'
    | nil => ⊥
    end.
  Notation "⋁ A" := (big_or A) (at level 20).

  Lemma or_subst A rho :
    subst_form rho (⋁ A) = ⋁ (map (subst_form rho) A).
  Proof.
    induction A; cbn; try easy.
    now rewrite IHA.
  Qed.

  Lemma context_shift A phi n :
    bounded_L (S n) A -> bounded n phi ->
    (A ⊢f phi[↑]) <-> [ psi[$n..] | psi ∈ A] ⊢f phi.
  Proof.
    intros HL Hphi. split.
    - intros H % (subst_Weak ($n..)). comp.
      enough (phi = phi[↑][($n)..]) as ->. eassumption.
      rewrite subst_comp, subst_id. try easy. now intros [|m].
    - intros H % (subst_Weak (cycle_shift n)). rewrite map_map in *.
      rewrite (map_ext_in _ id), map_id, cycle_shift_shift in H. 1-2: assumption.
      intros ? ? % HL. rewrite cycle_shift_subject; unfold id; tauto.
  Qed.

  Ltac use_free H := try intros ? ?; eapply bounded_up; [ apply H; intuition | lia].


  Lemma or_char A B phi :
    A ⊢f (⋁ B) -> (forall psi A', psi el B -> A' ⊢f psi -> A' ⊢f phi) -> A ⊢f phi.
  Proof.
    enough (H : forall a, A ⊢f a -> forall B, a = (⋁ B) -> forall phi, (forall psi A', psi el B -> A' ⊢f psi -> A' ⊢f phi) ->
              A ⊢f phi) by (intros H' H''; apply (H _ H' B eq_refl phi H'')). clear B phi.
    intros a; induction 1; intros B Heq goal Hgoal; try eauto.
    all: try (destruct B; cbn in Heq; discriminate Heq); subst.
    - subst. induction B.
      + apply Exp, Ax.
      + apply OL; [refine (Hgoal a _ _ (Ax _ _)) | apply IHB]; firstorder.
    - destruct B; [discriminate| ]. cbn in *. injection Heq. intros _ ->%Eqdep_dec.inj_pair2_eq_dec. 1: apply (Hgoal f A); intuition.
      apply dec_falsity.
    - destruct B; [discriminate| injection Heq; intros ->%Eqdep_dec.inj_pair2_eq_dec ->%Eqdep_dec.inj_pair2_eq_dec]. 1: apply (IHfprv B eq_refl goal); firstorder.
      all: apply dec_falsity.
    - apply ExL. apply (IHfprv _ (or_subst B ↑)). intros ? A' [psi [<- Hin]] % in_map_iff Hprv.
      destruct (find_bounded_L (goal :: psi :: A')) as [x Hx].
      apply context_shift with (n := x) in Hprv; [| use_free Hx | use_free Hx ]. specialize (Hgoal _ _ Hin Hprv).
      now apply context_shift with (n := x) in Hgoal; [| use_free Hx | use_free Hx ].
  Qed.

  Lemma or_el A phi B :
    A ⊢f phi -> phi el B -> A ⊢f (⋁ B).
  Proof.
    intros Hprv Hel. induction B; destruct Hel; subst; cbn; eauto.
  Qed.

  Lemma or_weak A B B' :
    A ⊢f (⋁ B) -> B <<= B' -> A ⊢f (⋁ B').
  Proof.
    intros H Hsub. apply (or_char H). intros psi A' Hel Hpsi. apply or_el with (phi := psi); intuition.
  Qed.

  Lemma or_single A B phi :
    A ⊢f (⋁ B) -> (forall psi, psi el B -> psi = phi) -> A ⊢f phi.
  Proof.
    intros H H'. apply (or_char H). now intros psi A' -> % H'.
  Qed.
End Sequent_def.


#[global] Notation "A ⊢f phi" := (fprv A phi) (at level 30).
#[global] Notation "⋁ A" := (big_or A) (at level 20).
#[global] Ltac use_free H := try intros ? ?; eapply bounded_up; [ apply H; intuition | lia].
