Set Implicit Arguments.
Require Import List Omega Lia.
From Undecidability.HOU Require Import std.std calculus.calculus unification.higher_order_unification.
Import ListNotations.


(** * System Unification *)
Section SystemUnification.

  Variable (X: Const).


  Definition eq: Type := exp X * exp X.
  Definition eqs := list eq.

  Implicit Types (sigma: fin -> exp X) (e: eq) (E : eqs).

  Definition eq_typing  Gamma e A := Gamma ⊢ fst e : A /\ Gamma ⊢ snd e : A.

  Notation "Gamma ⊢₂ e : A" := (eq_typing Gamma e A) (at level 80, e at level 99).


  Reserved Notation  "Gamma ⊢₊₊ E : L" (at level 80, E at level 99).

  Inductive eqs_typing Gamma : eqs -> list type -> Prop :=
  | eqs_typing_nil: Gamma ⊢₊₊ nil : nil
  | eqs_typing_cons s t A E L: Gamma ⊢ s : A -> Gamma ⊢ t : A -> Gamma ⊢₊₊ E : L -> Gamma ⊢₊₊ ((s,t) :: E) : A :: L
  where  "Gamma ⊢₊₊ E : L" := (eqs_typing Gamma E L).

  Hint Constructors eqs_typing : core.


  Definition left_side E := map fst E.
  Definition right_side E := map snd E.

  Lemma left_typing Gamma E L: Gamma ⊢₊₊ E : L -> Gamma ⊢₊ left_side E : L.
  Proof. induction 1; cbn; eauto. Qed.
  Lemma right_typing Gamma E L: Gamma ⊢₊₊ E : L -> Gamma ⊢₊ right_side E : L.
  Proof. induction 1; cbn; eauto. Qed.

  Lemma typing_combine Gamma E L:
    Gamma ⊢₊ left_side E : L -> Gamma ⊢₊ right_side E : L -> Gamma ⊢₊₊ E : L.
  Proof.
    intros H1 H2; induction E in L, H1, H2 |-*; inv H1; inv H2; eauto.
    destruct a; eauto.
  Qed.


  Hint Resolve left_typing right_typing : core.

  Definition vars' (e: eq) := vars (fst e) ++ vars (snd e).
  Definition Vars' (E: list eq) := flat_map vars' E.

  Lemma Vars'_cons e E: Vars' (e :: E) = vars' e ++ Vars' E.
  Proof. reflexivity. Qed.

  Lemma Vars'_app E1 E2:
    Vars' (E1 ++ E2) = Vars' E1 ++ Vars' E2.
  Proof.
    unfold Vars'; now rewrite !flat_map_app.
  Qed.

  Hint Rewrite Vars'_cons Vars'_app : simplify.



  Definition subst_eq sigma e := let (s, t) := e in (sigma • s, sigma • t).

  Notation "sigma •₊₊ E" := (map (subst_eq sigma) E) (at level 69, right associativity).


  Lemma left_subst_eqs E sigma:
    left_side (sigma •₊₊ E) = sigma •₊ left_side E.
  Proof.
    unfold left_side; induction E as [| []]; cbn; congruence.
  Qed.

  Lemma right_subst_eqs E sigma:
    right_side (sigma •₊₊ E) = sigma •₊ right_side E.
  Proof.
    unfold right_side; induction E as [| []]; cbn; congruence.
  Qed.

  Hint Rewrite left_subst_eqs right_subst_eqs : simplify.


  Lemma equiv_eqs_pointwise sigma E:
    (sigma •₊ left_side E) ≡₊ (sigma •₊ right_side E) -> (forall s t, (s, t) ∈ E -> sigma • s ≡ sigma • t).
  Proof.
    induction E; cbn; intuition; subst.
    all: eapply equiv_lstep_cons_inv in H; intuition.
  Qed.


  Lemma equiv_pointwise_eqs sigma E:
    (forall s t, (s, t) ∈ E -> sigma • s ≡ sigma • t) ->
    (sigma •₊ left_side E) ≡₊ (sigma •₊ right_side E).
  Proof.
    induction E as [| [s t]]; cbn; intros; eauto; intuition.
    rewrite H; intuition.
    rewrite IHE; intuition.
  Qed.


  Lemma eqs_typing_preservation_subst Gamma E L Delta sigma:
      Gamma ⊢₊₊ E : L -> Delta ⊩ sigma : Gamma -> Delta ⊢₊₊ sigma •₊₊ E : L.
  Proof. induction 1; cbn; eauto. Qed.



  Definition all_terms (P: exp X -> Prop) (E: eqs) := forall s t, (s, t) ∈ E -> P s /\ P t.
  Definition all_eqs (P: exp X -> exp X -> Prop) (E: eqs) := forall s t, (s, t) ∈ E -> P s t.



  Lemma all_terms_cons P e E:
    all_terms P (e :: E) -> P (fst e) /\ P (snd e) /\ all_terms P E.
  Proof.
    destruct e as [s t]; intros H; cbn.
    specialize (H s t) as H'; cbn in H'; intuition.
    intros ???; eapply H; cbn; intuition.
  Qed.


  Lemma all_terms_cons_iff P e E:
    all_terms P (e :: E) <-> P (fst e) /\ P (snd e) /\ all_terms P E.
  Proof.
    unfold all_eqs; cbn; split.
    - eauto using all_terms_cons.
    - intros (? & ? & ?) ? ? [->|H']; firstorder.
  Qed.

  Hint Rewrite all_terms_cons_iff : simplify.

  Lemma all_terms_nil P: all_terms P nil.
  Proof. intros ??[]. Qed.

  Lemma all_terms_app P (E1 E2: eqs):
    all_terms P (E1 ++ E2) <-> all_terms P E1 /\ all_terms P E2.
  Proof.
    unfold all_eqs; split.
    - intros H; split; intros s t H'; eapply H; simplify; intuition.
    - intros [H1 H2] s t; simplify; intros [? % H1|? % H2]; intuition.
  Qed.

  Hint Rewrite all_terms_app : simplify.



  Class sysuni :=
  {
    Gammaᵤ'  : ctx;
    Eᵤ'  : eqs;
    Lᵤ'  : list type;
    Hᵤ' : Gammaᵤ' ⊢₊₊ Eᵤ' : Lᵤ';
  }.


  Definition SU (I: sysuni) := exists (Delta: ctx) (sigma: fin -> exp X),
      (Delta ⊩ sigma : Gammaᵤ') /\ forall s t, (s, t) ∈ Eᵤ' -> sigma • s ≡ sigma • t.

  Arguments SU: clear implicits.
  Hint Resolve @Hᵤ' : core.



  Definition linearize_terms (S: list (exp X)) :=
    lambda AppR (var 0) (renL shift S).

  Lemma linearize_terms_subst sigma S: sigma • linearize_terms S = linearize_terms (sigma •₊ S).
  Proof. unfold linearize_terms; asimpl.
         rewrite !map_map; asimpl.
         f_equal. f_equal. eapply map_ext.
         intros ?; now asimpl.
  Qed.

  Lemma linearize_terms_equiv S T:
    linearize_terms S ≡ linearize_terms T <-> S ≡₊ T.
  Proof.
    split.
    - intros [? % list_equiv_anti_ren _] % equiv_lam_elim % equiv_AppR_elim; eauto.
      unfold shift; intros ??; congruence.
    - unfold linearize_terms. now intros ->.
  Qed.

  Lemma linearize_terms_typing Gamma S L A:
    Gamma ⊢₊ S : L -> Gamma ⊢ linearize_terms S : (Arr (rev L) A) → A.
  Proof.
    intros H; econstructor; eapply AppR_typing with (L0 := L).
    eapply listtyping_preservation_under_renaming; eauto.
    intros x ?; cbn; eauto.
    econstructor; eauto; simplify; cbn; intuition.
  Qed.


  Lemma linearize_vars S:
    vars (linearize_terms S) === Vars S.
  Proof.
    split.
    - intros ? H % vars_varof. inv H. eapply varof_vars in H1.
      rewrite AppR_vars in H1. simplify in H1. cbn in H1; intuition.
      discriminate. eapply in_flat_map in H as [? []].
      mapinj. eapply vars_ren in H0 as []. intuition.
      injection H1 as ->. eapply in_flat_map. eexists; eauto.
    - intros x H. eapply varof_vars; econstructor; eapply vars_varof.
      rewrite AppR_vars; simplify; right.
      eapply in_flat_map in H as [y]; eapply in_flat_map; exists (ren shift y).
      intuition. now eapply ren_vars.
  Qed.

  Hint Resolve linearize_terms_typing : core.

  Section Interreducible.

  Global Program Instance uni_sysuni (I: uni X): sysuni :=
     { Gammaᵤ' := Gammaᵤ; Eᵤ' := [(sᵤ, tᵤ)]; Lᵤ' := [Aᵤ]; Hᵤ' := _; }.


   Global Program Instance sysuni_uni (I: sysuni): uni X :=
       {
         Gammaᵤ := Gammaᵤ';
         sᵤ := linearize_terms (left_side Eᵤ');
         tᵤ := linearize_terms (right_side Eᵤ');
         Aᵤ := (Arr (rev Lᵤ') alpha) → alpha;
         H1ᵤ := _;
         H2ᵤ := _;
       }.


   Lemma U_SU: U X ⪯ SU.
   Proof.
     exists (uni_sysuni); intros I.
     split; intros (Delta & sigma & H1 & H2); exists Delta; exists sigma; intuition.
     firstorder; injection H; intros; subst; eauto.
     eapply H2; firstorder.
   Qed.

   Lemma SU_U: SU ⪯ U X.
   Proof.
     exists (sysuni_uni).
     intros I; split; intros (Delta & sigma & H1 & H2); exists Delta; exists sigma; destruct I; intuition;
       cbn [sᵤ tᵤ sysuni_uni] in *.
     rewrite !linearize_terms_subst, linearize_terms_equiv. now apply equiv_pointwise_eqs.
     eapply equiv_eqs_pointwise; eauto.
     now rewrite <-linearize_terms_equiv, <-!linearize_terms_subst.
   Qed.

  End Interreducible.

End SystemUnification.

Arguments SU : clear implicits.
Arguments sysuni : clear implicits.
Arguments Gammaᵤ' {_} {_}.
Arguments Eᵤ' {_} {_}.
Arguments Lᵤ' {_} {_}.


Notation "sigma •₊₊ E" := (map (subst_eq sigma) E) (at level 69, right associativity).
Notation  "Gamma ⊢₊₊ E : L" := (eqs_typing Gamma E L) (at level 80, E at level 99).
Notation "Gamma ⊢₂ e : A" := (eq_typing Gamma e A) (at level 80, e at level 99).

Hint Rewrite all_terms_cons_iff all_terms_app Vars'_app Vars'_cons: simplify.
Hint Resolve all_terms_nil : core.

(** ** Normalisation *)
Definition NSU {X: Const} (I: sysuni X) := exists Delta sigma,
    Delta ⊩ sigma : Gammaᵤ' /\ (forall s t, (s, t) ∈ Eᵤ' -> sigma • s ≡ sigma • t) /\
                 forall x, normal (sigma x).

Lemma SU_NSU X I: SU X I <-> NSU I.
Proof.
  split; intros (Delta & sigma & H1 & H2); [| exists Delta; exists sigma; intuition].
  eapply normalise_subst in H1 as (tau & H5 & H6 & H7).
  pose (theta x := if nth (@Gammaᵤ' _ I) x then tau x else var x).
  exists Delta. exists theta. intuition.
  + intros ???; unfold theta; rewrite H; eapply H7; eauto.
  + rewrite subst_pointwise_equiv with (sigma0 := theta) (tau0 := sigma).
    rewrite subst_pointwise_equiv with (sigma0 := theta) (tau0 := sigma); eauto.
    all: intros ? ?; enough (x ∈ dom Gammaᵤ') as D;
      [domin D; unfold theta; rewrite D|]; eauto.
    all: eapply Vars_listtyping.
    2, 4: eapply in_flat_map; eexists; (intuition eauto).
    2: change t with (snd (s, t)); eapply in_map; eauto.
    2: change s with (fst (s, t)); eapply in_map; eauto.
    eapply right_typing, @Hᵤ'.
    eapply left_typing, @Hᵤ'.
  + unfold theta; destruct nth eqn: ?; [|eauto].
    domin Heqo; eauto.
Qed.
