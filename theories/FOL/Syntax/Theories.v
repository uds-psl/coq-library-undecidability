From Undecidability.FOL.Syntax Require Import Core Facts.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation.
From Undecidability Require Import Shared.Libs.PSL.Vectors.Vectors Shared.Libs.PSL.Vectors.VectorForall.
Require Import Coq.Setoids.Setoid.
Import ListAutomationNotations.
Require Import Arith Lia List.

#[global]
Create HintDb contains_theory.

Declare Scope theory.
Open Scope theory.

Section Theory.
  (* **** Theories *)
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.
  Context {ff : falsity_flag}.

  Definition theory := form -> Prop.
  Definition contains phi (T : theory) := T phi.
  Definition contains_L (A : list form) (T : theory) := forall f, f el A -> contains f T.
  Definition subset_T (T1 T2 : theory) := forall (phi : form), contains phi T1 -> contains phi T2.
  Definition list_T A : theory := fun phi => phi el A.

  Infix "⊏" := contains_L (at level 20) : theory.
  Infix "⊑" := subset_T (at level 20) : theory.
  Infix "∈" := contains (at level 70) : theory.

  Hint Unfold contains : contains_theory.
  Hint Unfold contains_L : contains_theory.
  Hint Unfold subset_T : contains_theory.

  Global Instance subset_T_trans : Transitive subset_T.
  Proof.
    intros T1 T2 T3. intuition.
  Qed.

  Definition extend T (phi : form) := fun psi => T psi \/ psi = phi.
  Infix "⋄" := extend (at level 20).

  Definition closed_T (T : theory) := forall phi, contains phi T -> bounded 0 phi.
  Lemma closed_T_extend T phi :
    closed_T T -> closed phi -> closed_T (T ⋄ phi).
  Proof.
    intros ? ? ? [|]; subst; intuition.
  Qed.

  Section ContainsAutomation.
    Lemma contains_nil T :
      List.nil ⊏ T.
    Proof. intuition. Qed.

    Lemma contains_cons a A T :
      a ∈ T -> A ⊏ T -> (a :: A) ⊏ T.
    Proof. intros ? ? ? []; subst; intuition. Qed.

    Lemma contains_cons2 a A T :
      (a :: A) ⊏ T -> A ⊏ T.
    Proof. firstorder. Qed.

    Lemma contains_app A B T :
      A ⊏ T -> B ⊏ T -> (A ++ B) ⊏ T.
    Proof. intros ? ? ? [] % in_app_or; intuition. Qed.

    Lemma contains_extend1 phi T :
      phi ∈ (T ⋄ phi).
    Proof. now right. Qed.

    Lemma contains_extend2 phi psi T :
      phi ∈ T -> phi ∈ (T ⋄ psi).
    Proof. intros ?. now left. Qed.

    Lemma contains_extend3 A T phi :
      A ⊏ T -> A ⊏ (T ⋄ phi).
    Proof.
      intros ? ? ?. left. now apply H.
    Qed.
  End ContainsAutomation.
End Theory.

Section TheoryMap.
  Context {Σ_funcs1 Σ_funcs2 : funcs_signature}.
  Context {Σ_preds1 Σ_preds2 : preds_signature}.
  Context {ops1 ops2 : operators}.
  Context {ff1 ff2 : falsity_flag}.

  Definition tmap (f : @form Σ_funcs1 Σ_preds1 ops1 ff1 -> @form Σ_funcs2 Σ_preds2 ops2 ff2) (T : @theory Σ_funcs1 Σ_preds1 ops1 ff1) : @theory Σ_funcs2 Σ_preds2 ops2 ff2 :=
    fun phi => exists psi, T psi /\ f psi = phi.

  Lemma enum_tmap' (f : @form Σ_funcs1 Σ_preds1 ops1 ff1 -> @form Σ_funcs2 Σ_preds2 ops2 ff2) (T : @theory Σ_funcs1 Σ_preds1 ops1 ff1) L :
    cumulative L -> list_enumerator L T -> cumulative (L >> List.map f) /\ list_enumerator (L >> List.map f) (tmap f T).
  Proof.
    intros H H0. split; unfold ">>".
    - intros n. destruct (H n) as [A ->]. exists (List.map f A). apply map_app.
    - intros x; split.
      + intros (phi & [m Hin] % H0 & <-). exists m. apply in_map_iff. firstorder.
      + intros (m & (phi & <- & Hphi) % in_map_iff). firstorder.
  Qed.

  Lemma enum_tmap (f : @form Σ_funcs1 Σ_preds1 ops1 ff1 -> @form Σ_funcs2 Σ_preds2 ops2 ff2) (T : @theory Σ_funcs1 Σ_preds1 ops1 ff1) :
    enumerable T -> enumerable (tmap f T).
  Proof.
    intros (L & HL).
    exists (fun n => match (L n) with Some k => Some (f k) | None => None end).
    split.
    - intros (y & Hy & <-). destruct (HL y) as [HL1 HL2].
      destruct (HL1 Hy) as [n Hn]. exists n. rewrite Hn. easy.
    - intros (n & Hn). destruct (L n) as [f0|] eqn:Heq; try congruence.
      exists f0. split; try congruence. destruct (HL f0) as [HL1 HL2].
      apply HL2. exists n. easy.
  Qed.

  Lemma tmap_contains_L (f : @form Σ_funcs1 Σ_preds1 ops1 ff1 -> @form Σ_funcs2 Σ_preds2 ops2 ff2) T A :
    contains_L A (tmap f T) -> exists B, A = List.map f B /\ contains_L B T.
  Proof.
    induction A.
    - intros. now exists List.nil.
    - intros H. destruct IHA as (B & -> & HB). 1: firstorder.
      destruct (H a (or_introl eq_refl)) as (b & Hb & <-).
      exists (b :: B). split. 1: auto. intros ? []; subst; auto.
  Qed.

  Lemma tmap_closed (f : @form Σ_funcs1 Σ_preds1 ops1 ff1 -> @form Σ_funcs2 Σ_preds2 ops2 ff2) T : 
    (forall x, closed x -> closed (f x)) ->
    closed_T T -> closed_T (tmap f T).
  Proof.
    intros Hf Hclosed ? (y & Hy & <-).
    apply Hf, Hclosed, Hy.
  Qed.

End TheoryMap.
#[global] Hint Constructors Vector_In2 : contains_theory.

Infix "⊏" := contains_L (at level 20) : theory.
Infix "⊑" := subset_T (at level 20) : theory.
Infix "∈" := contains (at level 70) : theory.
Infix "⋄" := extend (at level 20) : theory.

#[global] Hint Resolve contains_nil contains_cons contains_cons2 contains_app : contains_theory.
#[global] Hint Resolve contains_extend1 contains_extend2 contains_extend3 : contains_theory.
#[global] Ltac use_theory A := exists A; split; [eauto 15 with contains_theory|].
