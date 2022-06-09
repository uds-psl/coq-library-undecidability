Require Import List Lia Morphisms.
From Undecidability.HOU Require Import std.std calculus.calculus unification.higher_order_unification unification.systemunification.
Import ListNotations.

(* * Nth-Order Unification *)
Section NthOrderUnificationDefinition.

  Context {n: nat} {X: Const}.

  Class orduni  :=
    {
      Gamma₀  : ctx;
      s₀  : exp X;
      t₀  : exp X;
      A₀  : type;
      H1₀ : Gamma₀ ⊢(n) s₀ : A₀;
      H2₀ : Gamma₀ ⊢(n) t₀ : A₀
    }.


  Definition OU (I: orduni) :=
    exists (Delta: ctx) (sigma: fin -> exp X), Delta ⊩(n) sigma : Gamma₀ /\ sigma • s₀ ≡ sigma • t₀.

End NthOrderUnificationDefinition.
Arguments orduni _ : clear implicits.
Arguments OU _ : clear implicits.
#[export] Hint Resolve H1₀ H2₀ : core.




(* ** Nth-Order System Unification *)
Section NthOrderSystemUnification.

  Variable (X: Const).

  Implicit Types (sigma: fin -> exp X) (e: eq X) (E : eqs X).

  Definition eq_ordertyping n Gamma e A := Gamma ⊢(n) fst e : A /\ Gamma ⊢(n) snd e : A.

  Notation "Gamma ⊢₂( n ')' e : A" := (eq_ordertyping n Gamma e A) (at level 80, e at level 99).


  Reserved Notation  "Gamma ⊢₊₊( n ) E : L" (at level 80, E at level 99).

  Inductive eqs_ordertyping Gamma n : eqs X -> list type -> Prop :=
  | eqs_ordertyping_nil: Gamma ⊢₊₊(n) nil : nil
  | eqs_ordertyping_cons s t  A E L: Gamma ⊢(n) s : A -> Gamma ⊢(n) t : A -> Gamma ⊢₊₊(n) E : L -> Gamma ⊢₊₊(n) ((s,t) :: E) : A :: L
  where  "Gamma ⊢₊₊( n ) E : L" := (eqs_ordertyping Gamma n E L).

  Hint Constructors eqs_ordertyping : core.


  Lemma eqs_ordertyping_step Gamma n E L: Gamma ⊢₊₊(n) E : L -> Gamma ⊢₊₊(S n) E : L.
  Proof. induction 1; eauto. Qed.

  Lemma eqs_ordertyping_monotone Gamma n m E L: n <= m -> Gamma ⊢₊₊(n) E : L -> Gamma ⊢₊₊(m) E : L.
  Proof. induction 1; eauto using eqs_ordertyping_step. Qed.

  Lemma eqs_ordertyping_soundness Gamma n E L: Gamma ⊢₊₊(n) E : L -> Gamma ⊢₊₊ E : L.
  Proof. induction 1; eauto using eqs_typing. Qed.


  Lemma left_ordertyping Gamma n E L: Gamma ⊢₊₊(n) E : L -> Gamma ⊢₊(n) left_side E : L.
  Proof. induction 1; cbn; eauto. Qed.
  Lemma right_ordertyping Gamma n E L: Gamma ⊢₊₊(n) E : L -> Gamma ⊢₊(n) right_side E : L.
  Proof. induction 1; cbn; eauto. Qed.

  Lemma ordertyping_combine Gamma n E L:
    Gamma ⊢₊(n) left_side E : L -> Gamma ⊢₊(n) right_side E : L -> Gamma ⊢₊₊(n) E : L.
  Proof.
    intros H1 H2; induction E in L, H1, H2 |-*; inv H1; inv H2; eauto.
    destruct a; eauto.
  Qed.


  Hint Resolve left_typing right_typing left_ordertyping right_ordertyping : core.
  Hint Rewrite Vars'_cons Vars'_app : simplify.
  Hint Rewrite left_subst_eqs right_subst_eqs : simplify.



  Lemma eqs_ordertyping_preservation_subst n Gamma E L Delta sigma:
    Gamma ⊢₊₊(n) E : L -> Delta ⊩(n) sigma : Gamma -> Delta ⊢₊₊(n) sigma •₊₊ E : L.
  Proof. induction 1; cbn; eauto. Qed.

  Class ordsysuni (n: nat) :=
  {
    Gamma₀'  : ctx;
    E₀'  : eqs X;
    L₀'  : list type;
    H₀' : Gamma₀' ⊢₊₊(n) E₀' : L₀';
  }.

  Definition SOU n (I: ordsysuni n) := exists (Delta: ctx) (sigma: fin -> exp X),
      Delta ⊩(n) sigma : Gamma₀' /\ forall s t, (s, t) ∈ E₀' -> sigma • s ≡ sigma • t.

  Arguments SOU: clear implicits.

  Hint Resolve H₀' : core.


  Lemma linearize_terms_ordertyping n Gamma (S: list (exp X)) L A:
    ord' L < n -> ord A <= n ->
    Gamma ⊢₊(n) S : L -> Gamma ⊢(n) linearize_terms S : (Arr (rev L) A) → A.
  Proof.
    intros H; econstructor; eapply AppR_ordertyping with (L := L).
    eapply orderlisttyping_preservation_under_renaming; eauto.
    intros x ?; cbn; eauto.
    econstructor; eauto; simplify; cbn; intuition.
  Qed.


  Hint Resolve linearize_terms_ordertyping : core.
    Global Instance orduni_ordsysuni n (I: orduni n X): ordsysuni n.
    Proof.
      refine {| Gamma₀' := Gamma₀; E₀' := [(s₀, t₀)]; L₀' := [A₀]; H₀' := _; |}.
      abstract (eauto).
    Defined.

    Global Instance ordsysuni_orduni {n} (I: ordsysuni n): ord' L₀' < n -> orduni n X.
    Proof. 
      intro H.
      refine {|
         Gamma₀ := Gamma₀';
         s₀ := linearize_terms (left_side E₀');
         t₀ := linearize_terms (right_side E₀');
         A₀ := (Arr (rev L₀') alpha) → alpha;
         H1₀ := _;
         H2₀ := _;
       |}.
      - abstract (assert (1 <= n) by (destruct n; lia); eauto).
      - abstract (assert (1 <= n) by (destruct n; lia); eauto).
    Defined.
    
   Lemma OU_SOU n: OU n X ⪯ SOU n.
   Proof.
     exists (orduni_ordsysuni n); intros I.
     split; intros (Delta & sigma & H1 & H2); exists Delta; exists sigma; intuition.
     firstorder; injection H; intros; subst; eauto.
     firstorder.
   Qed.

  Lemma SOU_OU n (I: ordsysuni n) (H: ord' L₀' < n):
    SOU n I <-> OU n X (ordsysuni_orduni I H).
  Proof.
    split; intros (Delta & sigma & H1 & H2); exists Delta; exists sigma; intuition;
      cbn [s₀ t₀ ordsysuni_orduni] in *.
    rewrite !linearize_terms_subst, linearize_terms_equiv. now apply equiv_pointwise_eqs.
     eapply equiv_eqs_pointwise; eauto.
     now rewrite <-linearize_terms_equiv, <-!linearize_terms_subst.
  Qed.


End NthOrderSystemUnification.

Arguments SOU : clear implicits.
Arguments ordsysuni : clear implicits.
Arguments Gamma₀' {_} {_} {_}.
Arguments E₀' {_} {_} {_}.
Arguments L₀' {_} {_} {_}.


Notation  "Gamma ⊢₊₊( n ) E : L" := (eqs_ordertyping _ Gamma n E L)(at level 80, E at level 99).
Notation "Gamma ⊢₂( n ')' e : A" := (eq_ordertyping _ n Gamma e A) (at level 80, e at level 99).

#[export] Hint Resolve eqs_ordertyping_soundness : core.



(* ** Nth-Order Normalisation *)
Definition NOU {X: Const} n (I: orduni n X) :=
  exists Delta sigma, Delta ⊩(n) sigma : Gamma₀ /\ sigma • s₀ ≡ sigma • t₀ /\ forall x, normal (sigma x).

Definition NSOU {X: Const} n (I: ordsysuni X n) := exists Delta sigma,
    Delta ⊩(n) sigma : Gamma₀' /\ (forall s t, (s, t) ∈ E₀' -> sigma • s ≡ sigma • t) /\ forall x, normal (sigma x).




Section SubstitutionTransformations.

  Variable (X: Const) (n: nat) (s t: exp X) (A: type) (Gamma: ctx).
  Hypothesis (Leq: 1 <= n).
  Hypothesis (T1:  Gamma ⊢(n) s : A) (T2: Gamma ⊢(n) t : A).
  Implicit Types (Delta: ctx) (sigma : fin -> exp X).


  Lemma ordertyping_normalise_subst sigma Delta :
    Delta ⊩(n) sigma : Gamma -> {tau  | (forall x : fin, sigma x >* tau x) /\
                         (forall x : nat, x ∈ dom Gamma -> normal (tau x)) /\
                         Delta ⊩(n) tau : Gamma}.
  Proof.
    intros H; eapply ordertypingSubst_soundness in H as H';
      eapply normalise_subst in H' as [tau].
    exists tau; intuition. intros ???.
    eapply ordertyping_preservation_under_steps; [eapply H0 |].
    eapply H; eauto.
  Qed.

End SubstitutionTransformations.

Section Normalisation.

  Variable (X: Const).
  Arguments s₀ {_} {_} _.
  Arguments t₀ {_} {_} _.
  Arguments Gamma₀ {_} {_} _.
  Arguments A₀ {_} {_} _.
  Arguments sᵤ {_} _.
  Arguments tᵤ {_} _.
  Arguments Gammaᵤ {_} _.
  Arguments Aᵤ {_} _.



  Lemma U_NU I: U X I <-> NU I.
  Proof.
    split; intros (Delta & sigma & H1 & H2); [| exists Delta; exists sigma; intuition].
    eapply normalise_subst in H1 as (tau & H5 & H6 & H7).
    pose (theta x := if nth (Gammaᵤ I) x then tau x else var x).
    exists Delta. exists theta. intuition.
    + intros ???; unfold theta; rewrite H; eapply H7; eauto.
    + rewrite subst_pointwise_equiv with (sigma := theta) (tau := sigma).
      rewrite subst_pointwise_equiv with (sigma := theta) (tau := sigma); eauto.
      all: intros ? H; eapply typing_variables in H; eauto; domin H.
      all: unfold theta; now rewrite H, H5.
    + unfold theta; destruct nth eqn: ?; [|eauto].
      domin Heqo; eauto.
  Qed.



  Lemma OU_NOU n I: 1 <= n -> OU n X I <-> NOU n I.
  Proof.
    intros Leq; split; intros (Delta & sigma & H1 & H2); [| exists Delta; exists sigma; intuition].
    eapply ordertyping_normalise_subst in H1 as (tau & H5 & H6 & H7).
    pose (theta x := if nth (Gamma₀ I) x then tau x else var x).
    exists Delta. exists theta. intuition.
    + intros ???; unfold theta; rewrite H; eapply H7; eauto.
    + rewrite subst_pointwise_equiv with (sigma := theta) (tau := sigma).
      rewrite subst_pointwise_equiv with (sigma := theta) (tau := sigma); eauto.
      all: intros ? H; eapply typing_variables in H; eauto; domin H.
      all: unfold theta; now rewrite H, H5.
    + unfold theta; destruct nth eqn: ?; [|eauto]; domin Heqo; eauto.
  Qed.


  Lemma SOU_NSOU n I: 1 <= n -> SOU X n I <-> NSOU n I.
  Proof.
    intros Leq; split; intros (Delta & sigma & H1 & H2); [| exists Delta; exists sigma; intuition].
    eapply ordertyping_normalise_subst in H1 as (tau & H5 & H6 & H7).
    pose (theta x := if nth (@Gamma₀' _ _ I) x then tau x else var x).
    exists Delta. exists theta. intuition.
    + intros ???; unfold theta; rewrite H; eapply H7; eauto.
    + intros; eauto.
      rewrite subst_pointwise_equiv with (sigma := theta) (tau := sigma).
      rewrite subst_pointwise_equiv with (sigma := theta) (tau := sigma); eauto.
      all: intros ? ?; enough (x ∈ dom Gamma₀') as D;
        [domin D; unfold theta; rewrite D; eauto|].
      all: eapply Vars_listtyping.
      2, 4: eapply in_flat_map; eexists; (intuition eauto).
      2: change t with (snd (s, t)); eapply in_map; eauto.
      2: change s with (fst (s, t)); eapply in_map; eauto.
      eapply right_typing, eqs_ordertyping_soundness, @H₀'.
      eapply left_typing, eqs_ordertyping_soundness, @H₀'.
    + unfold theta; destruct nth eqn: ?; [|eauto].
      domin Heqo; eauto.
  Qed.


  Lemma OU_reduction n (I I': orduni n X):
    s₀ I ≡ s₀ I' -> t₀ I ≡ t₀ I' ->
    Gamma₀ I = Gamma₀ I' -> A₀ I = A₀ I' ->
    OU n X I -> OU n X I'.
  Proof.
    intros H1 H2 H3 H4; intros (Delta & sigma & T & N); exists Delta; exists sigma; split.
    rewrite <-H3; eauto. now rewrite <-H1, <-H2, N.
  Qed.


  Program Instance orduni_normalise n (I: orduni n X) : orduni n X :=
    { Gamma₀ := Gamma₀ I; s₀ := eta₀ (s₀ I) H1₀; t₀ := eta₀ (t₀ I) H2₀; A₀ := A₀ I }.
  Next Obligation.
    eapply ordertyping_preservation_under_steps. rewrite <-eta₀_correct. all: eauto.
  Qed.
  Next Obligation.
    eapply ordertyping_preservation_under_steps. rewrite <-eta₀_correct. all: eauto.
  Qed.


  Lemma orduni_normalise_correct n I:
    OU n X I <-> OU n X (orduni_normalise n I).
  Proof.
    split; intros H; [eapply @OU_reduction|eapply @OU_reduction with (I := orduni_normalise n I)].
    all: eauto; cbn; eapply equiv_join.
    1, 3, 6, 8: rewrite eta₀_correct. all: reflexivity.
  Qed.

End Normalisation.
