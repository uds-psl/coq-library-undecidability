Require Import List Lia.
Import ListNotations.

From Undecidability.HOU.calculus Require Import 
  prelim terms syntax semantics equivalence typing order evaluator. 

(* * Higher-Order Unification *)
Section UnificationDefinitions.

  Context {X: Const}.

  Class uni :=
    {
      Gammaᵤ  : ctx;
      sᵤ  : exp X;
      tᵤ  : exp X;
      Aᵤ  : type;
      H1ᵤ : Gammaᵤ ⊢ sᵤ : Aᵤ;
      H2ᵤ : Gammaᵤ ⊢ tᵤ : Aᵤ
    }.


  Definition U (I: uni) :=
    exists (Delta: ctx) (sigma: fin -> exp X), Delta ⊩ sigma : Gammaᵤ /\ sigma • sᵤ ≡ sigma • tᵤ.

End UnificationDefinitions.

Arguments uni _ : clear implicits.
Arguments U _ : clear implicits.
#[export] Hint Resolve H1ᵤ H2ᵤ : core.

(* ** Normalisation *)


Definition NU {X: Const} (I: uni X) :=
  exists Delta sigma, Delta ⊩ sigma : Gammaᵤ /\ sigma • sᵤ ≡ sigma • tᵤ /\ forall x, normal (sigma x).

Section Normalisation.

  Section SubstitutionTransformations.
    
    Variable (X: Const) (n: nat) (s t: exp X) (A: type) (Gamma: ctx).
    Hypothesis (Leq: 1 <= n).
    Hypothesis (T1:  Gamma ⊢(n) s : A) (T2: Gamma ⊢(n) t : A).
    Implicit Types (Delta: ctx) (sigma : fin -> exp X).
    
    
    Lemma normalise_subst Delta sigma:
      Delta ⊩ sigma : Gamma ->
                { tau | (forall x, sigma x >* tau x) /\
                      (forall x, x ∈ dom Gamma -> normal (tau x)) /\ Delta ⊩ tau : Gamma}.
    Proof.
      intros T.
      assert (forall x, x ∈ dom Gamma -> { A | nth Gamma x = Some A }) as I.
      { intros x H1. destruct nth eqn: ?; eauto.
        exfalso. domin H1. congruence.  }
      exists (fun x => match x el dom Gamma with
              | left H => eta (sigma x) (T _ _ (proj2_sig (I x H)))
              | right _ => sigma x
              end).
      split; [| split].
      1-2: intros x; destruct dec_in; intuition.
      eapply eta_correct. eapply eta_normal. 
      intros x B H. destruct dec_in; intuition.
      destruct I; cbn. generalize (T x x0 e).
      rewrite H in e; injection e as ->.
      eapply eta_typing.
    Qed.
    
  End SubstitutionTransformations.
  Variable (X: Const).
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

  Lemma U_reduction (I I': uni X):
    sᵤ I ≡ sᵤ I' -> tᵤ I ≡ tᵤ I' ->
    Gammaᵤ I = Gammaᵤ I' -> Aᵤ I = Aᵤ I' ->
    U X I -> U X I'.
  Proof.
    intros H1 H2 H3 H4; intros (Delta & sigma & T & N); exists Delta; exists sigma; split.
    rewrite <-H3; eauto. now rewrite <-H1, <-H2, N. 
  Qed.

  
  Program Instance uni_normalise (I: uni X) : uni X :=
    { Gammaᵤ := Gammaᵤ I; sᵤ := eta (sᵤ I) H1ᵤ; tᵤ := eta (tᵤ I) H2ᵤ; Aᵤ := Aᵤ I }.
  Next Obligation.
    eapply preservation_under_steps. rewrite <-eta_correct. all: eauto.
  Qed.
  Next Obligation.
    eapply preservation_under_steps. rewrite <-eta_correct. all: eauto.
  Qed.


  Lemma uni_normalise_correct I:
    U X I <-> U X (uni_normalise I).
  Proof.
    split; intros H; [eapply @U_reduction|eapply @U_reduction with (I := uni_normalise I)].
    all: eauto; cbn; eapply equiv_join.
    1, 3, 6, 8: rewrite eta_correct. all: reflexivity. 
  Qed.


End Normalisation.
