Set Implicit Arguments.
Require Import Morphisms Omega Lia.
From Undecidability.HOU Require Import std.std.
From Undecidability.HOU.calculus Require Import 
  prelim terms syntax semantics confluence typing order. 

Set Default Proof Using "Type".

(* * Weak Normalisation *)


Section SemanticTyping.


  Variable (X: Const).


  Definition SemType := exp X -> Prop.

  (* ** Logical Relations *)
  Definition active (s: exp X) :=
    match s with lambda s => True | _ => False end.

  Definition C (T: SemType) (s: exp X) :=
    exists t, s ▷ t /\ (active t -> T t).
  

  Fixpoint V (A: type) (s: exp X) :=
    match A with
    | typevar beta => False
    | A → B => match s with
              | lambda s => normal s /\
                      forall t delta, C (V A) t -> C (V B) ((ren delta (lambda s)) t)
              | _ => False
              end
    end.


  Definition E A := C (V A).
  Definition G Gamma gamma := forall i A, nth Gamma i = Some A -> E A (gamma i).



  Lemma E_evaluates s A:
    E A s -> exists t, s ▷ t.
  Proof. intros (t & H1 & H2); exists t; intuition. Qed.



  Lemma closure_under_expansion s t A:
    s >* t -> E A s -> E A t.
  Proof.
    intros H [v [[H1 H2] H3]]. exists v. intuition. split; eauto.
    eapply confluence_normal_left; eauto.
  Qed.


  Lemma closure_under_reduction s t A:
    s >* t -> E A t -> E A s.
  Proof.
    intros H [v [[H1 H2] H3]]. exists v; intuition. split; eauto.
  Qed.




  Definition ren_closed (S: SemType) :=
    forall delta s, S s -> S (ren delta s).


  Lemma ren_closed_C S: ren_closed S -> ren_closed (C S).
  Proof.
    intros H delta s; unfold C in *; intros (t & [H1 H2] & H3).
    exists (ren delta t); split.
    split; eauto using ren_steps, normal_ren.
    intros H4. eapply H, H3. destruct t; cbn in *; intuition. 
  Qed.


  Lemma ren_closed_V A: ren_closed (V A).
  Proof.
    induction A as [beta | A IHA B IHB].
    - intros ? ? []. 
    - intros delta []; cbn in *; eauto; intros [H1 H2].
      split; eauto using normal_ren. 
      intros t delta' H'. asimpl. 
      replace (_ • e) with (ren (upRen_exp_exp (delta >> delta')) e)by now asimpl.
      now eapply H2.
  Qed.

  Lemma ren_closed_E A: ren_closed (E A).
  Proof.
    eapply ren_closed_C, ren_closed_V.
  Qed.

  Lemma ren_closed_G Gamma gamma delta: G Gamma gamma -> G Gamma (gamma >> ren delta).
  Proof.
    intros H x A E. eapply ren_closed_E, H, E.
  Qed.    




  Lemma E_var x A: E A (var x).
  Proof.
    exists (var x). unfold evaluates; cbn; intuition.
  Qed.

  Lemma G_id Gamma: G Gamma var.
  Proof.
    intros ???. eapply E_var. 
  Qed.

  Lemma G_cons Gamma A s gamma:
    G Gamma gamma -> E A s -> G (A :: Gamma) (s .: gamma).
  Proof.
    intros. intros [|] B H'; cbn in *.
    now injection H' as ->. now eapply H.
  Qed.

  Lemma G_up Gamma A gamma:
    G Gamma gamma -> G (A :: Gamma) (up gamma).
  Proof.
    eauto using G_cons, ren_closed_G, E_var.
  Qed.


  Lemma compat_var Gamma i A gamma:
    nth Gamma i = Some A -> G Gamma gamma -> E A (gamma i).
  Proof. intuition. Qed.

  Lemma compat_const c:
    E (ctype X c) (const c).
  Proof.
    exists (const c); split; [split|]; cbn; intuition.
  Qed.


  Lemma compat_lambda A B s:
    E B s -> (forall t delta, E A t -> E B (ren delta (lambda s) t)) ->  E (A → B) (lambda s).
  Proof.
    intros [t [[H1 H2] _]] ?; cbn; exists (lambda t); intuition; split; rewrite ?H1; eauto.
    intros; eapply closure_under_expansion; [|eauto]; now rewrite H1.
  Qed.


  Lemma compat_app A B s t:
    E (A → B) s -> E A t -> E B (s t).
  Proof.
    intros (v1 & [H1 H2] & H3). intros (v2 & [H4 H5] & H6).
    eapply closure_under_reduction. rewrite H1, H4; eauto. 
    destruct v1.
    1, 2, 4: eexists; split; [split|]; eauto; cbn; intuition.
    cbn in H3; mp H3; cbn; intuition.
    specialize (H0 v2 id); asimpl in H0; unfold id in H0.
    eapply H0; exists v2; split; [split|]; eauto. 
  Qed.

End SemanticTyping.

(* ** Semantic Soundness *)
Section Soundness.

  Context {X: Const}.

  Implicit Type (s: exp X).

  Definition semtyping Gamma s A := forall gamma, G Gamma gamma -> E A (gamma • s).

  Notation "Gamma ⊨ s : A" := (semtyping Gamma s A) (at level 80, s at level 99).

  Lemma semantic_soundness Gamma s A:
    Gamma ⊢ s : A -> Gamma ⊨ s : A.
  Proof.
    induction 1.
    - intros ??; cbn; eapply compat_var; eauto. 
    - intros ??; cbn; eapply compat_const.
    - intros ??; cbn; eapply compat_lambda; eauto using G_up.  
      intros; eapply closure_under_reduction. cbn; dostep; now asimpl.  
      eapply IHtyping, G_cons; eauto. 
      replace (gamma >> _) with (gamma >> ren delta) by now asimpl.
      eapply ren_closed_G; eauto. 
    - intros ??; cbn; eapply compat_app; eauto.
  Qed.

  (* ** Termination *)
  Lemma termination_steps Gamma s A:
    Gamma ⊢ s : A -> exists t, s ▷ t.
  Proof.
    intros H % semantic_soundness.
    specialize (H var (@G_id X Gamma)).
    asimpl in H; unfold id in H. 
    eapply E_evaluates, H.
  Qed.

  Lemma ordertyping_termination_steps Gamma n s A:
    Gamma ⊢(n) s : A -> exists t, s ▷ t.
  Proof.
    now intros ? % ordertyping_soundness % termination_steps.
  Qed.

End Soundness.
