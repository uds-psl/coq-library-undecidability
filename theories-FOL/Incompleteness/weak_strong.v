From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.

From FOL Require Import FullSyntax Arithmetics.
From FOL.Proofmode Require Import Theories ProofMode.
From FOL.Incompleteness Require Import fol_utils qdec sigma1.


Require Import String List.
Open Scope string_scope.

From Equations Require Import Equations.
Require Import Lia.


Section value_disjoint.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.
  Context `{pei : peirce}.

  Existing Instance interp_nat.

  Variable P1 P2 : nat -> Prop.
  Hypothesis P_disjoint : forall x, P1 x -> P2 x -> False.

  Section value_disjoint'.
    Variable φ1 φ2 : form.
    Hypothesis (φ1_bounded : bounded 2 φ1) (φ2_bounded : bounded 2 φ2).
    Hypothesis (φ1_qdec : Qdec φ1) (φ2_qdec : Qdec φ2).
    (* varphi1 and varphi2 are weakly representable using with single
        * existential quantifier  over a decidable core *)
    Hypothesis (φ1_syn : forall x, P1 x <-> Qeq ⊢ ∃ φ1[(num x) ..])
               (φ2_syn : forall x, P2 x <-> Qeq ⊢ ∃ φ2[(num x) ..]).

    (* Transating representability assumptions to a semantic level *)
    Local Lemma φ1_sem x ρ : P1 x <-> ρ ⊨ ∃ φ1[(num x) ..].
    Proof.
      rewrite φ1_syn.
      split.
      - intros H. apply Σ1_soundness with (p := ρ) in H.
        + assumption.
        + constructor. apply Σ1_subst. now constructor.
        + constructor. eapply subst_bounded_max; last eassumption.
          intros [|[|k]] Hk; apply num_bound + solve_bounds.
      - intros H. apply Σ1_completeness.
        + do 2 constructor. now apply Qdec_subst.
        + solve_bounds. eapply subst_bounded_max; last eassumption.
          intros [|[|n]] Hn; cbn. 2-3: solve_bounds.
          apply num_bound.
        + intros ρ'. eapply sat_closed; last eassumption.
          constructor. eapply subst_bounded_max; last eassumption.
          intros [|[|k]] Hk; apply num_bound + solve_bounds.
    Qed.

    Local Lemma φ2_sem x ρ : P2 x <-> ρ ⊨ ∃ φ2[(num x) ..].
    Proof.
      rewrite φ2_syn.
      split.
      - intros H. eapply Σ1_soundness in H.  
        + eassumption.
        + constructor. apply Σ1_subst. now constructor.
        + constructor. eapply subst_bounded_max; last eassumption.
          intros [|[|k]] Hk; apply num_bound + solve_bounds.
      - intros H. apply Σ1_completeness.
        + do 2 constructor. now apply Qdec_subst.
        + solve_bounds. eapply subst_bounded_max; last eassumption.
          intros [|[|n]] Hk; cbn. 2-3: solve_bounds.
          apply num_bound.
        + intros ρ'. eapply sat_closed; last eassumption.
          constructor. eapply subst_bounded_max; last eassumption.
          intros [|[|k]] Hk; apply num_bound + solve_bounds.
    Qed.
          
    (* Definition of formulas strongly separating *)
    Definition φ1' := φ1 ∧ ∀ $0 ⧀= $2 → φ2[$1 .: $0 ..] → ⊥.
    Definition φ2' := φ2 ∧ ∀ $0 ⧀= $2 → φ1[$1 .: $0 ..] → ⊥.

    (* Properties of these formulas *)
    Lemma φ1'_bounded : bounded 2 φ1'.
    Proof.
      repeat solve_bounds.
      - assumption.
      - eapply subst_bounded_max; last eassumption.
        intros [|[|n]] H; cbn; solve_bounds.
    Qed.

    Lemma φ2'_bounded : bounded 2 φ2'.
    Proof.
      repeat solve_bounds.
      - assumption.
      - eapply subst_bounded_max; last eassumption.
        intros [|[|n]] H; cbn; solve_bounds.
    Qed.

    Lemma φ1'_qdec : Qdec φ1'.
    Proof.
      apply Qdec_and; first assumption.
      apply (@Qdec_bounded_forall $1).
      apply Qdec_impl.
      - apply Qdec_subst, φ2_qdec.
      - apply Qdec_bot.
    Qed.

    Lemma φ2'_qdec : Qdec φ2'.
    Proof.
      apply Qdec_and; first assumption.
      apply (@Qdec_bounded_forall $1).
      apply Qdec_impl.
      - apply Qdec_subst, φ1_qdec.
      - apply Qdec_bot.
    Qed.

    (* Strong separation *)
    Local Lemma DR1 x : P1 x -> Qeq ⊢ ∃ φ1'[(num x)..].
    Proof.
      intros HP1. eapply Σ1_completeness.
      { constructor. apply Σ1_subst. constructor. apply φ1'_qdec. }
      { constructor. eapply subst_bounded_max; last apply φ1'_bounded.
        intros [|[|n]] H; try solve_bounds. apply num_bound. }
      intros ρ.
      pose proof HP1 as H. erewrite (φ1_sem _ _) in H.
      destruct H as [k Hk]. exists k.
      split; first eassumption.
      cbn. intros k' _ Hk'. apply (@P_disjoint x).
      - eapply φ1_sem. exists k. apply Hk.
      - eapply φ2_sem with (ρ := k .: ρ). exists k'.
        rewrite subst_comp in Hk'.
        erewrite bounded_subst. 1-2: eassumption.
        intros [|[|n]] H; cbn.
        + now rewrite num_subst.
        + easy.
        + lia.
    Qed.

    Local Lemma DR1' x : P2 x -> Qeq ⊢ ∃ φ2'[(num x)..].
    Proof. 
      intros HP1. eapply Σ1_completeness.
      { constructor. apply Σ1_subst. constructor. apply φ2'_qdec. }
      { constructor. eapply subst_bounded_max; last apply φ2'_bounded.
        intros [|[|n]] H; try solve_bounds. apply num_bound. }
      intros ρ.
      pose proof HP1 as H. erewrite (φ2_sem _ _) in H.
      destruct H as [k Hk]. exists k.
      split; first eassumption.
      cbn. intros k' _ Hk'. apply (@P_disjoint x).
      - eapply φ1_sem with (ρ := k .: ρ). exists k'.
        rewrite subst_comp in Hk'.
        erewrite bounded_subst. 1-2: eassumption.
        intros [|[|n]] H; cbn.
        + now rewrite num_subst.
        + easy.
        + lia.
      - eapply φ2_sem. exists k. apply Hk.
    Qed.

    Local Lemma DR2 x : P2 x -> Qeq ⊢ ¬∃ φ1'[(num x)..].
    Proof. 
      cbn. intros HP2. 
      assert (exists k, Qeq ⊢ φ2'[(num x)..][(num k)..]) as [k Hk].
      { apply Σ1_witness.
        - constructor. apply Qdec_subst. apply φ2'_qdec.
        - eapply subst_bounded_max; last apply φ2'_bounded.
          intros [|[|n]] H; try solve_bounds. apply num_bound.
        - apply Σ1_completeness.
          + constructor. apply Σ1_subst. constructor. apply φ2'_qdec.
          + constructor. eapply subst_bounded_max; last apply φ2'_bounded.
            intros [|[|n]] H; try solve_bounds. apply num_bound.
          + apply Σ1_soundness.
            * do 2 constructor. apply Qdec_subst. eapply φ2'_qdec.
            * constructor. 
              eapply subst_bounded_max; last eapply φ2'_bounded. 
              intros [|[|n]] H; apply num_bound + solve_bounds.
            * apply DR1', HP2. }
      cbn in Hk. 

      custom_simpl. unfold "↑". fstart.
      fintros "H". fdestruct "H". fdestruct "H".

      pose proof (Qsdec_le x0 (num_bound k 0)). 
      fdestruct H.
      - fapply ("H0" (num k)).
        + ctx.
        + asimpl. fassert (φ2[(num x)..][(num k)..]).
          { fstop. eapply CE1, Weak; eauto; now do 3 right. }
          rewrite !subst_comp. erewrite bounded_subst.
          * fapply "H2".
          * eassumption.
          * intros [|[|[|l]]]; cbn; (now rewrite ?num_subst + lia).
      - rewrite num_subst in Hk.
        fassert (∀ $0 ⧀= num k → ¬ φ1[$1 .: $0..][up (num x)..][up (num k)..]).
        { fstop. eapply CE2, Weak; eauto; now do 3 right. }
        fapply ("H2" x0).
        + rewrite num_subst. fapply "H1".
        + rewrite !subst_comp. pattern (φ1[(num x).. >> subst_term x0..]). erewrite bounded_subst.
          * fapply "H".
          * eassumption.
          * intros [|[|[|l]]]; cbn; (now rewrite ?num_subst + lia).
    Qed.

    Lemma weak_strong' : exists φ, Σ1 φ /\ bounded 1 φ /\
      (forall x, P1 x -> Qeq ⊢ φ[(num x)..]) /\
      (forall x, P2 x -> Qeq ⊢ ¬φ[(num x)..]).
    Proof.
      exists (∃ φ1'[$1 .: $0 ..]). repeat apply conj.
      { do 2 constructor. apply Qdec_subst, φ1'_qdec. }
      { constructor. eapply subst_bounded_max; last apply φ1'_bounded.
        intros [|[|n]]; intros H; solve_bounds. }
      - intros x H%DR1. 
        replace ((_)[_]) with (∃ φ1'[(num x)..]); first assumption.
        change (∃ _)[_] with (∃ φ1'[$1 .: $0 ..][up (num x)..]).
        f_equal. rewrite subst_comp. eapply bounded_subst; first apply φ1'_bounded.
        intros [|[|n]] Hn; cbn. 2-3:now asimpl.
        now rewrite num_subst.
      - intros x H%DR2.
        replace ((_)[_]) with (∃ φ1'[(num x)..]); first assumption.
        change (∃ _)[_] with (∃ φ1'[$1 .: $0 ..][up (num x)..]).
        f_equal. rewrite subst_comp. eapply bounded_subst; first apply φ1'_bounded.
        intros [|[|n]] Hn; cbn. 2-3: now asimpl.
        now rewrite num_subst.
    Qed.

  End value_disjoint'.

  Section weak_strong.
    Variable φ1 φ2 : form.
    Hypothesis (φ1_bounded : bounded 1 φ1) (φ2_bounded : bounded 1 φ2).
    Hypothesis (φ1_Σ : Σ1 φ1) (φ2_qdec : Σ1 φ2).
    (* P1 and P2 are weakly Sigma1-representable *)
    Hypothesis (φ1_syn : forall x, P1 x <-> Qeq ⊢ φ1[(num x) ..])
               (φ2_syn : forall x, P2 x <-> Qeq ⊢ φ2[(num x) ..]).

    Lemma iff_iff φ ψ : (Qeq ⊢ φ ↔ ψ) -> Qeq ⊢ φ <-> Qeq ⊢ ψ.
    Proof.
      intros H. split; intros H'; fapply H; exact H'.
    Qed.

    (* Combine above results with compression to yield strong separability from weak representability *)
    Theorem weak_strong : exists φ, Σ1 φ /\ bounded 1 φ /\
      (forall x, P1 x -> Qeq ⊢ φ[(num x)..]) /\
      (forall x, P2 x -> Qeq ⊢ ¬φ[(num x)..]).
    Proof.
      destruct (@Σ1_compression φ1 1) as (ψ1 & HQ1 & Hb1 & Hψ1), (@Σ1_compression φ2 1) as (ψ2 & HQ2 & Hb2 & Hψ2).
      all: try assumption.
      apply weak_strong' with (φ1 := ψ1[$1.:$0..]) (φ2 := ψ2[$1.:$0..]).
      { eapply subst_bounded_max; last eassumption. intros [|[|n]] Hn; solve_bounds. }
      { eapply subst_bounded_max; last eassumption. intros [|[|n]] Hn; solve_bounds. }
      { now apply Qdec_subst. }
      { now apply Qdec_subst. }
      - intros x. rewrite φ1_syn. 
        apply iff_iff.
        apply (subst_Weak ((num x)..)) in Hψ1.
        change (map _ _) with Qeq in Hψ1.
        cbn in Hψ1.
        assert (ψ1[$1 .: $0 ..][(num x) ..] = ψ1[up (num x)..]) as ->.
        + rewrite subst_comp. eapply bounded_subst; first eassumption.
          intros [|[|n]] Hn; cbn.
          * reflexivity.
          * now rewrite num_subst.
          * lia.
        + apply prv_intu_peirce, Hψ1.
      - intros x. rewrite φ2_syn. 
        apply iff_iff.
        apply (subst_Weak ((num x)..)) in Hψ2.
        change (map _ _) with Qeq in Hψ2.
        cbn in Hψ2.
        assert (ψ2[$1 .: $0 ..][(num x) ..] = ψ2[up (num x)..]) as ->.
        + rewrite subst_comp. eapply bounded_subst; first eassumption.
          intros [|[|n]] Hn; cbn.
          * reflexivity.
          * now rewrite num_subst.
          * lia.
        + apply prv_intu_peirce, Hψ2.
    Qed.

  End weak_strong.


End value_disjoint.

