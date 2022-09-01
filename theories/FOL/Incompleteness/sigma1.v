(* Order of imports: import proofmode after utils after robinson *)
From Undecidability.FOL Require Import FullSyntax Utils.FriedmanTranslation.
From Undecidability.FOL.Arithmetics Require Import Signature FA Robinson NatModel.

From Undecidability.FOL.Incompleteness Require Import fol_utils qdec.
From Undecidability.FOL.Proofmode Require Import Theories ProofMode.

Require Import Lia.
Require Import String.


Open Scope string_scope.
(** ** Sigma1 completeness *)

Section Sigma1.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  Context {p : peirce}.


  (** # <a id="Sigma1" /> #*)
  Inductive Σ1 : form -> Prop :=
  | Sigma_exists : forall α, Σ1 α -> Σ1 (∃ α)
  | Sigma_Delta : forall α, Qdec α -> Σ1 α.
  Inductive Π1 : form -> Prop :=
  | Pi_forall : forall α, Π1 α -> Π1 (∀ α)
  | Pi_Delta : forall α, Qdec α -> Π1 α.

  Lemma Σ1_subst φ ρ : Σ1 φ -> Σ1 φ[ρ].
  Proof.
    induction 1 as [α H IH | α H] in ρ |-*.
    - cbn. constructor. apply IH.
    - constructor. apply Qdec_subst, H.
  Qed.

  Lemma Π1_subst φ ρ : Π1 φ -> Π1 φ[ρ].
  Proof.
    induction 1 as [α H IH | α H] in ρ |-*.
    - cbn. constructor. apply IH.
    - constructor. apply Qdec_subst, H.
  Qed.

  Lemma exist_times_Σ1 n φ :
    Σ1 φ -> Σ1 (exist_times n φ).
  Proof.
    intros H. induction n.
    - easy.
    - now constructor.
  Qed.


  Lemma exists_compression_2 φ n : Qdec φ -> bounded (S (S n)) φ -> exists ψ, Qdec ψ /\ bounded (S n) ψ /\ Qeq ⊢ (∃∃φ) ↔ (∃ψ).
  Proof.
    intros HQ Hb.
    exists (∃ ($0 ⧀= $1) ∧ ∃ ($0 ⧀=' $2) ∧ φ[up (up (S >> var))]).
    repeat split.
    { apply (@Qdec_bounded_exists $0), (@Qdec_bounded_exists_comm $1).
      apply Qdec_subst, HQ. }
    { repeat solve_bounds.
      eapply subst_bounded_max; last eassumption.
      intros n' H'.
      destruct n' as [|[|n']]; cbn; unfold "↑"; cbn; constructor; lia. }
    fstart. fsplit.
    - fintros "[x [y H]]". fexists (x ⊕ y). 
      fexists x. fsplit.
      { fexists y. fapply ax_refl. }
      fexists y. fsplit.
      { fexists x. fapply ax_refl. }
      asimpl. ctx.
    - fintros "[z [x [Hx [y [Hy H]]]]]".
      fexists x. fexists y. 
      asimpl. ctx.
  Qed.

  Lemma exists_compression φ k n : bounded (n + k) φ -> Qdec φ ->
    exists ψ, Qdec ψ /\ bounded (S k) ψ /\ Qeq ⊢ exist_times n φ ↔ ∃ ψ.
  Proof.
    intros Hb HQ. revert Hb. induction n as [|n IH] in k |-*.
    2: destruct n. all: cbn.
    all: intros Hb.
    - exists φ[↑]. repeat split.
      { now apply Qdec_subst. }
      { eapply subst_bounded_max; last apply Hb. intros n H. constructor. lia. }
      fsplit.
      + fintros. fexists zero. ctx.
      + fintros. fdestruct 0. ctx.
    - exists φ. repeat split.
      + assumption.
      + cbn. replace (k - 0) with k by lia. assumption.
      + fsplit; fintros; ctx.
    - destruct (IH (S k)) as (ψ & HQ' & Hb' & H). 
      { now replace (S n + S k) with (S (S n) + k) by lia. }
      edestruct (@exists_compression_2 ψ) as (ψ' & HΔψ & Hbψ' & Hψ).
      1-2: eassumption.
      exists ψ'. repeat split; try easy. cbn in H.
      fsplit; fstart.
      + fintros "[x H]". 
        fapply Hψ. fexists x. 
        apply subst_Weak  with (xi := x..) in H.
        cbn in H. fapply H. ctx.
      + fintros "H". fapply Hψ in "H".
        fdestruct "H" as "[x H]". fexists x.
        apply subst_Weak  with (xi := x..) in H.
        fapply H. ctx.
  Qed.

  Lemma Σ1_exist_times φ : Σ1 φ -> exists n ψ, Qdec ψ /\ φ = exist_times n ψ.
  Proof.
    induction 1 as [φ H (n & ψ & HΔ & Hψ)|φ H].
    - exists (S n), ψ. now rewrite Hψ.
    - now exists 0, φ.
  Qed.

  Lemma bounded_exist_times φ n k : bounded (n + k) φ <-> bounded k (exist_times n φ).
  Proof.
    induction n in k |-*; split.
    - easy.
    - easy.
    - cbn. intros H. constructor. apply IHn. replace (n + S k) with (S n + k) by lia. apply H.
    - cbn. invert_bounds. replace (S (n + k)) with (n + (S k)) by lia. now apply IHn. 
  Qed.
End Sigma1.

Section Sigma1.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  (* Note that we get the equivalence proof intuitionistically, even though the Sigma 1 proof might be classical *)
  Context {p : peirce}.


  (** # <a id="Sigma1_compression" /> #*)
  Lemma Σ1_compression φ n : bounded n φ -> Σ1 φ -> exists ψ, Qdec ψ /\ bounded (S n) ψ /\ Qeq ⊢I φ ↔ ∃ψ.
  Proof.
    intros Hb (k & ψ & HΔ & ->)%Σ1_exist_times.
    destruct (@exists_compression intu ψ n k) as (ψ' & HΔ' & Hb' & H').
    all: firstorder using bounded_exist_times.
  Qed.
End Sigma1.



Section Sigma1completeness.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Existing Instance intu.

  Lemma Σ1_completeness_intu φ : Σ1 φ -> bounded 0 φ -> interp_nat ⊨= φ -> Qeq ⊢ φ.
  Proof.
    enough (forall ρ, Σ1 φ -> bounded 0 φ[ρ] -> interp_nat ⊨= φ[ρ] -> Qeq ⊢ φ[ρ]).
    { intros HΣ Hb Hsat. rewrite <-subst_var. apply H.
      - easy.
      - now rewrite subst_var.
      - intros ρ'. rewrite subst_var. apply Hsat. }
    intros ρ. induction 1 as [φ H IH|φ H] in ρ |-*.
    - cbn. invert_bounds.
      intros Hnat. destruct (Hnat (fun _ => 0)) as [d Hd].
      fexists (num d). rewrite subst_comp. apply IH.
      + rewrite <-subst_comp. eapply subst_bounded_max; last apply H4.
        intros [|n] Hn; last lia. apply num_bound.
      + intros ρ'. rewrite <-subst_comp.
        rewrite sat_single_nat in Hd.
        eapply sat_closed; last apply Hd.
        eapply subst_bounded_max; last apply H4. 
        intros [|n] Hn; last lia. apply num_bound.
    - intros Hb Hnat.
      assert (Qdec φ[ρ]) as H'.
      { apply Qdec_subst, H. }
      destruct (H' intu (fun _ => zero)) as [H1|H1].
      { intros _. solve_bounds. }
      + rewrite bounded_0_subst in H1; assumption.
      + eapply soundness in H1. cbn in H1. unfold valid_ctx in H1. 
        specialize (H1 _ interp_nat (fun _ => 0) (nat_is_Q_model _)).
        cbn in H1. destruct H1. rewrite bounded_0_subst; auto.
  Qed.

End Sigma1completeness.

Section conservativity.

  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Lemma Σ1_conservativity ϕ :
    Σ1 ϕ -> bounded 0 ϕ -> Qeq ⊢C ϕ -> Qeq ⊢I ϕ.
  Proof. 
    intros S1 Hcl Htc.
    destruct (Σ1_compression Hcl S1) as [α (dec_α & b1_α & Hα)].
    assert (bounded 0 (∃ α)) as b0_α by (now solve_bounds).
    eapply IE with (∃ α).
    1: eapply CE2; apply Hα.
    apply Σ1_completeness_intu; auto.
    1: do 2 constructor; auto.
    assert (Qeq ⊢C ∃ α) as H.
    { eapply IE with ϕ; auto.
      apply prv_intu_peirce. 
      eapply CE1. apply Hα. }
    apply Fr_cl_to_min, soundness in H.
    refine (let H' := H nat (extend_interp interp_nat _) (fun _ => 0) _ in _).
    cbn in H'; apply H'. clear H H'.
    intros [n Hn].
    destruct (dec_α intu (fun _ => num n)) as [H|H].
    - intro. apply num_bound.
    - exists n. apply soundness in H.
      eapply sat_single_nat. 
      erewrite bounded_subst.
      + apply H, nat_is_Q_model.
      + eauto.
      + intros []; [reflexivity|lia].
    - apply prv_intu_peirce with (p:=class) in H.
      apply Fr_cl_to_min, soundness in H.
      refine (let H' := H nat (extend_interp interp_nat _) (fun _ => 0) _ in _).
      cbn in H'. apply H'; clear H H'.
      rewrite <-subst_Fr. apply sat_comp.
      eapply bound_ext with (N:=1).
      3 : apply Hn.
      { now apply bounded_Fr. }
      intros []; [intros _;cbn|lia].
      apply nat_eval_num.
      Unshelve. all: apply nat_sat_Fr_Q.
  Qed.

  Context `{pei : peirce}.

  Lemma Σ1_soundness ϕ :
    Σ1 ϕ -> bounded 0 ϕ -> Qeq ⊢ ϕ -> interp_nat ⊨= ϕ.
  Proof.
    intros HΣ Hb Hϕ. intros ρ. 
    destruct pei eqn:H; eapply soundness. 
    - apply Σ1_conservativity.
      * congruence.
      * assumption.
      * assumption.
    - apply nat_is_Q_model.
    - apply Hϕ.
    - apply nat_is_Q_model.
  Qed.

End conservativity.

Section Sigma1completeness.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Context `{pei : peirce}.

  (** # <a id="Sigma1_completeness" /> #*)
  Theorem Σ1_completeness φ : Σ1 φ -> bounded 0 φ -> interp_nat ⊨= φ -> Qeq ⊢ φ.
  Proof.
    destruct pei; last apply Σ1_completeness_intu.
    enough (forall ρ, Σ1 φ -> bounded 0 φ[ρ] -> interp_nat ⊨= φ[ρ] -> Qeq ⊢C φ[ρ]).
    { intros HΣ Hb Hsat. rewrite <-subst_var. apply H.
      - easy.
      - now rewrite subst_var.
      - intros ρ'. rewrite subst_var. apply Hsat. }
    intros ρ. induction 1 as [φ H IH|φ H] in ρ |-*.
    - cbn. invert_bounds.
      intros Hnat. destruct (Hnat (fun _ => 0)) as [d Hd].
      remember intu as Hintu. (* for proof mode *)
      fexists (num d). rewrite subst_comp. apply IH.
      + rewrite <-subst_comp. eapply subst_bounded_max; last apply H4.
        intros [|n] Hn; last lia. apply num_bound.
      + intros ρ'. rewrite <-subst_comp.
        rewrite sat_single_nat in Hd.
        eapply sat_closed; last apply Hd.
        eapply subst_bounded_max; last apply H4. 
        intros [|n] Hn; last lia. apply num_bound.
    - intros Hb Hnat.
      assert (@Qdec φ[ρ]) as H'.
      { apply Qdec_subst, H. }
      destruct (H' class (fun _ => zero)) as [H1|H1].
      { intros _. solve_bounds. }
      all: rewrite bounded_0_subst in H1; try eassumption.
      contradict Hnat.
      apply Σ1_soundness with (rho := fun _ => 0) in H1.
      + cbn in H1. contradict H1. apply H1.
      + constructor. apply Qdec_impl.
        * assumption.
        * apply Qdec_bot.
      + now solve_bounds.
  Qed.


  (** # <a id="Sigma1_witness" /> #*)
  Theorem Σ1_witness φ : Σ1 φ -> bounded 1 φ -> Qeq ⊢ ∃φ -> exists x, Qeq ⊢ φ[(num x)..].
  Proof.
    intros Hb HΣ Hφ. eapply Σ1_soundness with (rho := fun _ => 0) in Hφ as [x Hx].
    exists x. eapply Σ1_completeness.
    - now apply Σ1_subst.
    - eapply subst_bounded_max; last eassumption.
      intros [|n] H; last lia. apply num_bound.
    - intros ρ. rewrite sat_single_nat in Hx. 
      eapply sat_closed; last eassumption.
      eapply subst_bounded_max; last eassumption.
      intros [|n] H; lia + apply num_bound.
    - now constructor.
    - now constructor.
  Qed.

End Sigma1completeness.
