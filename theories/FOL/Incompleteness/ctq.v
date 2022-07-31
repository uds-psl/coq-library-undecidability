From Undecidability.Shared Require Import embed_nat Dec.
From Undecidability.Synthetic Require Import Definitions EnumerabilityFacts.

From Undecidability.FOL Require Import FullSyntax Axiomatisations.
From Undecidability.FOL.Arithmetics Require Import Signature Robinson NatModel.

From Undecidability.FOL.Incompleteness Require Import utils fol qdec bin_qdec sigma1 epf epf_mu.
From Undecidability.FOL.Proofmode Require Import Theories ProofMode.

Require Import Lia String List.
Import ListNotations.

(** * Church's thesis for Q *)
Section ctq.
  Context {pei : peirce}.

  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  Existing Instance interp_nat.
  Definition CTQ := 
    forall (f : nat -\ nat), exists φ, bounded 2 φ /\ Σ1 φ /\ (forall x y, f x ▷ y <-> Qeq ⊢ ∀ φ[num x .: $0 ..] ↔ $0 == num y).
  Definition CTQ_total := 
    forall (f : nat -> nat), exists φ, bounded 2 φ /\ Σ1 φ /\ forall x, Qeq ⊢ ∀ φ[num x .: $0..] ↔ $0 == num (f x).
  Definition uCTQ := 
    exists φ, bounded 3 φ /\ Σ1 φ /\ forall (f : nat -\ nat), exists c, (forall x y, f x ▷ y <-> Qeq ⊢ ∀ φ[num c .: num x .: $0 ..] ↔ $0 == num y).

  Lemma uctq_ctq : uCTQ -> CTQ.
  Proof.
    intros (φ & Hb & HΣ & Hφ). 
    intros f. destruct (Hφ f) as [c Hc].
    exists (φ[(num c)..]). 
    split.
    { eapply subst_bounded_max; last eassumption.
      intros [|[|[|n]]]; solve_bounds; apply num_bound. }
    split.
    { apply Σ1_subst, HΣ. }
    intros x y.  specialize (Hc x y). 
    enough (φ[num c .: num x .: $0 ..] = φ[(num c)..][num x .: $0..]) by congruence.
    rewrite subst_comp. apply subst_ext.
    intros [|[|[|n]]]; cbn; now rewrite ?num_subst.
  Qed.

  Lemma ctq_ctq_total : CTQ -> CTQ_total.
  Proof.
    intros ctq f. destruct (ctq (partialise f)) as (φ & Hb & HΣ & Hφ).
    exists φ. do 2 (split; first assumption). 
    intros x. apply Hφ. exists 0. reflexivity.
  Qed.

End ctq.


Section ctq_epf.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  Existing Instance interp_nat.
  Context {pei : peirce}.

  Lemma Q_num_inj x y : Qeq ⊢ num x == num y -> x = y.
  Proof. 
    intros H. apply Σ1_soundness with (rho := fun _ => 0) in H.
    - cbn in H. now erewrite !nat_eval_num in H.
    - constructor. apply Qdec_eq.
    - solve_bounds; apply num_bound.
  Qed.

  Lemma prv_enumerable (T : list form) (p' : peirce) :
    enumerable (fun phi => T ⊢ phi).
  Proof.
    edestruct (@tprv_enumerable PA_funcs_signature PA_preds_signature) with (T := list_theory T) as [f Hf].
    - apply enumerable_PA_funcs.
    - exact _.
    - apply enumerable_PA_preds.
    - exact _.
    - apply list_theory_enumerable.
    - exists f. intros phi. unfold enumerator in Hf.
      rewrite <-Hf. split.
      + intros H. exists T. eauto.
      + intros [T' HT']. apply Weak with (A := T'); firstorder.
  Qed.

  (** ** Church's thesis implies EPF *)
  Lemma ctq_epfn : CTQ -> EPF_N.
  Proof.
    unshelve edestruct (@form_enumerable PA_funcs_signature PA_preds_signature enumerable_PA_funcs enumerable_PA_preds) as [f_form Hform].
    assert (semi_decidable (fun ψ => Qeq ⊢ ψ)) as [f_prv Hprv].
    { apply enumerable_semi_decidable.
      - apply form_discrete.
      - apply prv_enumerable. }

    intros ctq.
    unshelve eexists.
    { intros c. 
      intros x. unshelve eexists.
      { intros k. 
        destruct (f_form c) as [φ|]. 2: exact None.
        destruct (unembed k) as [l y].
        destruct (f_prv (∀ φ[num x .: $0 ..] ↔ $0 == num y) l).
        - exact (Some y).
        - exact None. }
      intros y1 y2 k1 k2. destruct (f_form c) as [φ|] eqn:Hc; cbn.
      2: congruence. 
      destruct (unembed k1) as [l1 y'1].
      destruct (unembed k2) as [l2 y'2].
      destruct (f_prv _ l1) eqn:H1, (f_prv _ l2) eqn:H2.  2-4: congruence. intros [= <-] [= <-].
      assert (Qeq ⊢ ∀ φ[num x .: $0..] ↔ $0 == num y'1) as H1'. 
      { apply Hprv. eauto. }
      assert (Qeq ⊢ ∀ φ[num x .: $0..] ↔ $0 == num y'2) as H2'. 
      { apply Hprv. eauto. }
      enough (Qeq ⊢ num y'1 == num y'2).
      { apply Q_num_inj, H. }
      fspecialize (H2' (num y'1)). rewrite num_subst in H2'.
      fapply H2'.
      fspecialize (H1' (num y'1)). rewrite num_subst in H1'.
      fapply H1'. fapply ax_refl. }
    intros f. destruct (ctq f) as (φ & H1 & H2 & Hφ).
    destruct (Hform φ) as [c Hc]. exists c.
    intros x y. setoid_rewrite Hφ. cbn. split.
    - intros H. apply Hprv in H as [l Hl].
      exists (embed (l, y)). cbn.
      rewrite Hc. rewrite embedP. rewrite Hl.
      reflexivity.
    - intros [k H3]. cbn in H3.
      rewrite Hc in H3. destruct (unembed k) as [l y'].
      destruct f_prv eqn:H.
      + apply Hprv. exists l. now injection H3 as ->.
      + congruence.
  Qed.

End ctq_epf.

Section ctq_repr.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  Existing Instance interp_nat.

  Context {p : peirce}. 

  (** ** Church's thesis implies weak representability  and strong separability *)
  Lemma ctq_weak_repr (ctq : CTQ_total) (P : nat -> Prop) :
    enumerable P -> exists φ,
    bounded 1 φ /\ Σ1 φ /\ forall x, P x <-> Qeq ⊢ φ[(num x)..].
  Proof.
    intros [f Hf].
    pose (f' := fun x => match f x with Some y => S y | None => 0 end).
    destruct (ctq f') as (φ & Hb & HΣ & Hφ).
    exists (∃(φ[$0 .: (σ $1) ..])).
    repeat apply conj.
    { constructor. eapply subst_bounded_max; last eassumption.
      intros [|[|n]] ?; repeat solve_bounds. }
    { constructor. apply Σ1_subst, HΣ. }
    intros x. unfold enumerator in Hf. setoid_rewrite Hf.
    split.
    - intros [k Hk]. cbn. 
      fexists (num k). 
      specialize (Hφ k). fspecialize (Hφ (num (f' k))).
      rewrite num_subst in Hφ.
      replace (φ[_][_][_]) with (φ[num k .: $0 ..][(num (f' k))..]).
      { fapply Hφ. fapply ax_refl. }
      rewrite !subst_comp. eapply bounded_subst; first eassumption.
      intros [|[|n]] ?; cbn; rewrite ?num_subst.
      + reflexivity.
      + unfold f'. rewrite Hk. reflexivity.
      + lia.
    - cbn. intros [k Hk]%Σ1_witness. 
      2: { apply Σ1_subst, Σ1_subst, HΣ. }
      2: { rewrite subst_comp. eapply subst_bounded_max; last eassumption.
        intros [|[|n]] ?; cbn.
        - constructor. lia.
        - repeat (solve_bounds; rewrite ?num_subst); apply num_bound. 
        - lia. }
      exists k.
      enough (f' k = S x) as H.
      { unfold f' in H. now destruct (f k). }
      apply Q_num_inj. 
      specialize (Hφ k). fspecialize (Hφ (num (S x))). 
      rewrite num_subst in Hφ. 
      fapply ax_sym. fapply Hφ.
      replace (φ[_][_][_]) with (φ[num k .: $0 ..][(σ num x)..]) in Hk; first easy.
      rewrite !subst_comp. eapply bounded_subst; first eassumption.
      intros [|[|n]] ?; cbn; rewrite ?num_subst; easy + lia.
  Qed.

  Lemma ctq_strong_sepr (ctq : CTQ) (P Q : nat -> Prop) :
    (forall x, P x -> Q x -> False) ->
    semi_decidable P -> semi_decidable Q ->
    exists φ, bounded 1 φ /\ Σ1 φ /\ 
      (forall x, P x -> Qeq ⊢ φ[(num x)..]) /\ 
      (forall x, Q x -> Qeq ⊢ ¬φ[(num x)..]).
  Proof.
    intros Hdisj HP HQ.
    destruct (enumerable_separable Hdisj HP HQ) as [f Hf].
    destruct (ctq (fun x => comp_part_total (fun b : bool => if b then 1 else 0) (f x))) as (φ & Hb & HΣ & Hφ).
    exists (φ[$0 .: (num 1) ..]). repeat split.
    { eapply subst_bounded_max; last eassumption.
      intros [|[|n]] ?; cbn; repeat solve_bounds. }
    { apply Σ1_subst, HΣ. }
    - intros x Hx%Hf. 
      assert (comp_part_total (fun b : bool => if b then 1 else 0) (f x) ▷ 1) as H%Hφ.
      { destruct Hx as [k Hk]. exists k. cbn. now rewrite Hk. }
      fspecialize (H (num 1)).
      replace (φ[_][_]) with (φ[num x .: $0..][(num 1)..]).
      { fapply H. fapply ax_refl. }
      rewrite !subst_comp. eapply bounded_subst; first eassumption.
      intros [|[|n]]?; cbn; rewrite ?num_subst; easy + lia.
    - intros x Hx%Hf. 
      assert (comp_part_total (fun b : bool => if b then 1 else 0) (f x) ▷ 0) as H%Hφ.
      { destruct Hx as [k Hk]. exists k. cbn. now rewrite Hk. }
      fspecialize (H (num 1)).
      replace (φ[_][_]) with (φ[num x .: $0..][(num 1)..]).
      { fstart. fintros "H". fapply H in "H". 
        (* For some reason, these assumption cause fapply to take a long time *)
        clear H Hx x Hφ HΣ Hb φ Hf f HQ HP Hdisj P Q ctq.
        fapply (ax_zero_succ zero). fapply ax_sym.
        ctx. }
      rewrite !subst_comp. eapply bounded_subst; first eassumption.
      intros [|[|n]]?; cbn; rewrite ?num_subst; easy + lia.
  Qed.

End ctq_repr.

Section ctq.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  Existing Instance interp_nat.

  Context `{pei : peirce}.

  Variable theta : nat -> nat -\ nat.
  Variable theta_universal : is_universal theta.

  Variable (φ : form).
  Hypothesis φ1_qdec : Qdec φ.
  Hypothesis φ1_bounded : bounded 4 φ.
  Hypothesis wrepr : forall c x y, theta c x ▷ y <-> Qeq ⊢ ∃ φ[$0 .: num c .: num x .: (num y)..].

  Local Definition ψ' : form :=
    φ ∧ ∀∀ ($1 ⊕ $0 ⧀= $5 ⊕ $2) → φ[$0.:$3.:$4.:$1..] → $1 == $5.
  Local Definition ψ : form := ∃ψ'.

  Lemma ψ'_bounded : bounded 4 ψ'.
  Proof.
    repeat solve_bounds.
    - auto.
    - rewrite pless_eq. cbn. unfold "↑". repeat solve_bounds.
    - eapply subst_bounded_max; last eassumption.
      intros [|[|[|[|k]]]]; solve_bounds.
  Qed.
  Lemma ψ_bounded : bounded 3 ψ.
  Proof.
    constructor. apply ψ'_bounded.
  Qed.
  Lemma ψ'_Qdec : Qdec ψ'.
  Proof.
    apply Qdec_and.
    - auto.
    - apply (Qdec_bin_bounded_forall ($3 ⊕ $0)).
      apply Qdec_impl.
      + now apply Qdec_subst. 
      + apply Qdec_eq.
  Qed.
  Lemma ψ_Σ1 : Σ1 ψ.
  Proof.
    constructor. constructor.
    apply ψ'_Qdec.
  Qed.
  Lemma ψ_subst c x y : ψ[c.:x.:y..] = 
    ∃ φ[$0 .: c`[↑] .: x`[↑] .: y`[↑]..] ∧ ∀∀ ($1 ⊕ $0 ⧀= y`[↑]`[↑]`[↑] ⊕ $2) → φ[$0 .: c`[↑]`[↑]`[↑] .: x`[↑]`[↑]`[↑] .: $1..] → $1 == y`[↑]`[↑]`[↑].
  Proof.
    cbn. do 2 f_equal.
    { eapply bounded_subst; first eassumption.
      intros [|[|[|[|n]]]]; cbn; solve_bounds. }
    do 4 f_equal.
    rewrite subst_comp. 
    eapply bounded_subst; first eassumption.
    intros [|[|[|[|n]]]]; cbn; solve_bounds.
  Qed.
  Lemma ψ'_subst k c x y :
    ψ'[k .: c .: x .: y ..] = φ[k .: c .: x .: y..] ∧  ∀∀ ($1 ⊕ $0 ⧀= y`[↑]`[↑] ⊕ k`[↑]`[↑]) → φ[$0 .: c`[↑]`[↑] .: x`[↑]`[↑] .: $1..] → $1 == y`[↑]`[↑].
  Proof.
    cbn. f_equal.
    do 4 f_equal.
    rewrite subst_comp. 
    eapply bounded_subst; first eassumption.
    intros [|[|[|[|n]]]]; cbn; solve_bounds.
  Qed.

  Lemma ψ_φ s t u :
    Qeq ⊢ ψ[s.:t.:u..] → ∃ φ[$0 .: s`[↑] .: t`[↑] .: u`[↑]..].
  Proof.
    rewrite ψ_subst. fstart.
    fintros "[k [H1 H2]]".
    fexists k. 
    fapply "H1".
  Qed.

  Lemma ψ_theta c x y :
    Qeq ⊢ ∀ ψ[num c .: num x .: $0 ..] ↔ $0 == num y -> theta c x ▷ y.
  Proof.
    intros H. apply wrepr.
    rewrite <-(num_subst c ↑), <-(num_subst x ↑), <-(num_subst y ↑).
    eapply IE; first apply ψ_φ.
    apply AllE with (t := num y) in H.
    cbn -[ψ] in H. replace (ψ[_][_]) with ψ[num c .: num x .: (num y)..] in H.
    2: { rewrite subst_comp. eapply bounded_subst; first apply ψ_bounded.
      intros [|[|[|n]]]; solve_bounds; cbn; now rewrite num_subst. }
    eapply IE.
    { eapply CE2, H. }
    rewrite num_subst. fapply ax_refl.
  Qed.

  Lemma sat_pless ρ s t :
    interp_nat; ρ ⊨ (s ⧀= t) <-> (eval ρ s) <= (eval ρ t).
  Proof.
    rewrite pless_eq. split.
    - intros [k Hk]. cbn in Hk.
      rewrite !eval_up in Hk. lia.
    - intros H. cbn. exists (eval ρ t - eval ρ s).
      rewrite !eval_up. lia.
  Qed.


  Lemma theta_ψ c x y :
    theta c x ▷ y -> Qeq ⊢ ψ[num c .: num x .: (num y) ..].
  Proof.
    intros H.
    apply Σ1_completeness.
    { apply Σ1_subst, ψ_Σ1. }
    { eapply subst_bounded_max; last apply ψ_bounded.
      intros [|[|[|n]]]; solve_bounds; apply num_bound. }
    intros ρ.
    pose proof H as [k Hk]%wrepr%Σ1_witness; first apply Σ1_soundness with (rho := ρ) in Hk; first last.
    { eapply subst_bounded_max; last eassumption.
      intros [|[|[|[|n]]]]; solve_bounds; apply num_bound. }
    { apply Σ1_subst. now constructor. }
    { rewrite subst_comp. eapply subst_bounded_max; last eassumption.
      intros [|[|[|[|n]]]]; solve_bounds; cbn; rewrite ?num_subst; apply num_bound. }
    { do 2 apply Σ1_subst. now constructor. }
    exists k. split.
    - pattern (φ[up (num c .: num x .: (num y)..)]).
      erewrite bounded_subst.
      + apply sat_single_nat, Hk.
      + eassumption.
      + intros [|[|[|[|n]]]]; solve_bounds; apply num_subst.
    - intros y' k' _ H'. cbn.
      rewrite !num_subst. rewrite nat_eval_num.
      eapply part_functional; last apply H.
      apply wrepr, Σ1_completeness.
      { do 2 constructor. now apply Qdec_subst. }
      { constructor. eapply subst_bounded_max; last eassumption.
        intros [|[|[|[|n]]]]; solve_bounds; apply num_bound. }
      intros ρ'. exists k'. 
      apply sat_single_nat. do 3 rewrite sat_single_nat in H'.
      evar (f : form).
      replace φ[_][_] with ?f.
      + eapply sat_closed; last apply H'.
        rewrite !subst_comp. eapply subst_bounded_max; last eassumption.
        intros [|[|[|[|n]]]] Hn; cbn; rewrite ?num_subst; apply num_bound + lia.
      + rewrite !subst_comp.
        eapply bounded_subst; first eassumption.
        intros [|[|[|[|n]]]] Hn; cbn; rewrite ?num_subst; congruence + lia.
  Qed.

  Lemma ψ_functional c x y y' :
    Qeq ⊢ ψ[num c .: num x .: (num y) ..] -> Qeq ⊢ ψ[num c .: num x .: y'..] → y' == num y.
  Proof. 
    cbn -[ψ']. 
    intros [k Hk]%Σ1_witness.
    2: { apply Σ1_subst. constructor. apply ψ'_Qdec. }
    2: { eapply subst_bounded_max; last apply ψ'_bounded.
      intros [|[|[|[|n]]]]; solve_bounds; cbn; rewrite num_subst; apply num_bound. }
    replace ψ'[_][_] with ψ'[num k .: num c .: num x .: (num y) ..] in Hk.
    2: { rewrite subst_comp. apply subst_ext.
      intros [|[|[|[|n]]]]; cbn; now rewrite ?num_subst. }
    rewrite ψ'_subst in Hk.
    assert (Qeq ⊢ φ[num k .: num c .: num x .: (num y)..]) as Hk1.
    { eapply CE1, Hk. }
    assert (Qeq ⊢ (∀ (∀ $1 ⊕ $0 ⧀= (num y)`[↑]`[↑] ⊕ (num k)`[↑]`[↑] → φ[$0 .: (num c)`[↑]`[↑] .: (num x)`[↑]`[↑] .: $1..] → $1 == (num y)`[↑]`[↑]))) as Hk2.
    { eapply CE2, Hk. }
    clear Hk.
    fintros "[k' [Hk21 Hk22]]".
    assert (bounded_t 0 (num y ⊕ num k)) as Hbyk.
    { solve_bounds; apply num_bound. }
    pose proof (@Qsdec_le pei (num y ⊕ num k) (y' ⊕ k') Hbyk) as Hyk.
    eapply DE.
    { eapply Weak; first apply Hyk. now do 2 right. }
    - assert (Qeq ⊢ ax_sym) as Hsym by ctx.
      unfold ax_sym in Hsym.
      apply AllE with (t := num y) in Hsym. cbn in Hsym.
      apply AllE with (t := y') in Hsym. cbn in Hsym.
      rewrite subst_term_shift in Hsym.
      eapply IE.
      { eapply Weak; first apply Hsym. now do 3 right. }
      eapply AllE_Ctx with (t := (num y)).
      { right. left. reflexivity. }
      cbn.
      eapply AllE_Ctx with (t := (num k)).
      { left. reflexivity. }
      cbn. rewrite !pless_subst. cbn. rewrite !num_subst.
      rewrite !up_term, !subst_term_shift.
      eapply IE. 1: eapply IE.
      1: { apply Ctx. left. reflexivity. }
      + ctx.
      + replace (φ[_][_][_][_][_]) with (φ[num k .: num c .: num x .: (num y) ..]).
        * eapply Weak; first apply Hk1. now do 5 right.
        * rewrite !subst_comp. eapply bounded_subst; first eassumption.
          intros [|[|[|[|n]]]] H; cbn; rewrite ?num_subst; lia + reflexivity.
    - apply AllE with (t := y') in Hk2. cbn in Hk2.
      apply AllE with (t := k') in Hk2.  cbn in Hk2.
      rewrite !pless_subst in Hk2. cbn in Hk2. rewrite !num_subst, subst_term_shift in Hk2.
      eapply IE. 1: eapply IE. 
      1: { eapply Weak; first apply Hk2. now do 3 right. }
      + ctx.
      + apply Ctx. right. right. left. 
        rewrite !subst_comp. eapply bounded_subst; first eassumption.
        intros [|[|[|[|n]]]] Hn; cbn; rewrite ?num_subst; reflexivity + lia.
  Qed.

  Lemma epf_n_uctq : uCTQ.
  Proof.
    exists ψ.
    split; first apply ψ_bounded.
    split; first apply ψ_Σ1.
    intros f. destruct (theta_universal f) as [c Hc]. exists c.
    intros x y. 
    split; first (intros Hf; apply AllI_named; intros y'; cbn -[ψ]; apply CI).
    - fintros. rewrite num_subst.
      pose proof (@ψ_functional c x y y') as Heq.
      eapply IE.
      + eapply Weak.
        * apply Heq, theta_ψ, Hc, Hf.
        * now right.
      + apply Ctx. left.
        rewrite subst_comp. eapply bounded_subst; first apply ψ_bounded.
        intros [|[|[|n]]]; cbn; lia + now rewrite ?num_subst.
    - fintros.
      eapply IE.
      { eapply IE.
        { eapply Weak.
          { apply (Q_leibniz ψ[num c .: num x .: $0 ..] (num y) y'). }
          now right. }
        rewrite num_subst.
        fapply ax_sym. ctx. }
      eapply Weak.
      + rewrite subst_comp. erewrite bounded_subst.
        * apply theta_ψ, Hc, Hf.
        * apply ψ_bounded.
        * intros [|[|[|n]]]; solve_bounds; apply num_subst.
      + now right.
    - intros H. apply Hc, ψ_theta, H.
  Qed.
End ctq.

Section ctq.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  Existing Instance interp_nat.

  Context `{pei : peirce}.

  Definition embed' t := embed t * 2.
  Definition unembed' c := unembed (Nat.div c 2).

  Lemma unembed'_embed' x y : unembed' (embed' (x, y)) = (x, y).
  Proof.
    unfold unembed', embed'.
    rewrite PeanoNat.Nat.div_mul.
    - apply embedP.
    - lia.
  Qed.
  Lemma gaussian_sum x : 2 * nat_rec (fun _ : nat => nat) 0 (fun i m : nat => S i + m) x = 
    x * (x + 1).
  Proof.
    induction x as [|x IH]; cbn in *; lia.
  Qed.

  Lemma embed'_expl x y : embed' (x, y) = y * 2 + (y + x) * (y + x + 1).
  Proof.
    unfold embed', embed.
    rewrite <-gaussian_sum. lia.
  Qed.
  Lemma compress_free φ n : bounded (S n) φ -> exists ρ,
    bounded (S (S n)) (φ[ρ]) /\ forall x y, Qeq ⊢ φ[(num (embed' (x, y)))..] ↔ φ[ρ][num x .: (num y)..].
  Proof. 
    intros Hb.
    exists (($1 ⊗ (σ σ zero) ⊕ ($1 ⊕ $0) ⊗ ($1 ⊕ $0 ⊕ σ zero)).:(S >> S >> var)).
    split. 
    { eapply subst_bounded_max; last eassumption.
      intros [|k] H; cbn.
      - repeat (constructor; lia + solve_bounds).
      - unfold funcomp. constructor. lia. }
    intros x y.
    assert (Qeq ⊢ num (embed' (x, y)) == num y ⊗ (σ σ zero) ⊕ (num y ⊕ num x) ⊗ (num y ⊕ num x ⊕ σ zero)) as Heq.
    { apply Σ1_completeness.
      { constructor. apply Qdec_eq. }
      { repeat solve_bounds; apply num_bound. }
      intros ρ. cbn. rewrite !nat_eval_num. apply embed'_expl. }
    replace (φ[_][_]) with φ[(num y ⊗ σ (σ zero) ⊕ (num y ⊕ num x) ⊗ (num y ⊕ num x ⊕ σ zero))..].
    2: { rewrite subst_comp. apply subst_ext.
      intros [|k]; reflexivity. }
    fsplit.
    - fapply Q_leibniz. apply Heq.
    - fapply Q_leibniz. fapply ax_sym. apply Heq.
  Qed.
  Lemma compress_free3 φ n : bounded (S n) φ -> exists ρ,
    bounded (S (S (S n))) (φ[ρ]) /\ forall x y z, Qeq ⊢ φ[(num (embed' (embed' (x, y), z)))..] ↔ φ[ρ][num x .: num y .: (num z)..].
  Proof.
    intros Hb.
    destruct (compress_free Hb) as (ρ1 & Hb1 & Hρ1).
    destruct (compress_free Hb1) as (ρ2 & Hb2 & Hρ2).
    rewrite subst_comp in Hb2.
    eexists. split.
    { apply Hb2. }
    intros x y z.
    rewrite <-subst_comp.
    fstart. fsplit.
    - fintros "H".
      (* rewrite subst_cons_comp3. *)
      specialize (Hρ2 x y). apply subst_Weak with (xi := (num z)..) in Hρ2.
      change (map _ _) with Qeq in Hρ2.
      specialize (Hρ1 (embed' (x, y)) z).
      asimpl. asimpl in Hρ1. asimpl in Hρ2. 
      rewrite !num_subst in Hρ2.
      fapply Hρ2. fapply Hρ1. ctx.
    - fintros "H". fapply Hρ1. 
      specialize (Hρ2 x y). apply subst_Weak with (xi := (num z)..) in Hρ2.
      change (map _ _) with Qeq in Hρ2.
      asimpl. asimpl in Hρ2. rewrite !num_subst in Hρ2.
      fapply Hρ2. ctx.
  Qed.

  Variable theta_mu_universal : is_universal theta_mu.

  Lemma embed'_unembed' t x y :
    embed' (x, y) = t -> unembed' t = (x, y).
  Proof. 
    intros <-. apply unembed'_embed'.
  Qed.

  Lemma theta_mu_enumerable : enumerable (fun t => let '(t', y) := unembed' t in let '(c, x) := unembed' t' in theta_mu c x ▷ y).
  Proof.
    apply semi_decidable_enumerable.
    { exists Some. intros x. eauto. }
    unshelve eexists.
    { intros [[c x]%unembed' y]%unembed' k.
      destruct ((theta_mu c x).(core) k) as [y'|].
      - exact (nat_eq_dec y y').
      - exact false. }
    intros t.
    destruct (unembed' t) as [t' y] eqn:H1, (unembed' t') as [c x] eqn:H2.
    split.
    - intros [k Hk]. exists k. cbv zeta match beta.
      rewrite H2. rewrite Hk. now apply Dec_reflect.
    - intros [k Hk]. exists k.
      cbv zeta match beta in Hk.
      rewrite H2 in Hk.
      destruct core.
      + now apply Dec_reflect in Hk.
      + discriminate.
  Qed.

  (** ** EPF_mu implies CTQ *)
  Lemma epf_mu_uctq : uCTQ.
  Proof.
    destruct (@Q_weak_repr pei theta_mu_universal (fun t => let '(t', y) := unembed' t in let '(c, x) := unembed' t' in theta_mu c x ▷ y)) as (φ1 & Hb1 & HΣ1 & Hφ1); first apply theta_mu_enumerable.
    assert (exists φ, Σ1 φ /\ bounded 3 φ /\ forall c x y, theta_mu c x ▷ y <-> Qeq ⊢ φ[num c .: num x .: (num y)..]) as (φ2 & HΣ2 & Hb2 & Hφ2).
    { destruct (compress_free3 Hb1) as (ρ & Hb & Hρ). exists (φ1[ρ]).
      split; first (apply Σ1_subst, HΣ1).
      split; first assumption.
      intros c x y. 
      specialize (Hφ1 (embed' (embed' (c, x), y))). rewrite !unembed'_embed' in Hφ1.
      setoid_rewrite Hφ1.
      split; intros H; fapply Hρ; apply H. }
    assert (exists φ, Qdec φ /\ bounded 4 φ /\ forall c x y, theta_mu c x ▷ y <-> Qeq ⊢ ∃ φ[$0 .: num c .: num x .: (num y)..]) as (φ3 & HQ3 & Hb3 & Hφ3).
    { destruct (Σ1_compression Hb2 HΣ2) as (φ & HQ & Hb & Hφ). 
      exists φ. do 2 (split; first assumption).
      intros c x y. rewrite Hφ2.
      apply subst_Weak with (xi := num c .: num x .: (num y)..) in Hφ.
      change (map _ _) with Qeq in Hφ. cbn in Hφ.
      replace (φ[$0 .: _]) with (φ[up (num c .: num x .: (num y)..)]).
      { apply prv_intu_class with (p := pei) in Hφ. split; intros H; fapply Hφ; apply H. }
      eapply bounded_subst; first eassumption.
      intros [|[|[|[|n]]]] H; cbn; lia + now rewrite ?num_subst. }
    eapply epf_n_uctq with (theta := theta_mu) (φ := φ3).
    all: assumption.
  Qed.
  Lemma epf_mu_ctq : CTQ.
  Proof.
    apply uctq_ctq, epf_mu_uctq.
  Qed.

End ctq.
