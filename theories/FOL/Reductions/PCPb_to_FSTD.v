(* ** Reduction from PCP to deductive entailment *)

Require Import Undecidability.FOL.Syntax.Facts.
Require Import Undecidability.FOL.Semantics.Tarski.FullFacts.
Require Import Undecidability.FOL.Deduction.FullNDFacts.
Require Import Undecidability.FOL.Sets.FST.
Require Import Undecidability.FOL.FST.
Require Import Undecidability.FOL.Reductions.PCPb_to_FST.

From Undecidability.PCP Require Import PCP Util.PCP_facts Reductions.PCPb_iff_dPCPb.

From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations ListAutomationHints.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Local Definition BSRS := list(card bool).
Local Notation "x / y" := (x, y).

Local Hint Constructors prv : core.

(* ** Simple derivations in FST *)

Section FST.

Context { p : peirce }.

Close Scope sem.

Lemma FST_eset x :
  FSTeq ⊢ ¬ (x ∈ ∅).
Proof.
  change (FSTeq ⊢ (¬ ($0 ∈ ∅))[x..]).
  apply AllE. apply Ctx. firstorder.
Qed.

Lemma FST_eset' T x :
  FSTeq <<= T -> T ⊢ ¬ (x ∈ ∅).
Proof.
  intros H. now apply (Weak (FST_eset x)).
Qed.

Fixpoint tnumeral n :=
  match n with 
  | O => ∅
  | S n => σ (tnumeral n)
end.

Lemma FST_refl' T x :
  FSTeq <<= T -> T ⊢ x ≡ x.
Proof.
  intros H. change (T ⊢ ($0 ≡ $0)[x..]).
  apply AllE. apply Ctx. firstorder.
Qed.

Lemma FST_refl x :
  FSTeq ⊢ x ≡ x.
Proof.
  now apply FST_refl'.
Qed.

Lemma FST_sym' T x y :
  FSTeq <<= T -> T ⊢ x ≡ y -> T ⊢ y ≡ x.
Proof.
  intros H1 H2. eapply IE; try apply H2.
  assert (H : T ⊢ ax_sym) by (apply Ctx; firstorder).
  apply (AllE x), (AllE y) in H; cbn in H. now subsimpl_in H.
Qed.

Lemma FST_trans' T x y z :
  FSTeq <<= T -> T ⊢ x ≡ y -> T ⊢ y ≡ z -> T ⊢ x ≡ z.
Proof.
  intros H1 H2 H3. eapply IE; try apply H3.
  eapply IE; try apply H2.
  assert (H : T ⊢ ax_trans) by (apply Ctx; firstorder).
  now apply (AllE x), (AllE y), (AllE z) in H; cbn in H; subsimpl_in H.
Qed.

Lemma FST_eq_elem T x y x' y' :
  FSTeq <<= T -> T ⊢ x ≡ x' -> T ⊢ y ≡ y' -> T ⊢ x ∈ y -> T ⊢ x' ∈ y'.
Proof.
  intros H1 H2 H3 H4. eapply IE; try apply H4.
  eapply IE; try apply H3. eapply IE; try apply H2.
  assert (H : T ⊢ ax_eq_elem) by (apply Ctx; firstorder).
  now apply (AllE x), (AllE y), (AllE x'), (AllE y') in H; cbn in H; subsimpl_in H.
Qed.

Lemma FST_ext' T x y :
  FSTeq <<= T -> T ⊢ sub x y -> T ⊢ sub y x -> T ⊢ x ≡ y.
Proof.
  intros H1 H2 H3. eapply IE; try apply H3.
  eapply IE; try apply H2.
  assert (H : T ⊢ ax_ext) by (apply Ctx; firstorder).
  apply (AllE x), (AllE y) in H; cbn in H.
  subsimpl_in H. apply H.
Qed.

Lemma FST_adj T x y z :
  FSTeq <<= T -> T ⊢ x ∈ y ::: z <-> T ⊢ x ≡ y ∨ x ∈ z.
Proof.
  intros HT.
  assert (HA : T ⊢ ax_adj) by (apply Ctx; firstorder).
  apply (AllE z), (AllE y), (AllE x) in HA; cbn in HA. subsimpl_in HA.
  split; intros H; eapply IE; try apply H.
  - now apply CE1 in HA.
  - now apply CE2 in HA.
Qed.

Lemma FST_pair_el' T x y z :
  FSTeq <<= T -> T ⊢ (z ≡ x ∨ z ≡ y) <-> T ⊢ z ∈ {x; y}.
Proof.
  intros HT. setoid_rewrite FST_adj; auto.
  split; intros H; apply (DE H); auto.
  - apply DI2. apply FST_adj; auto.
  - assert1 H'. apply DI2. apply FST_adj in H'; auto.
    apply (DE H'); auto. apply Exp. eapply IE; try eapply (FST_eset'); auto.
Qed.

Lemma FST_pair_el x y z :
  FSTeq ⊢ (z ≡ x ∨ z ≡ y) -> FSTeq ⊢ z ∈ {x; y}.
Proof.
  now apply FST_pair_el'.
Qed.

Lemma FST_sub_pair T x y x' y' :
  FSTeq <<= T -> T ⊢ x ≡ x' -> T ⊢ y ≡ y' -> T ⊢ {x; y} ⊆ {x'; y'}.
Proof.
  intros HT H1 H2. prv_all z.
  apply II. apply FST_pair_el'; auto.
  assert1 H. apply FST_adj in H; auto. apply (DE H).
  - apply DI1. apply (FST_trans') with x; auto. apply (Weak H1). auto.
  - apply DI2. clear H. assert1 H. apply FST_adj in H; auto. apply (DE H).
    + apply (FST_trans') with y; auto. apply (Weak H2). auto.
    + apply Exp. eapply IE; try eapply (FST_eset'); auto.
Qed.

Lemma FST_eq_pair T x y x' y' :
  FSTeq <<= T -> T ⊢ x ≡ x' -> T ⊢ y ≡ y' -> T ⊢ {x; y} ≡ {x'; y'}.
Proof.
  intros HT H1 H2. apply FST_ext'; trivial.
  - now apply FST_sub_pair.
  - apply FST_sub_pair; trivial. all: now apply FST_sym'.
Qed.

Lemma FST_eq_opair T x y x' y' :
  FSTeq <<= T -> T ⊢ x ≡ x' -> T ⊢ y ≡ y' -> T ⊢ opair x y ≡ opair x' y'.
Proof.
  intros HT H1 H2. repeat apply FST_eq_pair; trivial.
Qed.

Definition sing x :=
  {x; x}.

Lemma FST_sing_el x :
  FSTeq ⊢ x ∈ sing x.
Proof.
  apply FST_pair_el. apply DI1. apply FST_refl.
Qed.

Lemma FST_sing_iff T x y :
  FSTeq <<= T -> T ⊢ x ∈ sing y <-> T ⊢ x ≡ y.
Proof.
  intros HT. unfold sing.
  rewrite <- FST_pair_el'; trivial.
  split; intros H.
  - apply (DE H); auto.
  - now apply DI1.
Qed.

Lemma FST_sig_el T x :
   FSTeq <<= T -> T ⊢ x ∈ σ x.
Proof.
  intros HT. apply FST_adj; auto. apply DI1. now apply FST_refl'.
Qed.

Lemma FST_eq_sig T x y :
  FSTeq <<= T -> T ⊢ x ≡ y -> T ⊢ σ x ≡ σ y.
Proof.
  intros HT Hxy. apply FST_ext'; auto.
  - prv_all z. apply II. apply FST_adj; auto.
    assert1 H. apply FST_adj in H; auto. apply (DE H).
    + apply DI1. apply FST_trans' with x; auto. apply (Weak Hxy); auto.
    + apply DI2. eapply FST_eq_elem; auto; try apply FST_refl'; auto. apply (Weak Hxy); auto.
  - prv_all z. apply II. apply FST_adj; auto.
    assert1 H. apply FST_adj in H; auto. apply (DE H).
    + apply DI1. apply FST_trans' with y; auto. apply FST_sym'; auto. apply (Weak Hxy); auto.
    + apply DI2. eapply FST_eq_elem; auto; try apply FST_refl'; auto.
      apply FST_sym'; auto. apply (Weak Hxy); auto.
Qed.

Lemma sing_pair1 T x y z :
  FSTeq <<= T -> T ⊢ sing x ≡ {y; z} -> T ⊢ x ≡ y.
Proof.
  intros HT H. apply FST_sym'; trivial.
  apply FST_sing_iff; trivial. eapply FST_eq_elem; trivial.
  apply FST_refl'; trivial. apply FST_sym'; eauto.
  apply FST_pair_el'; trivial. apply DI1. now apply FST_refl'.
Qed.

Lemma sing_pair2 T x y z :
  FSTeq <<= T -> T ⊢ sing x ≡ {y; z} -> T ⊢ x ≡ z.
Proof.
  intros HT H. apply FST_sym'; trivial.
  apply FST_sing_iff; trivial. eapply FST_eq_elem; trivial.
  apply FST_refl'; trivial. apply FST_sym'; eauto.
  apply FST_pair_el'; trivial. apply DI2. now apply FST_refl'.
Qed.

Lemma opair_inj1 T x y x' y' :
  FSTeq <<= T -> T ⊢ opair x y ≡ opair x' y' -> T ⊢ x ≡ x'.
Proof.
  intros HT He. assert (H : T ⊢ {x; x} ∈ opair x y).
  { apply FST_pair_el'; trivial. apply DI1. now apply FST_refl'. }
  eapply FST_eq_elem in H; try apply He; try apply FST_refl'; trivial.
  apply FST_pair_el' in H; trivial.
  apply (DE H); eapply sing_pair1; try apply prv_T1; auto.
Qed.

Lemma opair_inj2 T x y x' y' :
  FSTeq <<= T -> T ⊢ opair x y ≡ opair x' y' -> T ⊢ y ≡ y'.
Proof.
  intros HT H. assert (H' : T ⊢ y ≡ x' ∨ y ≡ y').
  - assert (H2 : T ⊢ {x; y} ∈ opair x' y').
    { eapply FST_eq_elem; trivial. apply FST_refl'; trivial. apply H.
      apply FST_pair_el'; trivial. apply DI2. now apply FST_refl'. }
    apply FST_pair_el' in H2; trivial. apply (DE H2).
    + apply DI1. apply FST_sym'; auto. eapply sing_pair2; auto. apply FST_sym'; auto.
    + apply FST_pair_el'; auto. eapply FST_eq_elem; auto.
      * apply FST_refl'; auto.
      * apply FST_pair_el'; auto. apply DI2. apply FST_refl'. auto.
  - apply (DE H'); try apply prv_T1.
    assert (H1 : T ⊢ x ≡ x') by apply (opair_inj1 HT H).
    assert (H2 : T ⊢ {x'; y'} ∈ opair x y).
    { eapply FST_eq_elem; trivial. apply FST_refl'; trivial. apply FST_sym', H; trivial.
      apply FST_pair_el'; trivial. apply DI2. now apply FST_refl'. }
    apply FST_pair_el' in H2; trivial.
    eapply DE; try eapply (Weak H2); auto.
    + eapply FST_trans'; auto. eapply FST_trans'; auto.
      * apply FST_sym'. auto. apply (Weak H1). auto.
      * eapply sing_pair2; auto. apply FST_sym'; auto.
    + eapply FST_trans'; auto. eapply sing_pair2; auto. eapply FST_trans'; auto.
      2: apply FST_sym'; auto.
      eapply FST_eq_pair; try apply FST_sym'; auto.
      apply (Weak H1). auto.
    + auto.
Qed.

Lemma FST_numeral_trans T n x y :
  FSTeq <<= T -> T ⊢ x ∈ tnumeral n → y ∈ x → y ∈ tnumeral n.
Proof.
  intros HT. induction n; cbn.
  - apply II, Exp. eapply IE. apply FST_eset'. all: auto.
  - repeat apply II. apply FST_adj; auto. assert2 H. apply FST_adj in H; auto. apply (DE H).
    + apply DI2. eapply FST_eq_elem; auto. apply FST_refl'; auto.
    + apply DI2. eapply IE. eapply IE. apply (Weak IHn); auto. auto. auto.
Qed.

Lemma FST_numeral_wf T n :
  FSTeq <<= T -> T ⊢ ¬ (tnumeral n ∈ tnumeral n).
Proof.
  intros HT. induction n; cbn.
  - now apply FST_eset'.
  - apply II. assert1 H. apply FST_adj in H; auto. apply (DE H).
    + eapply IE. apply (Weak IHn); auto. eapply FST_eq_elem; auto.
    + eapply IE. apply (Weak IHn); auto. eapply IE. eapply IE.
      eapply FST_numeral_trans; auto. auto.
      apply FST_adj; auto. apply DI1. apply FST_refl'. auto.
Qed.

Lemma FST_sig_iff T x y :
  FSTeq <<= T -> T ⊢ y ∈ σ x -> T ⊢ y ∈ x ∨ y ≡ x.
Proof.
  intros HT. rewrite FST_adj; auto. intros H. apply (DE H); auto.
Qed.

Lemma FST_numeral T n :
  FSTeq <<= T -> T ⊢ htransitive (tnumeral n).
Proof.
  intros HT. induction n; apply CI; prv_all x; apply II.
  - apply Exp. apply imps. apply FST_eset'. auto.
  - apply Exp. apply imps. apply FST_eset'. auto.
  - prv_all y. apply -> imps. try apply (@FST_numeral_trans T (S n)); auto.
  - eapply DE; try apply FST_sig_iff; auto.
    + apply CE2 in IHn. apply (AllE x) in IHn. apply imps.
      cbn in IHn. subsimpl_in IHn. eapply Weak; eauto.
    + prv_all y. apply II. prv_all z. apply II. eapply FST_eq_elem.
      * auto. 
      * apply FST_refl'. auto.
      * apply FST_sym'; auto.
      * apply imps. eapply IE; try apply FST_numeral_trans; auto.
        eapply FST_eq_elem; auto. apply FST_refl'. auto.
Qed.



(* ** Preservation proof *)

Fixpoint enc_derivations B n :=
  match n with 
  | O => sing (opair ∅ (enc_stack B))
  | S n => opair (tnumeral (S n)) (enc_stack (derivations B (S n))) ::: enc_derivations B n
  end.

Lemma enc_derivations_base R n :
  FSTeq ⊢ {{∅; ∅}; {∅; enc_stack R}} ∈ enc_derivations R n.
Proof.
  induction n; cbn.
  - apply FST_sing_el.
  - apply FST_adj; auto.
Qed.

Lemma enc_derivations_step B n :
  FSTeq ⊢ opair (tnumeral n) (enc_stack (derivations B n)) ∈ enc_derivations B n.
Proof.
  destruct n; cbn.
  - apply FST_sing_el.
  - apply FST_adj; auto. apply DI1. apply FST_refl'. auto.
Qed.

Lemma enc_stack_spec R s t :
  s/t el R -> FSTeq ⊢ opair (enc_string s) (enc_string t) ∈ enc_stack R.
Proof.
  induction R as [|[u v] R IH]; cbn; auto.
  intros [[=]| H]; subst.
  - apply FST_adj; auto. apply DI1. apply FST_refl'. auto.
  - apply FST_adj; auto.
Qed.

Lemma FST_derivations_bound T B k n x :
  FSTeq <<= T -> T ⊢ opair k x ∈ enc_derivations B n -> T ⊢ k ∈ σ (tnumeral n).
Proof.
  induction n in T |- *; cbn; intros HT H.
  - apply FST_sing_iff in H; trivial. eapply FST_eq_elem; trivial.
    apply FST_sym'; trivial. eapply opair_inj1; trivial. apply H.
    apply FST_refl'; trivial. eapply FST_adj; trivial.
    apply DI1. apply FST_refl'; trivial.
  - apply FST_adj in H; trivial. apply (DE H).
    + apply FST_adj; auto. apply DI1. eapply opair_inj1; auto. 
    + apply FST_adj; auto.
Qed.

Lemma enc_derivations_functional B n x y y' :
  FSTeq ⊢ opair x y ∈ enc_derivations B n → opair x y' ∈ enc_derivations B n → y ≡ y'.
Proof.
  induction n; cbn -[derivations].
  - repeat apply II. eapply opair_inj2. auto. eapply FST_trans'. auto.
    + apply FST_sing_iff; auto.
    + apply FST_sym'. auto. apply FST_sing_iff; auto.
  - apply II. assert1 H1. apply FST_adj in H1; auto. apply (DE H1).
    all: apply II; assert1 H2; apply FST_adj in H2; auto; apply (DE H2).
    + eapply opair_inj2. auto. eapply FST_trans'; auto.
      apply FST_sym'; auto.
    + apply Exp. eapply IE. apply (@FST_numeral_wf _ (S n)). auto.
      eapply FST_derivations_bound. auto. eapply FST_eq_elem. auto.
      2: apply FST_refl'; auto. 2: auto. apply FST_eq_opair; auto.
      eapply opair_inj1; auto. apply FST_refl'. auto.
    + apply Exp. eapply IE. apply (@FST_numeral_wf _ (S n)). auto.
      eapply FST_derivations_bound. auto. eapply FST_eq_elem. auto.
      2: apply FST_refl'; auto. 2: auto. apply FST_eq_opair; auto.
      eapply opair_inj1; auto. apply FST_refl'. auto.
    + repeat rewrite imps in IHn. apply (Weak IHn). auto 8.
Qed.

Lemma prep_string_subst sigma s x :
  (prep_string s x)`[sigma] = prep_string s x`[sigma].
Proof.
  induction s; cbn; trivial. rewrite IHs. destruct a; reflexivity.
Qed.

Lemma enc_stack_subst sigma B :
  (enc_stack B)`[sigma] = enc_stack B.
Proof.
  induction B as [|[s t] B IH]; cbn; trivial.
  rewrite IH. unfold enc_string. now rewrite !prep_string_subst.
Qed.

Lemma is_rep_subst s t x y sigma :
  (is_rep (comb_rel s t) x y)[sigma] = is_rep (comb_rel s t) x`[sigma] y`[sigma].
Proof.
  unfold is_rep. cbn -[comb_rel]. subsimpl. repeat f_equal.
  - unfold comb_rel. cbn. rewrite !prep_string_subst. reflexivity.
  - unfold comb_rel. cbn. rewrite !prep_string_subst. reflexivity.
Qed.

Lemma combinations_subst B x y sigma :
  (combinations B x y)[sigma] = combinations B x`[sigma] y`[sigma].
Proof.
  induction B as [|[s t] B IH] in sigma, x, y |- *.
  - cbn. reflexivity.
  - cbn -[is_rep]. rewrite IH, is_rep_subst. cbn -[is_rep]. now subsimpl.
Qed.

Lemma enc_derivations_eq T B n x :
  FSTeq <<= T -> T ⊢ opair (tnumeral n) x ∈ enc_derivations B n -> T ⊢ x ≡ enc_stack (derivations B n).
Proof.
  intros HT H. destruct n; cbn in *.
  - eapply opair_inj2; trivial. eapply FST_sing_iff; eauto.
  - apply FST_adj in H; trivial. apply (DE H).
    + eapply opair_inj2. auto. auto.
    + apply Exp. eapply IE. apply (FST_numeral_wf (S n)). auto.
      eapply FST_derivations_bound. auto. auto.
Qed.

Lemma prep_string_app s t x :
  prep_string (s ++ t) x = prep_string s (prep_string t x).
Proof.
  induction s; cbn; congruence.
Qed.

Lemma FST_eq_prep T s x y :
  FSTeq <<= T -> T ⊢ x ≡ y -> T ⊢ prep_string s x ≡ prep_string s y.
Proof.
  intros HT H. induction s; cbn; try tauto.
  apply FST_eq_opair; trivial. now apply FST_refl'.
Qed.

Lemma append_all_el T B s t x y :
  FSTeq <<= T -> T ⊢ opair x y ∈ enc_stack B
  -> T ⊢ opair (prep_string s x) (prep_string t y) ∈ enc_stack (append_all B (s/t)).
Proof.
  intros HT H. induction B as [|[u v] B IH] in T, HT, H |- *; cbn in *.
  - apply Exp. eapply IE. 2: apply H. now apply FST_eset'.
  - eapply FST_adj; trivial. apply FST_adj in H; trivial. eapply (DE H).
    + assert1 H'. apply FST_sing_iff in H'; try now auto. apply DI1. auto.
      rewrite !prep_string_app. apply FST_eq_opair. auto.
      * apply FST_eq_prep. auto. eapply opair_inj1; eauto.
      * apply FST_eq_prep. auto. eapply opair_inj2; eauto.
    + apply DI2. apply IH; auto.
Qed.

Local Arguments comb_rel : simpl never.

Lemma is_rep_eq T B s t x y :
  FSTeq <<= T -> T ⊢ x ≡ enc_stack B -> T ⊢ is_rep (comb_rel s t) x y
  -> T ⊢ y ≡ enc_stack (append_all B (s / t)).
Proof.
  intros HT H1 H2. apply FST_ext'; trivial.
  - prv_all a.
    apply (AllE a) in H2. cbn in H2. subsimpl_in H2.
    eapply CE1 in H2. rewrite imps in *.
    use_exists H2 z. assert1 H. apply CE in H as [H H'].
    unfold comb_rel at 2 in H'. cbn in H'. subsimpl_in H'.
    rewrite !prep_string_subst in H'. cbn in H'. 
    use_exists H' c. clear H'.
    cbn. subsimpl. rewrite !prep_string_subst. cbn.
    assert1 H'. use_exists H' d. clear H'.
    cbn. subsimpl. rewrite !prep_string_subst. cbn. subsimpl.
    eapply FST_eq_elem. auto. apply FST_sym'. auto.
    eapply CE2. auto. apply FST_refl'. auto.
    apply append_all_el. auto.
    eapply FST_eq_elem. auto. eapply CE1. auto.
    eapply (Weak H1). auto. eapply (Weak H). auto.
  - prv_all a. apply (AllE a) in H2. cbn in H2. subsimpl_in H2.
    eapply CE2 in H2. apply II. eapply IE; try apply (Weak H2). auto.
    induction B as [|[u v] B IH] in T, x, HT, H1 |- *; cbn in *.
    + apply Exp. eapply IE. apply FST_eset'. all: auto.
    + rewrite <- imps. apply II. assert1 HA. apply FST_adj in HA; auto. apply (DE HA).
      * apply ExI with (opair (enc_string u) (enc_string v)).
        cbn. subsimpl. apply CI.
        -- eapply FST_eq_elem. auto. apply FST_refl'. auto.
           apply FST_sym'. auto. apply (Weak H1). auto. apply FST_adj; auto.
           apply DI1. apply FST_refl'. auto.
        -- cbn. apply ExI with (enc_string v).
           cbn. apply ExI with (enc_string u).
           cbn. subsimpl. rewrite !prep_string_subst, !prep_string_app; cbn.
           subsimpl. apply CI; auto. apply FST_refl'. auto.
      * specialize (IH T (enc_stack B) HT).
        assert (H : T ⊢ enc_stack B ≡ enc_stack B) by now apply FST_refl'.
        apply IH in H. apply imps. apply II. eapply Weak. use_exists H z. clear H. 2: auto.
        apply ExI with z. cbn. subsimpl. assert1 H. apply CE in H as [H H'].
        apply CI; trivial. eapply FST_eq_elem. auto.
        apply FST_refl'. auto. apply FST_sym'. auto.
        apply (Weak H1). auto. apply FST_adj; auto.
      
Qed.

Local Arguments is_rep : simpl never.

Lemma FST_enc_stack_app T A B :
  FSTeq <<= T -> T ⊢ is_bunion (enc_stack A) (enc_stack B) (enc_stack (A ++ B)).
Proof.
  intros HT. induction A as [|[s t] A IH]; cbn.
  - apply CI. apply CI.
    + prv_all x. apply II, Exp. apply imps. apply FST_eset'. auto.
    + prv_all x. apply II, Ctx. auto.
    + prv_all x. apply II, DI2, Ctx. auto.
  - apply CI. apply CI.
    + prv_all x. apply II. assert1 H. apply FST_adj in H; auto.
      apply FST_adj; auto. apply (DE H); clear H.
      * apply DI1. auto.
      * apply DI2. repeat apply CE1 in IH. apply (AllE x) in IH. cbn in IH.
        subsimpl_in IH. eapply IE. apply (Weak IH). auto. auto.
    + prv_all x. apply II. apply FST_adj; auto. apply DI2.
      apply CE1, CE2 in IH. apply (AllE x) in IH. cbn in IH.
      subsimpl_in IH. eapply IE. apply (Weak IH). auto. auto.
    + prv_all x. apply II. assert1 H. apply FST_adj in H; auto. apply (DE H); clear H.
      * apply DI1. apply FST_adj; auto.
      * apply CE2 in IH. apply (AllE x) in IH. cbn in IH. subsimpl_in IH.
        eapply DE. eapply IE. apply (Weak IH); auto. auto. 2: auto.
        apply DI1. apply FST_adj; auto.
Qed.

Lemma FST_bunion_sub T a b c c' :
  FSTeq <<= T -> T ⊢ is_bunion a b c -> T ⊢ is_bunion a b c' -> T ⊢ c ⊆ c'.
Proof.
  intros HT H1 H2. prv_all x. apply II.
  apply CE2 in H1. apply (AllE x) in H1. cbn in H1. subsimpl_in H1.
  rewrite imps in H1. apply (DE H1).
  - apply CE1, CE1 in H2. apply (AllE x) in H2. cbn in H2. subsimpl_in H2.
    eapply IE. apply (Weak H2); auto. auto.
  - apply CE1, CE2 in H2. apply (AllE x) in H2. cbn in H2. subsimpl_in H2.
    eapply IE. apply (Weak H2); auto. auto.
Qed.

Lemma FST_bunion_unique T a b c c' :
  FSTeq <<= T -> T ⊢ is_bunion a b c -> T ⊢ is_bunion a b c' -> T ⊢ c ≡ c'.
Proof.
  intros HT H1 H2. apply FST_ext'; trivial.
  - apply (FST_bunion_sub HT H1 H2).
  - apply (FST_bunion_sub HT H2 H1).
Qed.

Lemma FST_bunion_eq T a a' b b' c :
  FSTeq <<= T -> T ⊢ a ≡ a' -> T ⊢ b ≡ b' -> T ⊢ is_bunion a b c -> T ⊢ is_bunion a' b' c.
Proof.
  intros HT HA HB HC. apply CI. apply CI.
  - prv_all x. apply II. apply CE1, CE1 in HC. apply (AllE x) in HC. cbn in HC. subsimpl_in HC.
    eapply IE. apply (Weak HC); auto. eapply FST_eq_elem; auto. apply FST_refl'; auto.
    apply FST_sym'; auto. apply (Weak HA). auto.
  - prv_all x. apply II. apply CE1, CE2 in HC. apply (AllE x) in HC. cbn in HC. subsimpl_in HC.
    eapply IE. apply (Weak HC); auto. eapply FST_eq_elem; auto. apply FST_refl'; auto.
    apply FST_sym'; auto. apply (Weak HB). auto.
  - prv_all x. apply II. apply CE2 in HC. apply (AllE x) in HC. cbn in HC. subsimpl_in HC.
    rewrite imps in HC. apply (DE HC).
    + apply DI1. eapply FST_eq_elem; auto. apply FST_refl'; auto.  apply (Weak HA). auto.
    + apply DI2. eapply FST_eq_elem; auto. apply FST_refl'; auto.  apply (Weak HB). auto.
Qed.

Lemma combinations_eq T B C x y :
  FSTeq <<= T -> T ⊢ x ≡ enc_stack C -> T ⊢ combinations B x y -> T ⊢ y ≡ enc_stack (derivation_step B C).
Proof.
  induction B as [|[s t] B IH] in y, T |-*; cbn -[is_bunion]; intros HT H1 H2; trivial.
  use_exists H2 u. assert1 H. use_exists H v. clear H.
  rewrite !combinations_subst, !is_rep_subst. cbn. subsimpl.
  eapply FST_bunion_unique; auto; try apply FST_enc_stack_app; auto.
  eapply FST_bunion_eq; auto.
  - eapply is_rep_eq; auto. apply (Weak H1); auto. eapply CE2. auto.
  - apply IH; auto. apply (Weak H1); auto. eapply CE2. eapply CE1. auto.
  - assert1 H. apply CE1, CE1 in H. apply H.
Qed.

Lemma combinations_step B n (i x y : term) :
  FSTeq ⊢ i ∈ tnumeral n → opair i x ∈ enc_derivations B n
     → combinations B x y → opair (σ i) y ∈ enc_derivations B n.
Proof.
  induction n; cbn.
  - apply II. apply Exp.
    apply imps. apply FST_eset.
  - apply II. assert1 H1. apply FST_adj in H1; auto. apply (DE H1).
    all: apply II; assert1 H2; apply FST_adj in H2; auto; apply (DE H2).
    + apply Exp. eapply IE. apply (FST_numeral_wf n). auto.
      eapply FST_eq_elem. auto. apply FST_refl'. auto.
      eapply FST_trans'. auto. apply FST_sym'. auto.
      eapply opair_inj1. auto. auto. auto.
      apply FST_sig_el. auto.
    + apply II. apply FST_adj. auto 8.
      apply DI1. apply FST_eq_opair. auto 8.
      * apply FST_eq_sig; auto 8.
      * eapply combinations_eq; auto 8.
        apply enc_derivations_eq. auto 8.
        eapply FST_eq_elem; auto 8; try apply FST_refl'; auto 8.
        eapply FST_eq_opair; auto 8; try apply FST_refl'. auto 8.
    + apply Exp. eapply IE. apply (FST_numeral_wf (S n)). auto.
      eapply FST_eq_elem. auto. eapply opair_inj1. auto. auto.
      apply FST_refl'. auto. cbn. apply FST_adj. auto.
      apply DI2. auto.   
    + apply II. apply FST_adj. auto 8.
      apply DI2. eapply IE. eapply IE. eapply IE.
      * eapply Weak. apply IHn. auto 8.
      * auto.
      * auto.
      * auto.
Qed.

Theorem dPCP_FSTD B :
  dPCPb B -> FSTeq ⊢ solvable B.
Proof.
  intros [s H]. destruct (derivable_derivations H) as [n Hn].
  unfold solvable.
  apply ExI with (tnumeral n). cbn.
  apply ExI with (enc_derivations B n). cbn.
  apply ExI with (enc_string s). cbn. subsimpl.
  apply ExI with (enc_stack (derivations B n)). cbn.
  rewrite !enc_stack_subst, !combinations_subst. cbn. subsimpl.
  repeat apply CI.
  - specialize (@FST_numeral FSTeq n (fun phi H => H)). apply CE1.
  - specialize (@FST_numeral FSTeq n (fun phi H => H)). apply CE2.
  - prv_all x. prv_all y. prv_all z.
    apply enc_derivations_functional.
  - apply enc_derivations_base.
  - prv_all x. prv_all y. prv_all z. rewrite !combinations_subst.
    cbn. subsimpl. apply combinations_step.
  - apply enc_derivations_step.
  - now apply enc_stack_spec.
Qed.

Theorem PCP_FSTD B :
  PCPb B -> FSTeq ⊢ solvable B.
Proof.
  rewrite PCPb_iff_dPCPb. apply dPCP_FSTD.
Qed.

End FST.




