(** ** Reduction from PCP to deductive entailment in finite ZF *)

Require Import Undecidability.FOL.Util.Syntax.
Require Import Undecidability.FOL.Util.FullTarski.
Require Import Undecidability.FOL.Util.FullDeduction_facts.
Require Import Undecidability.FOL.ZF.
Require Import Undecidability.FOL.Reductions.PCPb_to_HF.

From Undecidability.PCP Require Import PCP Util.PCP_facts Reductions.PCPb_iff_dPCPb.

From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Local Definition BSRS := list(card bool).
Local Notation "x / y" := (x, y).

Local Hint Constructors prv : core.


(* ** Simple derivations in HF *)

Section HF.

Context { p : peirce }.

Close Scope sem.

Lemma HF_eset x :
  HFeq ⊢ ¬ (x ∈ ∅).
Proof.
  change (HFeq ⊢ (¬ ($0 ∈ ∅))[x..]).
  apply AllE. apply Ctx. firstorder.
Qed.

Lemma HF_eset' T x :
  HFeq <<= T -> T ⊢ ¬ (x ∈ ∅).
Proof.
  intros H. now apply (Weak (HF_eset x)).
Qed.

Fixpoint tnumeral n :=
  match n with 
  | O => ∅
  | S n => σ (tnumeral n)
end.

Lemma HF_refl' T x :
  HFeq <<= T -> T ⊢ x ≡ x.
Proof.
  intros H. change (T ⊢ ($0 ≡ $0)[x..]).
  apply AllE. apply Ctx. firstorder.
Qed.

Lemma HF_refl x :
  HFeq ⊢ x ≡ x.
Proof.
  now apply HF_refl'.
Qed.

Lemma HF_sym' T x y :
  HFeq <<= T -> T ⊢ x ≡ y -> T ⊢ y ≡ x.
Proof.
  intros H1 H2. eapply IE; try apply H2.
  assert (H : T ⊢ ax_sym) by (apply Ctx; firstorder).
  apply (AllE x), (AllE y) in H; cbn in H. now subsimpl_in H.
Qed.

Lemma HF_trans' T x y z :
  HFeq <<= T -> T ⊢ x ≡ y -> T ⊢ y ≡ z -> T ⊢ x ≡ z.
Proof.
  intros H1 H2 H3. eapply IE; try apply H3.
  eapply IE; try apply H2.
  assert (H : T ⊢ ax_trans) by (apply Ctx; firstorder).
  now apply (AllE x), (AllE y), (AllE z) in H; cbn in H; subsimpl_in H.
Qed.

Lemma HF_eq_elem T x y x' y' :
  HFeq <<= T -> T ⊢ x ≡ x' -> T ⊢ y ≡ y' -> T ⊢ x ∈ y -> T ⊢ x' ∈ y'.
Proof.
  intros H1 H2 H3 H4. eapply IE; try apply H4.
  eapply IE; try apply H3. eapply IE; try apply H2.
  assert (H : T ⊢ ax_eq_elem) by (apply Ctx; firstorder).
  now apply (AllE x), (AllE y), (AllE x'), (AllE y') in H; cbn in H; subsimpl_in H.
Qed.

Lemma HF_ext' T x y :
  HFeq <<= T -> T ⊢ sub x y -> T ⊢ sub y x -> T ⊢ x ≡ y.
Proof.
  intros H1 H2 H3. eapply IE; try apply H3.
  eapply IE; try apply H2.
  assert (H : T ⊢ ax_ext) by (apply Ctx; firstorder).
  apply (AllE x), (AllE y) in H; cbn in H.
  subsimpl_in H. apply H.
Qed.

Lemma HF_pair_el' T x y z :
  HFeq <<= T -> T ⊢ (z ≡ x ∨ z ≡ y) <-> T ⊢ z ∈ {x; y}.
Proof.
  intros HT; split; intros H; eapply IE; try apply H.
  all: assert (HP : T ⊢ ax_pair) by (apply Ctx; firstorder).
  all: apply (AllE y), (AllE x), (AllE z) in HP; cbn in HP; subsimpl_in HP.
  - eapply CE2, HP.
  - eapply CE1, HP.
Qed.

Lemma HF_pair_el x y z :
  HFeq ⊢ (z ≡ x ∨ z ≡ y) -> HFeq ⊢ z ∈ {x; y}.
Proof.
  now apply HF_pair_el'.
Qed.

Lemma HF_sub_pair T x y x' y' :
  HFeq <<= T -> T ⊢ x ≡ x' -> T ⊢ y ≡ y' -> T ⊢ {x; y} ⊆ {x'; y'}.
Proof.
  intros HT H1 H2. prv_all z.
  apply II. apply HF_pair_el'; auto. eapply DE.
  - apply HF_pair_el'; auto.
  - apply DI1. eapply HF_trans'; auto. eapply Weak; eauto.
  - apply DI2. eapply HF_trans'; auto. eapply Weak; eauto.
Qed.

Lemma HF_eq_pair T x y x' y' :
  HFeq <<= T -> T ⊢ x ≡ x' -> T ⊢ y ≡ y' -> T ⊢ {x; y} ≡ {x'; y'}.
Proof.
  intros HT H1 H2. apply HF_ext'; trivial.
  - now apply HF_sub_pair.
  - apply HF_sub_pair; trivial. all: now apply HF_sym'.
Qed.

Lemma HF_eq_opair T x y x' y' :
  HFeq <<= T -> T ⊢ x ≡ x' -> T ⊢ y ≡ y' -> T ⊢ opair x y ≡ opair x' y'.
Proof.
  intros HT H1 H2. repeat apply HF_eq_pair; trivial.
Qed.

Definition sing x :=
  {x; x}.

Lemma HF_sing_el x :
  HFeq ⊢ x ∈ sing x.
Proof.
  apply HF_pair_el. apply DI1. apply HF_refl.
Qed.

Lemma HF_sing_iff T x y :
  HFeq <<= T -> T ⊢ x ∈ sing y <-> T ⊢ x ≡ y.
Proof.
  intros HT. unfold sing.
  rewrite <- HF_pair_el'; trivial.
  split; intros H.
  - apply (DE H); auto.
  - now apply DI1.
Qed.

Lemma HF_union_el' T x y z :
  HFeq <<= T -> T ⊢ y ∈ x ∧ z ∈ y -> T ⊢ z ∈ ⋃ x.
Proof.
  intros HT H.
  assert (HU : T ⊢ ax_union) by (apply Ctx; firstorder).
  apply (AllE x), (AllE z) in HU; cbn in HU. subsimpl_in HU.
  apply CE2 in HU. eapply IE; try apply HU.
  apply ExI with y. cbn. subsimpl. apply H.
Qed.

Lemma HF_union_el x y z :
  HFeq ⊢ y ∈ x ∧ z ∈ y -> HFeq ⊢ z ∈ ⋃ x.
Proof.
  now apply HF_union_el'.
Qed.

Lemma HF_sub_union T x y :
  HFeq <<= T -> T ⊢ x ≡ y -> T ⊢ sub (⋃ x) (⋃ y).
Proof.
  intros HT H. prv_all z.
  apply II. assert1 H'.
  assert (HU : (z ∈ ⋃ x :: T) ⊢ ax_union) by (apply Ctx; firstorder).
  apply (AllE x), (AllE z) in HU; cbn in HU; subsimpl_in HU.
  apply CE1 in HU. eapply (IE HU) in H'.
  use_exists H' u. clear H' HU.
  eapply HF_union_el'; auto. apply CI.
  - eapply HF_eq_elem. auto. apply HF_refl'; auto.
    apply (Weak H); auto. eapply CE1; auto.
  - eapply CE2; auto.
Qed.

Lemma HF_eq_union T x y :
  HFeq <<= T -> T ⊢ x ≡ y -> T ⊢ ⋃ x ≡ ⋃ y.
Proof.
  intros HT H. apply HF_ext'; try apply HF_sub_union; trivial.
  now apply HF_sym'.
Qed.

Lemma HF_bunion_el' T x y z :
  HFeq <<= T -> T ⊢ (z ∈ x ∨ z ∈ y) -> T ⊢ z ∈ x ∪ y.
Proof.
  intros HT H. apply (DE H).
  - eapply HF_union_el' with x. auto. apply CI; auto.
    apply HF_pair_el'. auto. apply DI1. apply HF_refl'. auto.
  - eapply HF_union_el' with y. auto. apply CI; auto.
    apply HF_pair_el'. auto. apply DI2. apply HF_refl'. auto.
Qed.

Lemma HF_bunion_el x y z :
  HFeq ⊢ (z ∈ x ∨ z ∈ y) -> HFeq ⊢ z ∈ x ∪ y.
Proof.
  now apply HF_bunion_el'.
Qed.

Lemma HF_bunion_inv' x y z :
   HFeq ⊢ z ∈ x ∪ y ~> z ∈ x ∨ z ∈ y.
Proof.
  assert (TU : HFeq ⊢ ax_union) by (apply Ctx; firstorder). unfold ax_union in TU.
  eapply (AllE ({x; y})), (AllE z), CE1 in TU; cbn in TU; subsimpl_in TU.
  rewrite imps in *. use_exists TU u.
  eapply DE. apply HF_pair_el'; auto.
  - eapply CE1. auto.
  - apply DI1. eapply HF_eq_elem; auto.
    + apply HF_refl'. auto.
    + eapply CE2. auto.
  - apply DI2. eapply HF_eq_elem; auto.
    + apply HF_refl'. auto.
    + eapply CE2. auto.
Qed.

Lemma HF_bunion_inv T x y z :
   HFeq <<= T -> T ⊢ z ∈ x ∪ y -> T ⊢ z ∈ x ∨ z ∈ y.
Proof.
  intros HT H. eapply IE; try apply H.
  eapply Weak; try apply HT. apply HF_bunion_inv'.
Qed.

Lemma HF_eq_bunion T x y x' y' :
  HFeq <<= T -> T ⊢ x ≡ x' -> T ⊢ y ≡ y' -> T ⊢ x ∪ y ≡ x' ∪ y'.
Proof.
  intros HT H1 H2. now apply HF_eq_union, HF_eq_pair.
Qed.

Lemma HF_sig_el T x :
   HFeq <<= T -> T ⊢ x ∈ σ x.
Proof.
  intros H. apply HF_bunion_el'; trivial.
  apply DI2. apply HF_sing_iff; trivial.
  apply HF_refl'. trivial.
Qed.

Lemma HF_eq_sig T x y :
  HFeq <<= T -> T ⊢ x ≡ y -> T ⊢ σ x ≡ σ y.
Proof.
  intros HT H. now apply HF_eq_bunion, HF_eq_pair.
Qed.

Lemma sing_pair1 T x y z :
  HFeq <<= T -> T ⊢ sing x ≡ {y; z} -> T ⊢ x ≡ y.
Proof.
  intros HT H. apply HF_sym'; trivial.
  apply HF_sing_iff; trivial. eapply HF_eq_elem; trivial.
  apply HF_refl'; trivial. apply HF_sym'; eauto.
  apply HF_pair_el'; trivial. apply DI1. now apply HF_refl'.
Qed.

Lemma sing_pair2 T x y z :
  HFeq <<= T -> T ⊢ sing x ≡ {y; z} -> T ⊢ x ≡ z.
Proof.
  intros HT H. apply HF_sym'; trivial.
  apply HF_sing_iff; trivial. eapply HF_eq_elem; trivial.
  apply HF_refl'; trivial. apply HF_sym'; eauto.
  apply HF_pair_el'; trivial. apply DI2. now apply HF_refl'.
Qed.

Lemma opair_inj1 T x y x' y' :
  HFeq <<= T -> T ⊢ opair x y ≡ opair x' y' -> T ⊢ x ≡ x'.
Proof.
  intros HT He. assert (H : T ⊢ {x; x} ∈ opair x y).
  { apply HF_pair_el'; trivial. apply DI1. now apply HF_refl'. }
  eapply HF_eq_elem in H; try apply He; try apply HF_refl'; trivial.
  apply HF_pair_el' in H; trivial.
  apply (DE H); eapply sing_pair1; try apply prv_T1; auto.
Qed.

Lemma opair_inj2 T x y x' y' :
  HFeq <<= T -> T ⊢ opair x y ≡ opair x' y' -> T ⊢ y ≡ y'.
Proof.
  intros HT H. assert (H' : T ⊢ y ≡ x' ∨ y ≡ y').
  - assert (H2 : T ⊢ {x; y} ∈ opair x' y').
    { eapply HF_eq_elem; trivial. apply HF_refl'; trivial. apply H.
      apply HF_pair_el'; trivial. apply DI2. now apply HF_refl'. }
    apply HF_pair_el' in H2; trivial. apply (DE H2).
    + apply DI1. apply HF_sym'; auto. eapply sing_pair2; auto. apply HF_sym'; auto.
    + apply HF_pair_el'; auto. eapply HF_eq_elem; auto.
      * apply HF_refl'; auto.
      * apply HF_pair_el'; auto. apply DI2. apply HF_refl'. auto.
  - apply (DE H'); try apply prv_T1.
    assert (H1 : T ⊢ x ≡ x') by apply (opair_inj1 HT H).
    assert (H2 : T ⊢ {x'; y'} ∈ opair x y).
    { eapply HF_eq_elem; trivial. apply HF_refl'; trivial. apply HF_sym', H; trivial.
      apply HF_pair_el'; trivial. apply DI2. now apply HF_refl'. }
    apply HF_pair_el' in H2; trivial.
    eapply DE; try eapply (Weak H2); auto.
    + eapply HF_trans'; auto. eapply HF_trans'; auto.
      * apply HF_sym'. auto. apply (Weak H1). auto.
      * eapply sing_pair2; auto. apply HF_sym'; auto.
    + eapply HF_trans'; auto. eapply sing_pair2; auto. eapply HF_trans'; auto.
      2: apply HF_sym'; auto.
      eapply HF_eq_pair; try apply HF_sym'; auto.
      apply (Weak H1). auto.
    + auto.
Qed.

Lemma HF_bunion_el1 T x y z :
  HFeq <<= T -> T ⊢ z ∈ x -> T ⊢ z ∈ x ∪ y.
Proof.
  intros HT H. now apply HF_bunion_el', DI1.
Qed.

Lemma HF_bunion_el2 T x y z :
  HFeq <<= T -> T ⊢ z ∈ y -> T ⊢ z ∈ x ∪ y.
Proof.
  intros HT H. now apply HF_bunion_el', DI2.
Qed.
 
Lemma bunion_eset x :
   HFeq ⊢ ∅ ∪ x ≡ x.
Proof.
  apply HF_ext'; auto; prv_all y; apply II.
  - eapply DE. eapply HF_bunion_inv; auto. 
    + apply Exp. eapply IE.
      eapply Weak; try apply HF_eset. all: auto.
    + auto.
  - apply HF_bunion_el2; auto.
Qed.

Lemma bunion_swap x y z :
  HFeq ⊢ (x ∪ y) ∪ z ≡ (x ∪ z) ∪ y.
Proof.
  apply HF_ext'; auto; prv_all u; apply II.
  - eapply DE. eapply HF_bunion_inv; auto.
    + eapply DE. eapply HF_bunion_inv; auto.
      * apply HF_bunion_el1, HF_bunion_el1. all: auto.
      * apply HF_bunion_el2; auto.
    + apply HF_bunion_el1, HF_bunion_el2. all: auto.
  - eapply DE. eapply HF_bunion_inv; auto.
    + eapply DE. eapply HF_bunion_inv; auto.
      * apply HF_bunion_el1, HF_bunion_el1. all: auto.
      * apply HF_bunion_el2; auto.
    + apply HF_bunion_el1, HF_bunion_el2. all: auto.
Qed.

Lemma bunion_use T x y z phi :
  HFeq <<= T -> (x ∈ y :: T) ⊢ phi -> (x ≡ z :: T) ⊢ phi -> T ⊢ x ∈ y ∪ sing z ~> phi.
Proof.
  intros HT H1 H2. apply II. eapply DE.
  - eapply HF_bunion_inv; auto.
  - apply (Weak H1). auto.
  - eapply IE.
    + eapply Weak. apply II, H2. auto.
    + apply HF_sing_iff; auto.
Qed.

Lemma HF_numeral_trans T n x y :
  HFeq <<= T -> T ⊢ x ∈ tnumeral n ~> y ∈ x ~> y ∈ tnumeral n.
Proof.
  intros HT. induction n; cbn.
  - apply II, Exp. eapply IE. apply HF_eset'. all: auto.
  - apply bunion_use; trivial.
    + rewrite !imps. rewrite !imps in IHn. apply HF_bunion_el1; auto.
    + apply II. apply HF_bunion_el'. auto.
      apply DI1. eapply HF_eq_elem; auto.
      apply HF_refl'. auto.
Qed.

Lemma HF_numeral_wf T n :
  HFeq <<= T -> T ⊢ ¬ (tnumeral n ∈ tnumeral n).
Proof.
  intros HT. induction n; cbn.
  - now apply HF_eset'.
  - apply bunion_use; trivial.
    + eapply IE. apply (Weak IHn). auto.
      eapply IE. eapply IE. apply HF_numeral_trans; auto.
      auto. apply HF_sig_el. auto.
    + eapply IE. apply (Weak IHn). auto.
      eapply HF_eq_elem. auto. apply HF_refl'. auto.
      auto. apply HF_sig_el. auto.
Qed.

Lemma HF_sig_iff T x y :
  HFeq <<= T -> T ⊢ y ∈ σ x -> T ⊢ y ∈ x ∨ y ≡ x.
Proof.
  intros HT H % HF_bunion_inv; auto.
  eapply DE; try apply H; auto.
  apply DI2. eapply DE; try apply HF_pair_el'; auto.
Qed.

Lemma HF_numeral T n :
  HFeq <<= T -> T ⊢ htransitive (tnumeral n).
Proof.
  intros HT. induction n; apply CI; prv_all x; apply II.
  - apply Exp. apply imps. apply HF_eset'. auto.
  - apply Exp. apply imps. apply HF_eset'. auto.
  - prv_all y. apply -> imps. try apply (@HF_numeral_trans T (S n)); auto.
  - eapply DE; try apply HF_sig_iff; auto.
    + apply CE2 in IHn. apply (AllE x) in IHn. apply imps.
      cbn in IHn. subsimpl_in IHn. eapply Weak; eauto.
    + prv_all y. apply II. prv_all z. apply II. eapply HF_eq_elem.
      * auto. 
      * apply HF_refl'. auto.
      * apply HF_sym'; auto.
      * apply imps. eapply IE; try apply HF_numeral_trans; auto.
        eapply HF_eq_elem; auto. apply HF_refl'. auto.
Qed.



(* ** Preservation proof *)

Fixpoint enc_derivations B n :=
  match n with 
  | O => sing (opair ∅ (enc_stack B))
  | S n => enc_derivations B n ∪ sing (opair (tnumeral (S n)) (enc_stack (derivations B (S n))))
  end.

Lemma enc_derivations_base R n :
  HFeq ⊢ {{∅; ∅}; {∅; enc_stack R}} ∈ enc_derivations R n.
Proof.
  induction n; cbn.
  - apply HF_sing_el.
  - apply HF_bunion_el. now apply DI1.
Qed.

Lemma enc_derivations_step B n :
  HFeq ⊢ opair (tnumeral n) (enc_stack (derivations B n)) ∈ enc_derivations B n.
Proof.
  destruct n; cbn.
  - apply HF_sing_el.
  - apply HF_bunion_el. apply DI2. apply HF_sing_el.
Qed.

Lemma enc_stack_spec R s t :
  s/t el R -> HFeq ⊢ opair (enc_string s) (enc_string t) ∈ enc_stack R.
Proof.
  induction R as [|[u v] R IH]; cbn; auto.
  intros [[=]| H]; subst.
  - apply HF_bunion_el. apply DI2. apply HF_sing_el.
  - apply HF_bunion_el. apply DI1. now apply IH.
Qed.

Lemma HF_derivations_bound T B k n x :
  HFeq <<= T -> T ⊢ opair k x ∈ enc_derivations B n -> T ⊢ k ∈ σ (tnumeral n).
Proof.
  induction n in T |- *; cbn; intros HT H.
  - apply HF_sing_iff in H; trivial. eapply HF_eq_elem; trivial.
    apply HF_sym'; trivial. eapply opair_inj1; trivial. apply H.
    apply HF_refl'; trivial. eapply HF_bunion_el'; trivial.
    apply DI2. apply HF_sing_iff; trivial. apply HF_refl'; trivial.
  - apply HF_bunion_inv in H; trivial. apply (DE H).
    + apply HF_bunion_el1. auto. apply IHn; auto.
    + apply HF_bunion_el2. auto. apply HF_sing_iff. auto.
      eapply opair_inj1. auto. apply HF_sing_iff; auto.
Qed.

Lemma enc_derivations_functional B n x y y' :
  HFeq ⊢ opair x y ∈ enc_derivations B n ~> opair x y' ∈ enc_derivations B n ~> y ≡ y'.
Proof.
  induction n; cbn -[derivations].
  - repeat apply II. eapply opair_inj2. auto. eapply HF_trans'. auto.
    + apply HF_sing_iff; auto.
    + apply HF_sym'. auto. apply HF_sing_iff; auto.
  - apply bunion_use; try apply bunion_use. 1,2,5: auto.
    + repeat rewrite <- imps. now apply (Weak IHn).
    + apply Exp. eapply IE. apply (@HF_numeral_wf _ (S n)). auto.
      eapply HF_derivations_bound. auto. eapply HF_eq_elem. auto.
      2: apply HF_refl'; auto. 2: auto. apply HF_eq_opair; auto.
      eapply opair_inj1; auto. apply HF_refl'. auto.
    + apply Exp. eapply IE. apply (@HF_numeral_wf _ (S n)). auto.
      eapply HF_derivations_bound. auto. eapply HF_eq_elem. auto.
      2: apply HF_refl'; auto. 2: auto. apply HF_eq_opair; auto.
      eapply opair_inj1; auto. apply HF_refl'. auto.
    + eapply opair_inj2. auto. eapply HF_trans'; auto.
      apply HF_sym'; auto.
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
  HFeq <<= T -> T ⊢ opair (tnumeral n) x ∈ enc_derivations B n -> T ⊢ x ≡ enc_stack (derivations B n).
Proof.
  intros HT H. destruct n; cbn in *.
  - eapply opair_inj2; trivial. eapply HF_sing_iff; eauto.
  - apply HF_bunion_inv in H; trivial. apply (DE H).
    + apply Exp. eapply IE. apply (HF_numeral_wf (S n)). auto.
      eapply HF_derivations_bound. auto. auto.
    + eapply opair_inj2. auto. apply HF_sing_iff. auto. auto.
Qed.

Lemma enc_stack_app T B C :
  HFeq <<= T -> T ⊢ (enc_stack B) ∪ (enc_stack C) ≡ enc_stack (B ++ C).
Proof.
  intros HT. induction B as [|[s t] B IH]; cbn.
  - eapply Weak; try apply bunion_eset. assumption.
  - eapply HF_trans'; trivial. eapply Weak; try apply bunion_swap; trivial.
    eapply HF_eq_bunion; trivial. apply HF_refl'; trivial.
Qed.

Lemma prep_string_app s t x :
  prep_string (s ++ t) x = prep_string s (prep_string t x).
Proof.
  induction s; cbn; congruence.
Qed.

Lemma HF_eq_prep T s x y :
  HFeq <<= T -> T ⊢ x ≡ y -> T ⊢ prep_string s x ≡ prep_string s y.
Proof.
  intros HT H. induction s; cbn; try tauto.
  apply HF_eq_opair; trivial. now apply HF_refl'.
Qed.

Lemma append_all_el T B s t x y :
  HFeq <<= T -> T ⊢ opair x y ∈ enc_stack B
  -> T ⊢ opair (prep_string s x) (prep_string t y) ∈ enc_stack (append_all B (s/t)).
Proof.
  intros HT H. induction B as [|[u v] B IH] in T, HT, H |- *; cbn in *.
  - apply Exp. eapply IE. 2: apply H. now apply HF_eset'.
  - eapply (HF_bunion_el' HT). eapply DE. apply (HF_bunion_inv HT H).
    + apply DI1. apply IH; auto.
    + assert1 H'. apply HF_sing_iff in H'; try now auto.
      apply DI2. apply HF_sing_iff. auto.
      rewrite !prep_string_app. apply HF_eq_opair. auto.
      * apply HF_eq_prep. auto. eapply opair_inj1; eauto.
      * apply HF_eq_prep. auto. eapply opair_inj2; eauto.
Qed.

Local Arguments comb_rel : simpl never.

Lemma is_rep_eq T B s t x y :
  HFeq <<= T -> T ⊢ x ≡ enc_stack B -> T ⊢ is_rep (comb_rel s t) x y
  -> T ⊢ y ≡ enc_stack (append_all B (s / t)).
Proof.
  intros HT H1 H2. apply HF_ext'; trivial.
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
    eapply HF_eq_elem. auto. apply HF_sym'. auto.
    eapply CE2. auto. apply HF_refl'. auto.
    apply append_all_el. auto.
    eapply HF_eq_elem. auto. eapply CE1. auto.
    eapply (Weak H1). auto. eapply (Weak H). auto.
  - prv_all a. apply (AllE a) in H2. cbn in H2. subsimpl_in H2.
    eapply CE2 in H2. apply II. eapply IE; try apply (Weak H2). auto.
    induction B as [|[u v] B IH] in T, x, HT, H1 |- *; cbn in *.
    + apply Exp. eapply IE. apply HF_eset'. all: auto.
    + rewrite <- imps. apply bunion_use; trivial.
      * specialize (IH T (enc_stack B) HT).
        assert (H : T ⊢ enc_stack B ≡ enc_stack B) by now apply HF_refl'.
        apply IH in H. use_exists H z. clear H. apply ExI with z.
        cbn. subsimpl. assert1 H. apply CE in H as [H H'].
        apply CI; trivial. eapply HF_eq_elem. auto.
        apply HF_refl'. auto. apply HF_sym'. auto.
        apply (Weak H1). auto. apply HF_bunion_el1; trivial. auto.
      * apply ExI with (opair (enc_string u) (enc_string v)).
        cbn. subsimpl. apply CI.
        -- eapply HF_eq_elem. auto. apply HF_refl'. auto.
           apply HF_sym'. auto. apply (Weak H1). auto.
           apply HF_bunion_el2. auto. eapply Weak. apply HF_sing_el. auto.
        -- cbn. apply ExI with (enc_string v).
           cbn. apply ExI with (enc_string u).
           cbn. subsimpl. rewrite !prep_string_subst, !prep_string_app; cbn.
           subsimpl. apply CI; auto. apply HF_refl'. auto.
Qed.

Local Arguments is_rep : simpl never.

Lemma combinations_eq T B C x y :
  HFeq <<= T -> T ⊢ x ≡ enc_stack C -> T ⊢ combinations B x y -> T ⊢ y ≡ enc_stack (derivation_step B C).
Proof.
  induction B as [|[s t] B IH] in y, T |-*; cbn; intros HT H1 H2; trivial.
  use_exists H2 u. assert1 H. use_exists H v. clear H.
  rewrite !combinations_subst, !is_rep_subst. cbn. subsimpl.
  eapply HF_trans'. auto. eapply CE1. eapply CE1. auto.
  eapply HF_trans'. auto. 2: apply enc_stack_app; auto.
  apply HF_eq_bunion; auto.
  - eapply is_rep_eq; auto. apply (Weak H1); auto.
    eapply CE2. auto.
  - apply IH; auto.
    + apply (Weak H1); auto.
    + eapply CE2. eapply CE1. auto.
Qed.

Lemma combinations_step B n (i x y : term) :
  HFeq ⊢ i ∈ tnumeral n ~> opair i x ∈ enc_derivations B n
     ~> combinations B x y ~> opair (σ i) y ∈ enc_derivations B n.
Proof.
  induction n; cbn.
  - apply II. apply Exp.
    apply imps. apply HF_eset.
  - apply bunion_use; try apply bunion_use; auto.
    + apply II. apply HF_bunion_el'. auto.
      apply DI1. eapply IE. eapply IE. eapply IE.
      * eapply Weak. apply IHn. auto.
      * auto.
      * auto.
      * auto.
    + apply Exp. eapply IE. apply (HF_numeral_wf (S n)). auto.
      eapply HF_eq_elem. auto. eapply opair_inj1. auto. auto.
      apply HF_refl'. auto. cbn. apply HF_bunion_el'. auto.
      apply DI1. auto.
    + apply II. apply HF_bunion_el'. auto.
      apply DI2. apply HF_sing_iff. auto.
      apply HF_eq_opair. auto.
      * apply HF_eq_sig; auto.
      * eapply combinations_eq; auto.
        apply enc_derivations_eq. auto.
        eapply HF_eq_elem; auto; try apply HF_refl'; auto.
        eapply HF_eq_opair; auto; try apply HF_refl'. auto.
    + apply Exp. eapply IE. apply (HF_numeral_wf n). auto.
      eapply HF_eq_elem. auto. apply HF_refl'. auto.
      eapply HF_trans'. auto. apply HF_sym'. auto.
      eapply opair_inj1. auto. auto. auto.
      apply HF_sig_el. auto.
Qed.

Theorem dPCP_HFD B :
  dPCPb B -> HFeq ⊢ solvable B.
Proof.
  intros [s H]. destruct (derivable_derivations H) as [n Hn].
  unfold solvable.
  apply ExI with (tnumeral n). cbn.
  apply ExI with (enc_derivations B n). cbn.
  apply ExI with (enc_string s). cbn. subsimpl.
  apply ExI with (enc_stack (derivations B n)). cbn.
  rewrite !enc_stack_subst, !combinations_subst. cbn. subsimpl.
  repeat apply CI.
  - specialize (@HF_numeral HFeq n (fun phi H => H)). apply CE1.
  - specialize (@HF_numeral HFeq n (fun phi H => H)). apply CE2.
  - prv_all x. prv_all y. prv_all z.
    apply enc_derivations_functional.
  - apply enc_derivations_base.
  - prv_all x. prv_all y. prv_all z. rewrite !combinations_subst.
    cbn. subsimpl. apply combinations_step.
  - apply enc_derivations_step.
  - now apply enc_stack_spec.
Qed.

Theorem PCP_HFD B :
  PCPb B -> HFeq ⊢ solvable B.
Proof.
  rewrite PCPb_iff_dPCPb. apply dPCP_HFD.
Qed.

End HF.




