(** * Reduction to deductive ZF entailment *)

Require Import Undecidability.FOL.Util.Syntax.
Require Import Undecidability.FOL.Util.FullTarski.
Require Import Undecidability.FOL.Util.FullDeduction.
Require Import Undecidability.FOL.ZF.
Require Import Undecidability.FOL.Reductions.PCPb_to_ZF.

From Undecidability.PCP Require Import PCP Util.PCP_facts Reductions.PCPb_iff_dPCPb.

From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.

Local Set Implicit Arguments.
Local Unset Strict Implicit.




(** ** Simple derivations in ZF *)

Close Scope sem.

Section ZF.

Context { p : peirce }.

Lemma ZF_eset x :
  ZFeq' ⊢ ¬ (x ∈ ∅).
Proof.
  change (ZFeq' ⊢ (¬ ($0 ∈ ∅))[x..]).
  apply AllE. apply Ctx. firstorder.
Qed.

Lemma ZF_eset' T x :
  ZFeq' <<= T -> T ⊢ ¬ (x ∈ ∅).
Proof.
  intros H. now apply (Weak (ZF_eset x)).
Qed.

Fixpoint tnumeral n :=
  match n with 
  | O => ∅
  | S n => σ (tnumeral n)
end.

Lemma ZF_numeral n :
  ZFeq' ⊢ tnumeral n ∈ ω.
Proof.
  induction n; cbn.
  - eapply CE1. apply Ctx. firstorder.
  - eapply IE; try apply IHn.
    change (ZFeq' ⊢ ($0 ∈ ω --> σ ($0) ∈ ω)[(tnumeral n)..]).
    apply AllE. eapply CE2. apply Ctx. firstorder.
Qed.

Lemma ZF_refl' T x :
  ZFeq' <<= T -> T ⊢ x ≡ x.
Proof.
  intros H. change (T ⊢ ($0 ≡ $0)[x..]).
  apply AllE. apply Ctx. firstorder.
Qed.

Lemma ZF_refl x :
  ZFeq' ⊢ x ≡ x.
Proof.
  now apply ZF_refl'.
Qed.

(* Ltac subsimpl_in' H :=
  rewrite !subst_term_comp, !subst_term_id in H; try now intros [|[|[|[|[|]]]]].

Ltac subsimpl' :=
  rewrite !subst_term_comp, !subst_term_id; try now intros [|[|[|[|[|]]]]]. *)

Ltac subsimpl_in H :=
  rewrite ?up_term, ?subst_term_shift in H.

Ltac subsimpl :=
  rewrite ?up_term, ?subst_term_shift.

Lemma ZF_sym' T x y :
  ZFeq' <<= T -> T ⊢ x ≡ y -> T ⊢ y ≡ x.
Proof.
  intros H1 H2. eapply IE; try apply H2.
  assert (H : T ⊢ ax_sym) by (apply Ctx; firstorder).
  apply (AllE x), (AllE y) in H; cbn in H. now subsimpl_in H.
Qed.

Lemma ZF_trans' T x y z :
  ZFeq' <<= T -> T ⊢ x ≡ y -> T ⊢ y ≡ z -> T ⊢ x ≡ z.
Proof.
  intros H1 H2 H3. eapply IE; try apply H3.
  eapply IE; try apply H2.
  assert (H : T ⊢ ax_trans) by (apply Ctx; firstorder).
  now apply (AllE x), (AllE y), (AllE z) in H; cbn in H; subsimpl_in H.
Qed.

Lemma ZF_eq_elem T x y x' y' :
  ZFeq' <<= T -> T ⊢ x ≡ x' -> T ⊢ y ≡ y' -> T ⊢ x ∈ y -> T ⊢ x' ∈ y'.
Proof.
  intros H1 H2 H3 H4. eapply IE; try apply H4.
  eapply IE; try apply H3. eapply IE; try apply H2.
  assert (H : T ⊢ ax_eq_elem) by (apply Ctx; firstorder).
  now apply (AllE x), (AllE y), (AllE x'), (AllE y') in H; cbn in H; subsimpl_in H.
Qed.

Lemma ZF_ext' T x y :
  ZFeq' <<= T -> T ⊢ sub x y -> T ⊢ sub y x -> T ⊢ x ≡ y.
Proof.
  intros H1 H2 H3. eapply IE; try apply H3.
  eapply IE; try apply H2.
  assert (H : T ⊢ ax_ext) by (apply Ctx; firstorder).
  apply (AllE x), (AllE y) in H; cbn in H.
  subsimpl_in H. apply H.
Qed.

Lemma ZF_pair_el' T x y z :
  ZFeq' <<= T -> T ⊢ (z ≡ x ∨ z ≡ y) <-> T ⊢ z ∈ {x; y}.
Proof.
  intros HT; split; intros H; eapply IE; try apply H.
  all: assert (HP : T ⊢ ax_pair) by (apply Ctx; firstorder).
  all: apply (AllE y), (AllE x), (AllE z) in HP; cbn in HP; subsimpl_in HP.
  - eapply CE2, HP.
  - eapply CE1, HP.
Qed.

Lemma ZF_pair_el x y z :
  ZFeq' ⊢ (z ≡ x ∨ z ≡ y) -> ZFeq' ⊢ z ∈ {x; y}.
Proof.
  now apply ZF_pair_el'.
Qed.

Ltac prv_all x :=
  apply AllI; edestruct nameless_equiv_all as [x ->]; cbn; subsimpl.

Lemma ZF_sub_pair T x y x' y' :
  ZFeq' <<= T -> T ⊢ x ≡ x' -> T ⊢ y ≡ y' -> T ⊢ {x; y} ⊆ {x'; y'}.
Proof.
  intros HT H1 H2. prv_all z.
  apply II. apply ZF_pair_el'; auto. eapply DE.
  - apply ZF_pair_el'; auto.
  - apply DI1. eapply ZF_trans'; auto. eapply Weak; eauto.
  - apply DI2. eapply ZF_trans'; auto. eapply Weak; eauto.
Qed.

Lemma ZF_eq_pair T x y x' y' :
  ZFeq' <<= T -> T ⊢ x ≡ x' -> T ⊢ y ≡ y' -> T ⊢ {x; y} ≡ {x'; y'}.
Proof.
  intros HT H1 H2. apply ZF_ext'; trivial.
  - now apply ZF_sub_pair.
  - apply ZF_sub_pair; trivial. all: now apply ZF_sym'.
Qed.

Lemma ZF_eq_opair T x y x' y' :
  ZFeq' <<= T -> T ⊢ x ≡ x' -> T ⊢ y ≡ y' -> T ⊢ opair x y ≡ opair x' y'.
Proof.
  intros HT H1 H2. repeat apply ZF_eq_pair; trivial.
Qed.

Definition sing x :=
  {x; x}.

Lemma ZF_sing_el x :
  ZFeq' ⊢ x ∈ sing x.
Proof.
  apply ZF_pair_el. apply DI1. apply ZF_refl.
Qed.

Lemma ZF_sing_iff T x y :
  ZFeq' <<= T -> T ⊢ x ∈ sing y <-> T ⊢ x ≡ y.
Proof.
  intros HT. unfold sing.
  rewrite <- ZF_pair_el'; trivial.
  split; intros H.
  - apply (DE H); auto.
  - now apply DI1.
Qed.

Lemma ZF_union_el' T x y z :
  ZFeq' <<= T -> T ⊢ y ∈ x ∧ z ∈ y -> T ⊢ z ∈ ⋃ x.
Proof.
  intros HT H.
  assert (HU : T ⊢ ax_union) by (apply Ctx; firstorder).
  apply (AllE x), (AllE z) in HU; cbn in HU. subsimpl_in HU.
  apply CE2 in HU. eapply IE; try apply HU.
  apply ExI with y. cbn. subsimpl. apply H.
Qed.

Lemma ZF_union_el x y z :
  ZFeq' ⊢ y ∈ x ∧ z ∈ y -> ZFeq' ⊢ z ∈ ⋃ x.
Proof.
  now apply ZF_union_el'.
Qed.

Ltac assert1 H :=
  match goal with  |- (?phi :: ?T) ⊢ _ => assert (H : (phi :: T) ⊢ phi) by auto end.

Ltac assert2 H :=
  match goal with  |- (?phi :: ?psi :: ?T) ⊢ _
                   => assert (H : ?phi :: ?psi :: T ⊢ psi) by auto end.

Ltac use_exists H x :=
  apply (ExE _ H); edestruct nameless_equiv_ex as [x ->]; cbn; subsimpl.

Lemma ZF_sub_union T x y :
  ZFeq' <<= T -> T ⊢ x ≡ y -> T ⊢ sub (⋃ x) (⋃ y).
Proof.
  intros HT H. prv_all z.
  apply II. assert1 H'.
  assert (HU : (z ∈ ⋃ x :: T) ⊢ ax_union) by (apply Ctx; firstorder).
  apply (AllE x), (AllE z) in HU; cbn in HU; subsimpl_in HU.
  apply CE1 in HU. eapply (IE HU) in H'.
  use_exists H' u. clear H' HU.
  eapply ZF_union_el'; auto. apply CI.
  - eapply ZF_eq_elem. auto. apply ZF_refl'; auto.
    apply (Weak H); auto. eapply CE1; auto.
  - eapply CE2; auto.
Qed.

Lemma ZF_eq_union T x y :
  ZFeq' <<= T -> T ⊢ x ≡ y -> T ⊢ ⋃ x ≡ ⋃ y.
Proof.
  intros HT H. apply ZF_ext'; try apply ZF_sub_union; trivial.
  now apply ZF_sym'.
Qed.

Lemma ZF_bunion_el' T x y z :
  ZFeq' <<= T -> T ⊢ (z ∈ x ∨ z ∈ y) -> T ⊢ z ∈ x ∪ y.
Proof.
  intros HT H. apply (DE H).
  - eapply ZF_union_el' with x. auto. apply CI; auto.
    apply ZF_pair_el'. auto. apply DI1. apply ZF_refl'. auto.
  - eapply ZF_union_el' with y. auto. apply CI; auto.
    apply ZF_pair_el'. auto. apply DI2. apply ZF_refl'. auto.
Qed.

Lemma ZF_bunion_el x y z :
  ZFeq' ⊢ (z ∈ x ∨ z ∈ y) -> ZFeq' ⊢ z ∈ x ∪ y.
Proof.
  now apply ZF_bunion_el'.
Qed.

Lemma imps T phi psi :
  T ⊢ phi --> psi <-> (phi :: T) ⊢ psi.
Proof.
  split; try apply II.
  intros H. apply IE with phi; auto. apply (Weak H). auto.
Qed.

Lemma ZF_bunion_inv' x y z :
   ZFeq' ⊢ z ∈ x ∪ y --> z ∈ x ∨ z ∈ y.
Proof.
  assert (TU : ZFeq' ⊢ ax_union) by (apply Ctx; firstorder). unfold ax_union in TU.
  eapply (AllE ({x; y})), (AllE z), CE1 in TU; cbn in TU; subsimpl_in TU.
  rewrite imps in *. use_exists TU u.
  eapply DE. apply ZF_pair_el'; auto.
  - eapply CE1. auto.
  - apply DI1. eapply ZF_eq_elem; auto.
    + apply ZF_refl'. auto.
    + eapply CE2. auto.
  - apply DI2. eapply ZF_eq_elem; auto.
    + apply ZF_refl'. auto.
    + eapply CE2. auto.
Qed.

Lemma ZF_bunion_inv T x y z :
   ZFeq' <<= T -> T ⊢ z ∈ x ∪ y -> T ⊢ z ∈ x ∨ z ∈ y.
Proof.
  intros HT H. eapply IE; try apply H.
  eapply Weak; try apply HT. apply ZF_bunion_inv'.
Qed.

Lemma ZF_eq_bunion T x y x' y' :
  ZFeq' <<= T -> T ⊢ x ≡ x' -> T ⊢ y ≡ y' -> T ⊢ x ∪ y ≡ x' ∪ y'.
Proof.
  intros HT H1 H2. now apply ZF_eq_union, ZF_eq_pair.
Qed.

Lemma ZF_sig_el T x :
   ZFeq' <<= T -> T ⊢ x ∈ σ x.
Proof.
  intros H. apply ZF_bunion_el'; trivial.
  apply DI2. apply ZF_sing_iff; trivial.
  apply ZF_refl'. trivial.
Qed.

Lemma ZF_eq_sig T x y :
  ZFeq' <<= T -> T ⊢ x ≡ y -> T ⊢ σ x ≡ σ y.
Proof.
  intros HT H. now apply ZF_eq_bunion, ZF_eq_pair.
Qed.

Lemma sing_pair1 T x y z :
  ZFeq' <<= T -> T ⊢ sing x ≡ {y; z} -> T ⊢ x ≡ y.
Proof.
  intros HT H. apply ZF_sym'; trivial.
  apply ZF_sing_iff; trivial. eapply ZF_eq_elem; trivial.
  apply ZF_refl'; trivial. apply ZF_sym'; eauto.
  apply ZF_pair_el'; trivial. apply DI1. now apply ZF_refl'.
Qed.

Lemma sing_pair2 T x y z :
  ZFeq' <<= T -> T ⊢ sing x ≡ {y; z} -> T ⊢ x ≡ z.
Proof.
  intros HT H. apply ZF_sym'; trivial.
  apply ZF_sing_iff; trivial. eapply ZF_eq_elem; trivial.
  apply ZF_refl'; trivial. apply ZF_sym'; eauto.
  apply ZF_pair_el'; trivial. apply DI2. now apply ZF_refl'.
Qed.

Lemma opair_inj1 T x y x' y' :
  ZFeq' <<= T -> T ⊢ opair x y ≡ opair x' y' -> T ⊢ x ≡ x'.
Proof.
  intros HT He. assert (H : T ⊢ {x; x} ∈ opair x y).
  { apply ZF_pair_el'; trivial. apply DI1. now apply ZF_refl'. }
  eapply ZF_eq_elem in H; try apply He; try apply ZF_refl'; trivial.
  apply ZF_pair_el' in H; trivial.
  apply (DE H); eapply sing_pair1; try apply prv_T1; auto.
Qed.

Lemma opair_inj2 T x y x' y' :
  ZFeq' <<= T -> T ⊢ opair x y ≡ opair x' y' -> T ⊢ y ≡ y'.
Proof.
  intros HT H. assert (H' : T ⊢ y ≡ x' ∨ y ≡ y').
  - assert (H2 : T ⊢ {x; y} ∈ opair x' y').
    { eapply ZF_eq_elem; trivial. apply ZF_refl'; trivial. apply H.
      apply ZF_pair_el'; trivial. apply DI2. now apply ZF_refl'. }
    apply ZF_pair_el' in H2; trivial. apply (DE H2).
    + apply DI1. apply ZF_sym'; auto. eapply sing_pair2; auto. apply ZF_sym'; auto.
    + apply ZF_pair_el'; auto. eapply ZF_eq_elem; auto.
      * apply ZF_refl'; auto.
      * apply ZF_pair_el'; auto. apply DI2. apply ZF_refl'. auto.
  - apply (DE H'); try apply prv_T1.
    assert (H1 : T ⊢ x ≡ x') by apply (opair_inj1 HT H).
    assert (H2 : T ⊢ {x'; y'} ∈ opair x y).
    { eapply ZF_eq_elem; trivial. apply ZF_refl'; trivial. apply ZF_sym', H; trivial.
      apply ZF_pair_el'; trivial. apply DI2. now apply ZF_refl'. }
    apply ZF_pair_el' in H2; trivial.
    eapply DE; try eapply (Weak H2); auto.
    + eapply ZF_trans'; auto. eapply ZF_trans'; auto.
      * apply ZF_sym'. auto. apply (Weak H1). auto.
      * eapply sing_pair2; auto. apply ZF_sym'; auto.
    + eapply ZF_trans'; auto. eapply sing_pair2; auto. eapply ZF_trans'; auto.
      2: apply ZF_sym'; auto.
      eapply ZF_eq_pair; try apply ZF_sym'; auto.
      apply (Weak H1). auto.
    + auto.
Qed.

Lemma ZF_bunion_el1 T x y z :
  ZFeq' <<= T -> T ⊢ z ∈ x -> T ⊢ z ∈ x ∪ y.
Proof.
  intros HT H. now apply ZF_bunion_el', DI1.
Qed.

Lemma ZF_bunion_el2 T x y z :
  ZFeq' <<= T -> T ⊢ z ∈ y -> T ⊢ z ∈ x ∪ y.
Proof.
  intros HT H. now apply ZF_bunion_el', DI2.
Qed.
 
Lemma bunion_eset x :
   ZFeq' ⊢ ∅ ∪ x ≡ x.
Proof.
  apply ZF_ext'; auto; prv_all y; apply II.
  - eapply DE. eapply ZF_bunion_inv; auto. 
    + apply Exp. eapply IE.
      eapply Weak; try apply ZF_eset. all: auto.
    + auto.
  - apply ZF_bunion_el2; auto.
Qed.

Lemma bunion_swap x y z :
  ZFeq' ⊢ (x ∪ y) ∪ z ≡ (x ∪ z) ∪ y.
Proof.
  apply ZF_ext'; auto; prv_all u; apply II.
  - eapply DE. eapply ZF_bunion_inv; auto.
    + eapply DE. eapply ZF_bunion_inv; auto.
      * apply ZF_bunion_el1, ZF_bunion_el1. all: auto.
      * apply ZF_bunion_el2; auto.
    + apply ZF_bunion_el1, ZF_bunion_el2. all: auto.
  - eapply DE. eapply ZF_bunion_inv; auto.
    + eapply DE. eapply ZF_bunion_inv; auto.
      * apply ZF_bunion_el1, ZF_bunion_el1. all: auto.
      * apply ZF_bunion_el2; auto.
    + apply ZF_bunion_el1, ZF_bunion_el2. all: auto.
Qed.

Lemma bunion_use T x y z phi :
  ZFeq' <<= T -> (x ∈ y :: T) ⊢ phi -> (x ≡ z :: T) ⊢ phi -> T ⊢ x ∈ y ∪ sing z --> phi.
Proof.
  intros HT H1 H2. apply II. eapply DE.
  - eapply ZF_bunion_inv; auto.
  - apply (Weak H1). auto.
  - eapply IE.
    + eapply Weak. apply II, H2. auto.
    + apply ZF_sing_iff; auto.
Qed.

Lemma ZF_numeral_trans T n x y :
  ZFeq' <<= T -> T ⊢ x ∈ tnumeral n --> y ∈ x --> y ∈ tnumeral n.
Proof.
  intros HT. induction n; cbn.
  - apply II, Exp. eapply IE. apply ZF_eset'. all: auto.
  - apply bunion_use; trivial.
    + rewrite !imps in *. apply ZF_bunion_el1; auto.
    + apply II. apply ZF_bunion_el'. auto.
      apply DI1. eapply ZF_eq_elem; auto.
      apply ZF_refl'. auto.
Qed.

Lemma ZF_numeral_wf T n :
  ZFeq' <<= T -> T ⊢ ¬ (tnumeral n ∈ tnumeral n).
Proof.
  intros HT. induction n; cbn.
  - now apply ZF_eset'.
  - apply bunion_use; trivial.
    + eapply IE. apply (Weak IHn). auto.
      eapply IE. eapply IE. apply ZF_numeral_trans; auto.
      auto. apply ZF_sig_el. auto.
    + eapply IE. apply (Weak IHn). auto.
      eapply ZF_eq_elem. auto. apply ZF_refl'. auto.
      auto. apply ZF_sig_el. auto.
Qed.





(** ** Preservation proof *)

Lemma enc_derivations_base R n :
  ZFeq' ⊢ {{∅; ∅}; {∅; enc_stack R}} ∈ enc_derivations R n.
Proof.
  induction n; cbn.
  - apply ZF_sing_el.
  - apply ZF_bunion_el. now apply DI1.
Qed.

Lemma enc_derivations_step B n :
  ZFeq' ⊢ opair (tnumeral n) (enc_stack (derivations B n)) ∈ enc_derivations B n.
Proof.
  destruct n; cbn.
  - apply ZF_sing_el.
  - apply ZF_bunion_el. apply DI2. apply ZF_sing_el.
Qed.

Lemma enc_stack_spec R s t :
  s/t el R -> ZFeq' ⊢ opair (enc_string s) (enc_string t) ∈ enc_stack R.
Proof.
  induction R as [|[u v] R IH]; cbn; auto.
  intros [[=]| H]; subst.
  - apply ZF_bunion_el. apply DI2. apply ZF_sing_el.
  - apply ZF_bunion_el. apply DI1. now apply IH.
Qed.


Lemma ZF_derivations_bound T B k n x :
  ZFeq' <<= T -> T ⊢ opair k x ∈ enc_derivations B n -> T ⊢ k ∈ σ (tnumeral n).
Proof.
  induction n in T |- *; cbn; intros HT H.
  - apply ZF_sing_iff in H; trivial. eapply ZF_eq_elem; trivial.
    apply ZF_sym'; trivial. eapply opair_inj1; trivial. apply H.
    apply ZF_refl'; trivial. eapply ZF_bunion_el'; trivial.
    apply DI2. apply ZF_sing_iff; trivial. apply ZF_refl'; trivial.
  - apply ZF_bunion_inv in H; trivial. apply (DE H).
    + apply ZF_bunion_el1. auto. apply IHn; try apply prv_T1. auto.
    + apply ZF_bunion_el2. auto. apply ZF_sing_iff. auto.
      eapply opair_inj1. auto. apply ZF_sing_iff; try apply prv_T1. auto.
Qed.

Lemma enc_derivations_functional B n :
  ZFeq' ⊢ opair $2 $1 ∈ enc_derivations B n --> opair $2 $0 ∈ enc_derivations B n --> $ 1 ≡ $ 0.
Proof.
  induction n; cbn -[derivations].
  - repeat apply impl. eapply opair_inj2. auto. eapply ZF_trans'. auto.
    + apply ZF_sing_iff; try apply prv_T2. auto.
    + apply ZF_sym'. auto. apply ZF_sing_iff; try apply prv_T1. auto.
  - apply bunion_use; try apply bunion_use. 1,2,5: auto.
    + repeat apply imp. now apply (Weak IHn).
    + apply exf. eapply IE. apply (@ZF_numeral_wf _ (S n)). auto.
      eapply ZF_derivations_bound. auto. eapply ZF_eq_elem; try apply prv_T2. auto.
      2: apply ZF_refl'. 2: auto. apply ZF_eq_opair. auto.
      eapply opair_inj1; try apply prv_T1. auto. apply ZF_refl'. auto.
    + apply exf. eapply IE. apply (@ZF_numeral_wf _ (S n)). auto.
      eapply ZF_derivations_bound. auto. eapply ZF_eq_elem; try apply prv_T1. auto.
      2: apply ZF_refl'. 2: auto. apply ZF_eq_opair. auto.
      eapply opair_inj1; try apply prv_T2. auto. apply ZF_refl'. auto.
    + eapply opair_inj2. auto. eapply ZF_trans'; try apply prv_T2. auto.
      apply ZF_sym'; try apply prv_T1. auto.
Qed.

Lemma prep_string_subst sigma s x :
  subst_term sigma (prep_string s x) = prep_string s (subst_term sigma x).
Proof.
  induction s; cbn; trivial. rewrite IHs.
  rewrite substt_bounded0; eauto.
  apply enc_bool_bounded0.
Qed.

Lemma is_rep_subst s t x y sigma :
  subst_form sigma (is_rep (comb_rel s t) x y) =
  is_rep (comb_rel s t) (subst_term sigma x) (subst_term sigma y).
Proof.
  unfold is_rep. cbn -[comb_rel]. asimpl. repeat f_equal.
  - unfold comb_rel. cbn. rewrite !prep_string_subst. reflexivity.
  - unfold comb_rel. cbn. rewrite !prep_string_subst. reflexivity.
Qed.

Lemma combinations_subst B x y sigma :
  subst_form sigma (combinations B x y) = combinations B (subst_term sigma x) (subst_term sigma y).
Proof.
  induction B as [|[s t] B IH] in sigma, x, y |- *.
  - cbn. reflexivity.
  - cbn -[is_rep]. rewrite IH, is_rep_subst. cbn -[is_rep]. now asimpl.
Qed.

Lemma enc_derivations_eq T B n x :
  ZFeq' <<= T -> T ⊢ opair (tnumeral n) x ∈ enc_derivations B n -> T ⊢ x ≡ enc_stack (derivations B n).
Proof.
  intros HT H. destruct n; cbn in *.
  - eapply opair_inj2; trivial. eapply ZF_sing_iff; eauto.
  - apply ZF_bunion_inv in H; trivial. apply (DE H).
    + apply exf. eapply IE. apply (ZF_numeral_wf (S n)). auto.
      eapply ZF_derivations_bound. auto. apply prv_T1.
    + eapply opair_inj2. auto. apply ZF_sing_iff. auto. apply prv_T1.
Qed.

Lemma enc_stack_app {T} {HB : bounded_theory T} B C :
  ZFeq' <<= T -> T ⊢ (enc_stack B) ∪ (enc_stack C) ≡ enc_stack (B ++ C).
Proof.
  intros HT. induction B as [|[s t] B IH]; cbn.
  - eapply Weak; try apply bunion_eset. assumption.
  - eapply ZF_trans'; trivial. eapply Weak; try apply bunion_swap; trivial.
    eapply ZF_eq_bunion; trivial. apply ZF_refl'; trivial.
Qed.

Lemma prep_string_app s t x :
  prep_string (s ++ t) x = prep_string s (prep_string t x).
Proof.
  induction s; cbn; congruence.
Qed.

Lemma ZF_eq_prep T s x y :
  ZFeq' <<= T -> T ⊢ x ≡ y -> T ⊢ prep_string s x ≡ prep_string s y.
Proof.
  intros HT H. induction s; cbn; try tauto.
  apply ZF_eq_opair; trivial. now apply ZF_refl'.
Qed.

Lemma append_all_el T B s t x y :
  ZFeq' <<= T -> T ⊢ opair x y ∈ enc_stack B
  -> T ⊢ opair (prep_string s x) (prep_string t y) ∈ enc_stack (append_all B (s/t)).
Proof.
  intros HT H. induction B as [|[u v] B IH] in T, HT, H |- *; cbn in *.
  - apply exf. eapply IE. 2: apply H. now apply ZF_eset'.
  - eapply (ZF_bunion_el' HT). eapply DE. apply (ZF_bunion_inv HT H).
    + apply DI1. apply IH; try apply prv_T1. auto.
    + assert1 H'. apply ZF_sing_iff in H'; try now auto.
      apply DI2. apply ZF_sing_iff. auto.
      rewrite !prep_string_app. apply ZF_eq_opair. auto.
      * apply ZF_eq_prep. auto. eapply opair_inj1; eauto. auto.
      * apply ZF_eq_prep. auto. eapply opair_inj2; eauto. auto.
Qed.

Lemma is_rep_eq {T} {HB : bounded_theory T} B s t x y :
  ZFeq' <<= T -> T ⊢ x ≡ enc_stack B -> T ⊢ is_rep (comb_rel s t) x y
  -> T ⊢ y ≡ enc_stack (append_all B (s / t)).
Proof.
  intros HT H1 H2. apply ZF_ext'; trivial.
  - apply bt_all. intros a. cbn.
    eapply AllE in H2. cbn -[comb_rel] in H2.
    eapply CE1 in H2. eapply imps. apply H2.
    apply impl. assert1 H. use_exists H b. apply prv_clear2. clear H.
    cbn -[comb_rel]. asimpl. assert1 H. apply CE in H as [H H'].
    unfold comb_rel at 2 in H'. cbn -[comb_rel] in H'. asimpl in H'.
    rewrite !prep_string_subst in H'. cbn -[comb_rel] in H'. 
    use_exists H' c. clear H'.
    cbn -[comb_rel]. asimpl. rewrite !prep_string_subst. cbn -[comb_rel].
    assert1 H'. use_exists H' d. clear H'.
    cbn -[comb_rel]. asimpl. rewrite !prep_string_subst. cbn -[comb_rel]. asimpl.
    eapply ZF_eq_elem. auto. apply ZF_sym'. auto.
    eapply CE2. apply prv_T1. apply ZF_refl'. auto.
    apply append_all_el. auto.
    eapply ZF_eq_elem. auto. eapply CE1. apply prv_T1.
    eapply (Weak H1). auto. eapply (Weak H). auto.
  - apply bt_all. intros a. cbn. asimpl.
    apply (@AllE _ _ _ _ _ a) in H2. cbn -[comb_rel] in H2. asimpl in H2.
    eapply CE2 in H2. eapply imps. 2: apply H2. clear H2. apply impl.
    induction B as [|[u v] B IH] in T, x, HT, H1, HB |- *; cbn -[comb_rel] in *.
    + apply exf. eapply IE; try apply prv_T1. apply ZF_eset'. auto.
    + apply imp. apply bunion_use; trivial.
      * specialize (IH T HB (enc_stack B) HT).
        assert (H : T ⊢ enc_stack B ≡ enc_stack B) by now apply ZF_refl'.
        apply IH in H. use_exists H z. clear H. apply ExI with z.
        cbn -[comb_rel]. asimpl. assert1 H. apply CE in H as [H H'].
        apply CI; trivial. eapply ZF_eq_elem. auto.
        apply ZF_refl'. auto. apply ZF_sym'. auto.
        apply (Weak H1). auto. apply ZF_bunion_el1; trivial. auto.
      * apply ExI with (opair (enc_string u) (enc_string v)).
        cbn -[comb_rel]. asimpl. apply CI.
        -- eapply ZF_eq_elem. auto. apply ZF_refl'. auto.
           apply ZF_sym'. auto. apply (Weak H1). auto.
           apply ZF_bunion_el2. auto. eapply Weak. apply ZF_sing_el.
           auto.
        -- cbn. apply ExI with (enc_string v).
           cbn. apply ExI with (enc_string u).
           cbn. asimpl. rewrite !prep_string_subst, !prep_string_app; cbn.
           apply CI; try apply prv_T1. apply ZF_refl'. auto.
Qed.

Lemma combinations_eq {T} {HB : bounded_theory T} B C x y :
  ZFeq' <<= T -> T ⊢ x ≡ enc_stack C -> T ⊢ combinations B x y -> T ⊢ y ≡ enc_stack (derivation_step B C).
Proof.
  induction B as [|[s t] B IH] in y, T, HB |-*; cbn; intros HT H1 H2; trivial.
  use_exists H2 u. clear H2. cbn -[is_rep]. asimpl. assert1 H. use_exists H v. clear H. apply prv_clear2.
  cbn -[is_rep]. asimpl. rewrite !combinations_subst, !is_rep_subst. cbn -[is_rep]. asimpl.
  eapply ZF_trans'. auto. eapply CE1. apply prv_T1.
  eapply ZF_trans'. auto. 2: apply enc_stack_app; eauto. 2: auto.
  apply ZF_eq_bunion; eauto. auto.
  - eapply is_rep_eq; eauto. auto. apply prv_clear1. eauto.
    eapply CE2. eapply CE2. apply prv_T1.
  - apply IH; eauto. auto.
    + now apply prv_clear1.
    + eapply CE1. eapply CE2. apply prv_T1.
Qed.

Lemma combinations_step B n (i x y : term) :
  ZFeq' ⊢ i ∈ tnumeral n --> opair i x ∈ enc_derivations B n
     --> combinations B x y --> opair (σ i) y ∈ enc_derivations B n.
Proof.
  induction n; cbn.
  - apply impl. apply exf.
    apply imp. apply ZF_eset.
  - apply bunion_use; try apply bunion_use.
    apply tsubs_refl. 1, 4: apply tsubs_extend.
    + apply impl. apply ZF_bunion_el'. auto.
      apply DI1. eapply IE. eapply IE. eapply IE.
      * eapply Weak. apply IHn. auto.
      * apply prv_T3.
      * apply prv_T2.
      * apply prv_T1.
    + apply exf. eapply IE. apply (ZF_numeral_wf (S n)). auto.
      eapply ZF_eq_elem. auto. eapply opair_inj1. auto. apply prv_T1.
      apply ZF_refl'. auto. cbn. apply ZF_bunion_el'. auto.
      apply DI1. apply prv_T2.
    + apply impl. apply ZF_bunion_el'. auto.
      apply DI2. apply ZF_sing_iff. auto.
      apply ZF_eq_opair. auto.
      * apply ZF_eq_sig; eauto. auto. apply prv_T3.
      * eapply combinations_eq; eauto; try apply prv_T1. auto.
        apply enc_derivations_eq. auto.
        eapply ZF_eq_elem; try apply prv_T2; try apply ZF_refl'. 1, 3: auto.
        eapply ZF_eq_opair; try apply prv_T3; try apply ZF_refl'. all: auto.
    + apply exf. eapply IE. apply (ZF_numeral_wf n). auto.
      eapply ZF_eq_elem. auto. apply ZF_refl'. auto.
      eapply ZF_trans'. auto. apply ZF_sym'. auto.
      eapply opair_inj1. auto. apply prv_T1. apply prv_T2.
      apply ZF_sig_el. auto.
Qed.

Theorem BPCP_slv B :
  BPCP' B -> ZFeq' ⊢ solvable B.
Proof.
  intros [s H]. destruct (derivable_derivations H) as [n Hn].
  apply ExI with (tnumeral n);
  apply ExI with (enc_derivations B n);
  apply ExI with (opair (enc_string s) (enc_string s));
  apply ExI with (enc_string s);
  apply ExI with (enc_stack (derivations B n)); fold subst_form.
  cbn; rewrite !substt_bounded0; repeat apply perst_bounded0; eauto.
  repeat apply CI.
  - apply ZF_numeral.
  - repeat apply ZF_all. asimpl. unfold unscoped.shift.
    apply enc_derivations_functional.
  - apply enc_derivations_base.
  - repeat apply ZF_all. rewrite !combinations_subst. cbn. asimpl.
    rewrite !combinations_subst. cbn. unfold unscoped.shift.
    apply combinations_step.
  - apply enc_derivations_step.
  - now apply enc_stack_spec.
  - apply ZF_refl.
Qed.





(** ** Main Theorem *)

Theorem dPCP_ZFD B :
  dPCPb B -> ZFeq' ⊢ solvable B.
Proof.
Admitted.

Theorem PCP_ZFD B :
  PCPb B -> ZFeq' ⊢ solvable B.
Proof.
  rewrite PCPb_iff_dPCPb. apply dPCP_ZFD.
Qed.

End ZF.




