(** ** Conservativity Results for ZF *)

From Undecidability.FOL.Util
     Require Import FullTarski_facts Syntax_facts FullDeduction_facts.

From Undecidability.FOL
     Require Import ZF minZF Reductions.PCPb_to_ZF Reductions.PCPb_to_minZF Reductions.PCPb_to_ZFD.

From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Local Set Implicit Arguments.
Local Unset Strict Implicit.

Open Scope syn.


(* ** Deductive conservativity *)

Lemma elem_iff { p : peirce } A x y :
  minZFeq' <<= A -> A ⊢ ∃ $0 ≡' $(S x) ∧ (∃ $0 ≡' $(S (S y)) ∧ $1 ∈' $0) <-> A ⊢ $x ∈' $y.
Proof.
  intros HA. split; intros H.
  - use_exists' H x'. clear H. assert1 H. apply CE in H as [_ H].
    use_exists' H y'. eapply minZF_elem; auto. 1,2: eapply CE1; eauto. eapply CE2; auto.
  - apply ExI with $x. cbn. apply CI; try apply minZF_refl; auto.
    apply ExI with $y. cbn. apply CI; try apply minZF_refl; auto.
Qed.

Lemma equal_iff { p : peirce } A x y :
  minZFeq' <<= A -> A ⊢ ∃ $0 ≡' $(S x) ∧ (∃ $0 ≡' $(S (S y)) ∧ $1 ≡' $0) <-> A ⊢ $x ≡' $y.
Proof.
  intros HA. split; intros H.
  - use_exists' H x'. clear H. assert1 H. apply CE in H as [_ H].
    use_exists' H y'. eapply minZF_trans; auto. 2: eapply CE1; auto.
      apply minZF_sym; auto. eapply minZF_trans; auto. 2: eapply CE1; auto.
      apply minZF_sym; auto. eapply CE2; auto.
  - apply ExI with $x. cbn. apply CI; try apply minZF_refl; auto.
    apply ExI with $y. cbn. apply CI; try apply minZF_refl; auto.
Qed.

Lemma loop_deductive { p : peirce } phi :
  minZFeq' ⊢ phi <~> rm_const_fm (embed phi).
Proof.
  induction phi using form_ind_subst; cbn.
  - apply CI; apply II; auto.
  - rewrite (vec_inv2 t). cbn.
    destruct Vector.hd as [x|[]], (Vector.hd (Vector.tl t)) as [y|[]]. cbn.
    destruct P0; cbn in *; apply CI; apply II.
    + apply elem_iff; auto.
    + apply elem_iff; auto.
    + apply equal_iff; auto.
    + apply equal_iff; auto.
  - destruct b0; cbn in *; apply CI; apply II.
    + apply CE1 in IHphi1. apply CE1 in IHphi2. apply CI; eapply IE.
      1,3: eapply Weak; eauto. eapply CE1; auto. eapply CE2; auto.
    + apply CE2 in IHphi1. apply CE2 in IHphi2. apply CI; eapply IE.
      1,3: eapply Weak; eauto. eapply CE1; auto. eapply CE2; auto.
    + apply CE1 in IHphi1. apply CE1 in IHphi2. eapply DE; try now apply Ctx.
      * apply DI1. eapply IE; try now apply Ctx. eapply Weak; try apply IHphi1. auto.
      * apply DI2. eapply IE; try now apply Ctx. eapply Weak; try apply IHphi2. auto.
    + apply CE2 in IHphi1. apply CE2 in IHphi2. eapply DE; try now apply Ctx.
      * apply DI1. eapply IE; try now apply Ctx. eapply Weak; try apply IHphi1. auto.
      * apply DI2. eapply IE; try now apply Ctx. eapply Weak; try apply IHphi2. auto.
    + apply CE2 in IHphi1. apply CE1 in IHphi2. apply II. eapply IE.
      eapply Weak; eauto. eapply IE. auto. eapply IE; try now apply Ctx. eapply Weak; eauto.
    + apply CE1 in IHphi1. apply CE2 in IHphi2. apply II. eapply IE.
      eapply Weak; eauto. eapply IE. auto. eapply IE; try now apply Ctx. eapply Weak; eauto.
  - destruct q; cbn in *; apply CI; apply II.
    + prv_all' x. rewrite rm_const_fm_subst, <- embed_subst. eapply IE.
      * eapply Weak; try eapply CE1, H. auto.
      * apply AllE. auto.
    + prv_all' x. eapply IE.
      * eapply Weak; try eapply CE2, H. auto.
      * rewrite embed_subst, <- rm_const_fm_subst. apply AllE. auto.
    + assert1 H'. use_exists' H' x. apply ExI with x.
      rewrite rm_const_fm_subst, <- embed_subst. eapply IE; try now apply Ctx.
      eapply Weak; try eapply CE1, H. auto.
    + assert1 H'. use_exists' H' x. apply ExI with x.
      rewrite rm_const_fm_subst, <- embed_subst. eapply IE; try now apply Ctx.
      eapply Weak; try eapply CE2, H. auto.
Qed.

Lemma loop_deductive' { p : peirce } phi A :
  minZFeq' <<= A -> A ⊢ rm_const_fm (embed phi) -> A ⊢ phi.
Proof.
  intros H1 H2. eapply IE; try apply H2. eapply CE2.
  eapply Weak; try apply H1. apply loop_deductive.
Qed.

Theorem conservativity_ZF' { p : peirce } phi :
  ZFeq' ⊢ embed phi -> minZFeq' ⊢ phi.
Proof.
  intros H. apply (@rm_const_prv _ nil) in H. cbn in H. now apply loop_deductive'.
Qed.

Lemma Z_decomp { p : peirce } phi :
  Zeq ⊢T phi -> exists A, (map ax_sep A ++ ZFeq') ⊢ phi.
Proof.
  intros [A [H1 H2]]. induction A in phi, H1, H2 |- *.
  - exists nil. cbn. eapply Weak; eauto.
  - rewrite <- imps in H2. apply IHA in H2 as [B H]; auto.
    rewrite imps in H. destruct (H1 a); auto.
    + exists B. eapply Weak; try apply H. auto.
    + exists (phi0 :: B). cbn. apply H.
Qed.

Lemma minZF_sep { p : peirce } A phi :
  minZFeq' <<= A -> A ⊢ ax_sep' (rm_const_fm phi) ~> rm_const_fm (ax_sep phi).
Proof.
  intros HA. apply II. assert1 H. cbn in *.
  eapply all_equiv. 2: apply Ctx; now left. intros [x|[]]. cbn.
  apply ex_equiv. intros B [y|[]] HB. cbn.
  apply all_equiv. intros [z|[]]. cbn.
  apply iff_equiv; intros C HC.
  2: apply and_equiv. 1,2: apply elem_iff; intros psi; auto.
  rewrite !rm_const_fm_subst. cbn; subsimpl; rewrite !subst_comp.
  erewrite subst_ext; try reflexivity. now intros [|n].
Qed.

Theorem conservativity_Z { p : peirce } phi :
  Zeq ⊢T embed phi -> minZeq ⊢T phi.
Proof.
  intros [A HA] % Z_decomp. apply rm_const_prv in HA.
  rewrite map_map in HA. apply loop_deductive' in HA; auto.
  exists ([ax_sep' (rm_const_fm psi) | psi ∈ A] ++ minZFeq'). split.
  - intros psi [H|H] % in_app_iff; try now constructor.
    apply in_map_iff in H as [psi'[<- H]]. constructor 2.
  - apply (prv_cut HA). intros psi [[psi' [<- H]] % in_map_iff|H] % in_app_iff; auto.
    eapply IE; try apply minZF_sep; auto. apply Ctx, in_app_iff. left. refine (in_map _ _ _ H).
Qed.

Lemma ZF_decomp { p : peirce } phi :
  ZFeq ⊢T phi -> exists A B, ((map ax_sep A ++ map ax_rep B) ++ ZFeq') ⊢ phi.
Proof.
  intros [C [H1 H2]]. induction C in phi, H1, H2 |- *.
  - exists nil, nil. cbn. eapply Weak; eauto.
  - rewrite <- imps in H2. apply IHC in H2 as [A[B HAB]]; auto.
    rewrite imps in HAB. destruct (H1 a); auto.
    + exists A, B. eapply Weak; try apply HAB. auto.
    + exists (phi0 :: A), B. cbn. apply HAB.
    + exists A, (phi0 :: B). cbn. eapply Weak; try apply HAB.
      intros psi [->|[[H|H] % in_app_iff|H] % in_app_iff]; auto.
      apply in_app_iff. left. apply in_app_iff. right. now right.
Qed.

Lemma minZF_rep { p : peirce } A phi :
  minZFeq' <<= A -> A ⊢ ax_rep' (rm_const_fm phi) ~> rm_const_fm (ax_rep phi).
Proof.
  intros HA. apply II. assert1 H. cbn in *. eapply impl_equiv. 3: apply Ctx; now left.
  - intros B HB. apply all_equiv. intros [x|[]]. cbn. apply all_equiv. intros [y|[]]. cbn.
    apply all_equiv. intros [z|[]]. cbn. apply impl_equiv; intros C HC.
    + rewrite !rm_const_fm_subst, !subst_comp.
      erewrite subst_ext; try reflexivity. now intros [|[|n]].
    + apply impl_equiv; intros D HD. 2: eapply equal_iff; intros psi HP; apply HD; auto.
      rewrite !rm_const_fm_subst, !subst_comp.
      erewrite subst_ext; try reflexivity. now intros [|[|n]].
  - intros B HB. apply all_equiv. intros [x|[]]. cbn.
    apply ex_equiv. intros C [y|[]] HC. cbn.
    apply all_equiv. intros [z|[]]. cbn.
    apply iff_equiv; intros D HD. 1: apply elem_iff; intros psi HP; apply HD; auto.
    apply ex_equiv. intros E [u|[]] HE. cbn.
    apply and_equiv. 1: apply elem_iff; intros psi HP; apply HE, HD; auto.
    rewrite !rm_const_fm_subst. cbn; subsimpl; rewrite !subst_comp.
    erewrite subst_ext; try reflexivity. now intros [|[|n]].
Qed.

Theorem conservativity_ZF { p : peirce } phi :
  ZFeq ⊢T embed phi -> minZFeq ⊢T phi.
Proof.
  intros [A [B HAB]] % ZF_decomp. apply rm_const_prv, loop_deductive' in HAB; auto.
  exists ([ax_sep' (rm_const_fm psi) | psi ∈ A] ++ [ax_rep' (rm_const_fm psi) | psi ∈ B] ++ minZFeq'). split.
  - intros psi [|[H|H] % in_app_iff] % in_app_iff; try now constructor.
    all: apply in_map_iff in H as [psi'[<- H]]. constructor 2. constructor 3.
  - apply (prv_cut HAB). intros psi [[psi' [<- H]] % in_map_iff|H] % in_app_iff.
    + apply in_app_iff in H as [[phi' [<- H]] % in_map_iff|[phi' [<- H]] % in_map_iff].
      * eapply IE; try apply minZF_sep; auto. apply Ctx, in_app_iff. left. refine (in_map _ _ _ H).
      * eapply IE; try apply minZF_rep; auto. apply Ctx, in_app_iff. right.
        apply in_app_iff. left. refine (in_map _ _ _ H).
    + auto. apply Ctx. auto.
Qed.


(* ** Backwards directions *)

Lemma prv_embed { p : peirce } A phi :
  A ⊢ phi -> (map embed A) ⊢ embed phi.
Proof.
  intros H. pattern p, A, phi. revert p A phi H.
  apply prv_ind_full; cbn; intros; subst; auto. 1,6-9: eauto.
  - apply AllI. apply (Weak H0).
    rewrite !map_map. intros psi' [psi [<- HP]] % in_map_iff.
    apply in_map_iff. eexists. split; try apply HP.
    rewrite embed_subst. apply subst_ext. reflexivity.
  - apply (AllE (embed_t t)) in H0. rewrite embed_subst.
    erewrite subst_ext; try apply H0. now intros [|n].
  - apply (ExI (embed_t t)). rewrite embed_subst in H0.
    erewrite subst_ext; try apply H0. now intros [|n].
  - eapply ExE; try apply H0. rewrite embed_subst in H2.
    erewrite subst_ext; try apply (Weak H2); try now intros [|n].
    rewrite !map_map. intros theta' [<-|[theta [<- HP]] % in_map_iff]; auto.
    right. apply in_map_iff. eexists. split; try apply HP.
    rewrite embed_subst. apply subst_ext. reflexivity.
Qed.

Lemma ZF_eset { p : peirce } :
  ZFeq' ⊢ ∀ ¬ $0 ∈ ∅.
Proof.
  assert (H : ZFeq' ⊢ ax_eset) by (apply Ctx; unfold ZFeq', ZF'; eauto 6).
  prv_all x. apply (AllE x H).
Qed.

Lemma ZF_inductive_embed { p : peirce } t :
  ZFeq' ⊢ inductive t <~> (embed (is_inductive $0))[t..].
Proof.
  cbn. apply CI; apply II; apply CI.
  - apply (ExI ∅). cbn. subsimpl. apply CI; try apply (Weak ZF_eset); auto.
    eapply CE1. apply Ctx. left. reflexivity.
  - prv_all x. apply II. apply (ExI (σ x)). cbn. subsimpl. apply CI.
    + admit.
    + eapply IE; try now apply Ctx. assert2 H.
      apply CE2, (AllE x) in H. cbn in H. now subsimpl_in H.
  - assert1 H. apply CE1 in H. use_exists H x. clear H. eapply ZF_eq_elem; auto.
    2: apply ZF_refl'; auto. 2: eapply CE2; eauto. apply ZF_ext'; auto.
    + prv_all y. apply II. apply Exp. assert2 H. apply CE1 in H. apply (AllE y) in H.
      cbn in H. subsimpl_in H. apply (IE H). auto.
    + prv_all y. apply II. apply Exp. eapply IE; try now apply Ctx. apply ZF_eset'. auto.
  - prv_all x. assert1 H. apply CE2 in H. apply (AllE x) in H. cbn in H. subsimpl_in H.
    rewrite imps in *. use_exists H y. clear H. eapply ZF_eq_elem. admit.
Admitted.

Lemma embed_ZF' { p : peirce } phi :
  phi el minZFeq' -> ZFeq' ⊢ embed phi.
Proof.
  intros [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]].
  1-5: cbn; apply Ctx; unfold ZFeq', ZF'; eauto.
  - cbn. apply (ExI ∅). cbn. apply ZF_eset.
  - assert (H : ZFeq' ⊢ ax_pair) by (apply Ctx; unfold ZFeq', ZF'; eauto 7).
    cbn. prv_all x. prv_all y. apply (ExI ({x; y})). cbn. subsimpl.
    apply (AllE y) in H. cbn in H. apply (AllE x) in H. cbn in H. now subsimpl_in H.
  - assert (H : ZFeq' ⊢ ax_union) by (apply Ctx; unfold ZFeq', ZF'; eauto 8).
    cbn. prv_all x. apply (ExI (⋃ x)). cbn. subsimpl. apply (AllE x H).
  - assert (H : ZFeq' ⊢ ax_power) by (apply Ctx; unfold ZFeq', ZF'; eauto 9).
    cbn. prv_all x. apply (ExI (PP x)). cbn. subsimpl. apply (AllE x H).
  - cbn. apply (ExI ω). cbn. apply CI.
    + assert (H : ZFeq' ⊢ ax_om1) by (apply Ctx; unfold ZFeq', ZF'; eauto 10).
      unfold ax_om1 in H. apply (IE (CE1 (ZF_inductive_embed ω))) in H. apply H.
    + assert (H : ZFeq' ⊢ ax_om2) by (apply Ctx; unfold ZFeq', ZF'; eauto 11).
      prv_all x. apply II. apply (AllE x) in H. cbn in H. eapply IE; try apply (Weak H); auto.
      specialize (CE2 (ZF_inductive_embed x)). intros H'. eapply IE; try apply (Weak H'); auto.
Qed.

Theorem conservativity_back_ZF' { p : peirce } phi :
  minZFeq' ⊢ phi -> ZFeq' ⊢ embed phi.
Proof.
  intros HP. apply prv_embed in HP. apply (prv_cut HP).
  intros psi' [psi[<- H]] % in_map_iff. now apply embed_ZF'.
Qed.

Lemma minZ_decomp { p : peirce } phi :
  minZeq ⊢T phi -> exists A, (map ax_sep' A ++ minZFeq') ⊢ phi.
Proof.
  intros [A [H1 H2]]. induction A in phi, H1, H2 |- *.
  - exists nil. cbn. eapply Weak; eauto.
  - rewrite <- imps in H2. apply IHA in H2 as [B H]; auto.
    rewrite imps in H. destruct (H1 a); auto.
    + exists B. eapply Weak; try apply H. auto.
    + exists (phi0 :: B). cbn. apply H.
Qed.

Theorem conservativity_back_Z { p : peirce } phi :
  minZeq ⊢T phi -> Zeq ⊢T embed phi.
Proof.
  intros [A HA] % minZ_decomp. apply prv_embed in HA.
  exists ([ax_sep (embed psi) | psi ∈ A] ++ ZFeq'). split.
  - intros psi [H|H] % in_app_iff; try now constructor.
    apply in_map_iff in H as [psi'[<- H]]. constructor 2.
  - apply (prv_cut HA). intros psi' [psi [<- [H|H] % in_app_iff]] % in_map_iff.
    + apply in_map_iff in H as [theta [<- H]]. apply Ctx. apply in_app_iff. left.
      apply in_map_iff. exists theta. split; trivial. cbn. unfold ax_sep.
      rewrite embed_subst. erewrite subst_ext; try reflexivity. now intros [|n].
    + eapply Weak; try apply embed_ZF'; auto.
Qed.

Lemma minZF_decomp { p : peirce } phi :
  minZFeq ⊢T phi -> exists A B, ((map ax_sep' A ++ map ax_rep' B) ++ minZFeq') ⊢ phi.
Proof.
  intros [C [H1 H2]]. induction C in phi, H1, H2 |- *.
  - exists nil, nil. cbn. eapply Weak; eauto.
  - rewrite <- imps in H2. apply IHC in H2 as [A[B HAB]]; auto.
    rewrite imps in HAB. destruct (H1 a); auto.
    + exists A, B. eapply Weak; try apply HAB. auto.
    + exists (phi0 :: A), B. cbn. apply HAB.
    + exists A, (phi0 :: B). cbn. eapply Weak; try apply HAB.
      intros psi [->|[[H|H] % in_app_iff|H] % in_app_iff]; auto.
      apply in_app_iff. left. apply in_app_iff. right. now right.
Qed.

Theorem conservativity_back_ZF { p : peirce } phi :
  minZFeq ⊢T phi -> ZFeq ⊢T embed phi.
Proof.
  intros [A[B HAB]] % minZF_decomp. apply prv_embed in HAB.
  exists ([ax_sep (embed psi) | psi ∈ A] ++ [ax_rep (embed psi) | psi ∈ B] ++ ZFeq'). split.
  - intros psi [H|[H|H] % in_app_iff] % in_app_iff; try now constructor.
    + apply in_map_iff in H as [psi'[<- H]]. constructor 2.
    + apply in_map_iff in H as [psi'[<- H]]. constructor 3.
  - apply (prv_cut HAB). intros psi' [psi [<- [[H|H] % in_app_iff|H] % in_app_iff]] % in_map_iff.
    + apply in_map_iff in H as [theta [<- H]]. apply Ctx. apply in_app_iff. left.
      apply in_map_iff. exists theta. split; trivial. cbn. unfold ax_sep.
      rewrite embed_subst. erewrite subst_ext; try reflexivity. now intros [|n].
    + apply in_map_iff in H as [theta [<- H]]. apply Ctx. apply in_app_iff. right.
      apply in_app_iff. left. apply in_map_iff. exists theta. split; trivial. cbn. unfold ax_rep, fun_rel.
      rewrite !embed_subst. setoid_rewrite subst_ext at 1. setoid_rewrite subst_ext at 2.
      setoid_rewrite subst_ext at 3. setoid_rewrite subst_ext at 4. reflexivity.
      all: now intros [|[|n]].
    + eapply Weak; try apply embed_ZF'; auto.
Qed.



