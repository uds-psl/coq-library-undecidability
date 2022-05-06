(* ** Indirect reduction from ZF to finite set theory without Skolem functions *)

From Undecidability.FOL.Util Require Import Syntax Syntax_facts FullTarski_facts FullDeduction FullDeduction_facts.
From Undecidability.FOL Require Import binFST binZF Reductions.PCPb_to_binZF.
Require Import Lia.

From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Local Hint Constructors prv : core.

Definition ZF_to_FST phi :=
  ax_pair' ~> ax_union' ~> ax_power' ~> ax_om' ~> phi.

Lemma bZF_elem { p : peirce } T x x' y y' :
  binZF <<= T -> T ⊢ x ≡' x' -> T ⊢ y ≡' y' -> T ⊢ x ∈' y -> T ⊢ x' ∈' y'.
Proof.
  intros H1 H2 H3 H4. eapply IE; try apply H4.
  eapply IE; try apply H3. eapply IE; try apply H2.
  assert (H : T ⊢ ax_eq_elem') by (apply Ctx; firstorder).
  apply (AllE x), (AllE y), (AllE x'), (AllE y') in H; cbn in H.
  unfold eq' in H. cbn in H. subsimpl_in H. apply H.
Qed.

Lemma bZF_refl { p : peirce } T x :
  binZF <<= T -> T ⊢ x ≡' x.
Proof.
  intros H. prv_all' y. apply CI; apply II; auto.
Qed.

Ltac assert5 H :=
  match goal with |- (?g :: ?f :: ?phi :: ?psi :: ?theta :: ?T) ⊢ _
                  => assert (H : (g :: f :: phi :: psi :: theta :: T) ⊢ theta) by auto 7 end.

Ltac assert6 H :=
  match goal with |- (?h :: ?g :: ?f :: ?phi :: ?psi :: ?theta :: ?T) ⊢ _
                  => assert (H : (h :: g :: f :: phi :: psi :: theta :: T) ⊢ theta) by auto 7 end.

Lemma bZF_adj { p : peirce } :
  binZF ⊢ ax_adj'.
Proof.
  prv_all' x. prv_all' y.
  assert (H : binZF ⊢ ax_pair'). { apply Ctx. unfold binZF. auto. }
  apply (AllE y) in H. cbn in H. apply (AllE y) in H. cbn in H.
  use_exists' H sy. clear H.
  assert (H : binZF ⊢ ax_pair'). { apply Ctx. unfold binZF. auto. }
  apply (AllE x) in H. cbn in H. apply (AllE sy) in H. cbn in H.
  eapply Weak in H. use_exists' H pxy. clear H. 2: auto.
  assert (H : binZF ⊢ ax_union'). { apply Ctx. unfold binZF. auto. }
  apply (AllE pxy) in H. cbn in H. eapply Weak in H. use_exists' H a. clear H. 2: auto.
  apply (ExI a). cbn. subsimpl. prv_all' b. apply CI; apply II.
  - assert2 H. apply (AllE b) in H. cbn in H. subsimpl_in H. apply CE1 in H.
    rewrite imps in H. eapply Weak in H. use_exists' H c. clear H. 2: auto.
    assert4 H. apply (AllE c) in H. cbn in H. subsimpl_in H. cbn in H. apply CE1 in H.
    eapply DE. eapply IE. apply H. eapply CE1. auto.
    + apply DI1. eapply bZF_elem. auto 7.
      * apply bZF_refl. auto 7.
      * apply Ctx. left. unfold eq'. cbn. subsimpl. reflexivity.
      * eapply CE2. auto.
    + apply DI2. clear H. assert6 H. apply (AllE b) in H. cbn in H. subsimpl_in H.
      apply CE1 in H. eapply DE. eapply IE; try apply H.
      * eapply bZF_elem. auto 7. 1: apply bZF_refl. auto 7. 2: eapply CE2; auto.
        apply Ctx. left. unfold eq'. cbn. subsimpl. reflexivity.
      * apply Ctx. left. unfold eq'. cbn. subsimpl. reflexivity.
      * apply Ctx. left. unfold eq'. cbn. subsimpl. reflexivity.
  - assert2 H. apply (AllE b) in H. cbn in H. subsimpl_in H. apply CE2 in H.
    apply (IE H). eapply DE; try now apply Ctx.
    + apply (ExI x). cbn. subsimpl. apply CI; auto.
      clear H. assert4 H. apply (AllE x) in H. cbn in H. subsimpl_in H. apply CE2 in H.
      apply (IE H). apply DI1. unfold eq'. cbn. subsimpl. apply bZF_refl. auto 7.
    + apply (ExI sy). cbn. subsimpl. apply CI.
      * clear H. assert4 H. apply (AllE sy) in H. cbn in H. subsimpl_in H. apply CE2 in H.
        apply (IE H). apply DI2. unfold eq'. cbn. subsimpl. apply bZF_refl. auto 7.
      * clear H. assert5 H. apply (AllE b) in H. cbn in H. subsimpl_in H. apply CE2 in H.
        apply (IE H). apply DI2. unfold eq'. cbn. subsimpl. auto.
Qed.

Theorem reduction_entailment phi :
  entailment_binZF phi <-> entailment_binFST (ZF_to_FST phi).
Proof.
  split; intros Hp D I rho HI.
  - unfold ZF_to_FST. intros H1 H2 H3 H4. apply Hp.
    intros psi [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; trivial.
    all: apply HI; unfold binFST; intuition.
  - apply Hp; fold sat. 2-5: apply HI; unfold binZF; intuition auto 7.
    intros psi [<-|[<-|[<-|[<-|[]]]]]. 1-3: apply HI; unfold binZF; intuition.
    apply (soundness bZF_adj). apply HI.
Qed.

Theorem reduction_deduction phi :
  deduction_binZF phi <-> deduction_binFST (ZF_to_FST phi).
Proof.
  split; intros H.
  - repeat apply II. apply (prv_cut H).
    intros psi [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]].
    all: unfold binFST; apply Ctx; intuition auto 7.
  - unfold ZF_to_FST in H. repeat setoid_rewrite imps in H. apply (prv_cut H).
    intros psi [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; trivial.
    8: apply bZF_adj. all: unfold binZF; apply Ctx; intuition auto 7.
Qed.
