(** ** Conservativity Results for ZF *)

From Undecidability.FOL.Util Require Import FullTarski_facts Syntax_facts FullDeduction_facts.
From Undecidability.FOL Require Import ZF minZF Reductions.PCPb_to_ZF Reductions.PCPb_to_minZF.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Local Set Implicit Arguments.
Local Unset Strict Implicit.


(* ** Deductive conservativity *)

Lemma loop_deductive { p : peirce } phi :
  minZFeq' ⊢ phi <~> rm_const_fm (embed phi).
Proof.
  induction phi using form_ind_subst; cbn.
  - apply CI; apply II; auto.
  - rewrite (vec_inv2 t). cbn.
    destruct Vector.hd as [x|[]], (Vector.hd (Vector.tl t)) as [y|[]]. cbn.
    destruct P0; cbn in *; apply CI; apply II.
    + apply ExI with $x. cbn. apply CI; try apply minZF_refl; auto.
      apply ExI with $y. cbn. apply CI; try apply minZF_refl; auto.
    + assert1 H. use_exists' H a. clear H. assert1 H. apply CE in H as [_ H].
      use_exists' H b. eapply minZF_elem; auto. 1,2: eapply CE1; eauto. eapply CE2; auto.
    + apply ExI with $x. cbn. apply CI; try apply minZF_refl; auto.
      apply ExI with $y. cbn. apply CI; try apply minZF_refl; auto.
    + assert1 H. use_exists' H a. clear H. assert1 H. apply CE in H as [_ H].
      use_exists' H b. eapply minZF_trans; auto. 2: eapply CE1; auto.
      apply minZF_sym; auto. eapply minZF_trans; auto. 2: eapply CE1; auto.
      apply minZF_sym; auto. eapply CE2; auto.
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

Theorem conservativity_deductive { p : peirce } phi :
  ZFeq' ⊢ embed phi -> minZFeq' ⊢ phi.
Proof.
  intros H. apply (@rm_const_prv _ nil) in H. cbn in H.
  eapply IE; try apply H. eapply CE2, loop_deductive.
Qed.


(* ** Semantic conservativity *)

Section Model.

  Open Scope sem.

  Context {V : Type} {I : interp sig_func_empty _ V}.

  Hypothesis M_ZF : forall rho, rho ⊫ minZF'.
  Variable x0 : V.

  Instance full_model : interp _ _ V.
  Proof.
    split.
    - intros [] _; exact x0.
    - now apply (@i_atom sig_func_empty).
  Defined.

  Lemma full_embed_eval (rho : nat -> V) (t : term') :
    eval rho (embed_t t) = eval rho t.
  Proof.
    destruct t as [|[]]. reflexivity.
  Qed.

  Lemma full_embed (rho : nat -> V) (phi : form')  :
    sat full_model rho (embed phi) <-> sat I rho phi.
  Proof.
    induction phi in rho |- *; try destruct b0; try destruct q; cbn.
    1,3-7: firstorder. erewrite Vector.map_map, Vector.map_ext.
    reflexivity. apply full_embed_eval.
  Qed.

End Model.

Theorem conservativity_semantic phi :
  entailment_ZF' (embed phi) -> entailment_minZF' phi.
Proof.
  intros H D I rho H1 H2. destruct (H2 rho ax_eset') as [x0 _]; try now right.
  apply full_embed with x0. apply H; try apply H1. intros sigma psi [<-|[<-|[<-|[<-|Hp]]]].
  - cbn. apply (H2 sigma ax_ext'). now left.
  - cbn. admit.
  - cbn.
Abort.
  
