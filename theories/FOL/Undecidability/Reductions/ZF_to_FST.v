(** ** Indirect reduction from ZF to finite set theory with Skolem functions *)

From Undecidability.FOL.Basics
     Require Import Syntax.Facts Semantics.Tarski.FullFacts Deduction.FullFacts.

From Undecidability.FOL.Basics.Axiomatizations.Sets
     Require Import Models.Aczel Models.ZF_model ZF minZF FST.

From Undecidability.FOL.Undecidability.Reductions
     Require Import PCPb_to_ZF PCPb_to_ZFeq PCPb_to_minZF PCPb_to_minZFeq PCPb_to_ZFD.

Require Import Lia.

From Undecidability.PCP Require Import PCP.

From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Local Hint Constructors prv : core.

#[local] Notation term' := (term sig_empty).
#[local] Notation form' := (form sig_empty _ _ falsity_on).

Definition embed_t' (t : term') : term :=
  match t with
  | $x => $x
  | func f ts => False_rect term f
  end.

Fixpoint embed' {ff'} (phi : form sig_empty ZF_pred_sig _ ff') : form ff' :=
  match phi with 
  | atom P ts => atom (if P then elem else equal) (Vector.map embed_t' ts)
  | bin b phi psi => bin b (embed' phi) (embed' psi)
  | quant q phi => quant q (embed' phi)
  | ⊥ => ⊥
  end.

Lemma embed_subst_t' (sigma : nat -> term') (t : term') :
  embed_t' t`[sigma] = (embed_t' t)`[sigma >> embed_t'].
Proof.
  induction t; cbn; trivial. destruct F.
Qed.

Lemma embed_subst' (sigma : nat -> term') phi :
  embed' phi[sigma] = (embed' phi)[sigma >> embed_t'].
Proof.
  induction phi in sigma |- *; cbn; trivial.
  - f_equal. erewrite !Vector.map_map, Vector.map_ext. reflexivity. apply embed_subst_t'.
  - firstorder congruence.
  - rewrite IHphi. f_equal. apply subst_ext. intros []; cbn; trivial.
    unfold funcomp. cbn. unfold funcomp. now destruct (sigma n) as [x|[]].
Qed.

Lemma prv_embed { p : peirce } A phi :
  A ⊢ phi -> (map embed' A) ⊢ embed' phi.
Proof.
  intros H. pattern p, A, phi. revert p A phi H.
  apply prv_ind_full; cbn; intros; subst; auto. 1,6-9: eauto.
  - apply AllI. apply (Weak H0).
    rewrite !map_map. intros psi' [psi [<- HP]] % in_map_iff.
    apply in_map_iff. eexists. split; try apply HP.
    rewrite embed_subst'. apply subst_ext. reflexivity.
  - apply (AllE (embed_t' t)) in H0. rewrite embed_subst'.
    erewrite subst_ext; try apply H0. now intros [|n].
  - apply (ExI (embed_t' t)). rewrite embed_subst' in H0.
    erewrite subst_ext; try apply H0. now intros [|n].
  - eapply ExE; try apply H0. rewrite embed_subst' in H2.
    erewrite subst_ext; try apply (Weak H2); try now intros [|n].
    rewrite !map_map. intros theta' [<-|[theta [<- HP]] % in_map_iff]; auto.
    right. apply in_map_iff. eexists. split; try apply HP.
    rewrite embed_subst'. apply subst_ext. reflexivity.
Qed.

Definition solvable' B :=
  embed' (impl (rev minZFeq') (rm_const_fm (solvable B))).

Theorem PCP_FSTD { p : peirce } B :
  PCPb B -> FSTeq ⊢ solvable' B.
Proof.
  intros H. apply Weak with nil; auto.
  change nil with (map embed' nil). apply prv_embed.
  apply impl_prv.  rewrite rev_involutive, app_nil_r.
  change minZFeq' with (map rm_const_fm nil ++ minZFeq'). apply rm_const_prv.
  cbn. now apply PCP_ZFD.
Qed.

Section IM.
  
  Instance FST_interp : interp Acz.
  Proof.
    split; intros [].
    - intros _. exact AEmpty.
    - intros v.
      exact (Aunion (Aupair (Aupair (Vector.hd v) (Vector.hd v)) (Vector.hd (Vector.tl v)))).
    - intros v. exact (Ain (Vector.hd v) (Vector.hd (Vector.tl v))).
    - intros v. exact (Aeq (Vector.hd v) (Vector.hd (Vector.tl v))).
  Defined.

  Lemma FST_standard :
    standard Acz_interp.
  Proof.
    intros s [n Hn]. cbn in Hn. exists n. apply Hn.
  Qed.

  Lemma FST_FSTeq rho :
    rho ⊫ FSTeq.
  Proof.
    intros phi [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn -[Aunion].
    - apply Aeq_ref.
    - apply Aeq_sym.
    - apply Aeq_tra.
    - intros s t s' t' -> ->. tauto.
    - apply Aeq_ext.
    - apply AEmptyAx.
    - intros X Y Z. rewrite AunionAx. split; intros H.
      + destruct H as [A[H1 H2]]. apply AupairAx in H1 as [H1|H1].
        * left. rewrite H1 in H2. apply AupairAx in H2. tauto.
        * right. rewrite <- H1. tauto.
      + destruct H as [H|H].
        * exists (Aupair Y Y). rewrite !AupairAx. intuition.
        * exists X. split; trivial. apply AupairAx. now right.
  Qed.

End IM.

Section Model.

  Open Scope sem.

  Context {V : Type} {I : interp V}.

  Hypothesis M_ZF : forall rho, rho ⊫ FST.

  Instance min_model' : interp sig_empty ZF_pred_sig V.
  Proof.
    split.
    - intros [].
    - intros [].
      + apply (@i_atom _ _ _ I elem).
      + apply (@i_atom _ _ _ I equal).
  Defined.

  Lemma min_embed_eval' (rho : nat -> V) (t : term') :
    eval rho (embed_t' t) = eval rho t.
  Proof.
    destruct t as [|[]]. reflexivity.
  Qed.

  Lemma min_embed' (rho : nat -> V) phi :
    sat I rho (embed' phi) <-> sat min_model' rho phi.
  Proof.
    induction phi in rho |- *; try destruct b0; try destruct q; cbn.
    1,3-7: firstorder. destruct P; erewrite Vector.map_map, Vector.map_ext.
    reflexivity. apply min_embed_eval'.
    reflexivity. apply min_embed_eval'.
  Qed.

End Model.

Theorem PCP_FST B :
  entailment_FSTeq (solvable' B) -> PCPb B.
Proof.
  intros H. specialize (H Acz FST_interp). unshelve eapply PCP_ZFeq.
  - exact Acz.
  - exact Acz_interp.
  - intros N. apply AEmpty.
  - apply Acz_ZFeq'.
  - apply Acz_standard.
  - specialize (H (fun _ : nat => AEmpty) FST_FSTeq).
    assert (HE : @min_model Acz Acz_interp = @min_model' Acz FST_interp).
    { unfold min_model, min_model'. f_equal. }
    apply min_embed' in H. apply impl_sat in H.
    + rewrite <- HE in H. apply min_correct in H; trivial. apply Acz_ZFeq'.
    + intros phi Hp % in_rev. specialize (@min_axioms' Acz Acz_interp). intros HA.
      rewrite <- HE. apply HA; trivial. apply Acz_ZFeq'.
Qed.
      
