(** * Classical Natural Deduction *)

From Undecidability.FOLC Require Export ND BPCP_FOL GenTarski.

(** ** Double Negation Translation *)

Existing Instance min_sig.

Definition dnQ (phi : form) : form := (phi --> Pred Q Vector.nil) --> Pred Q Vector.nil.

Fixpoint trans (phi : form) : form :=
  match phi with
  | Impl phi1 phi2 => Impl (trans phi1) (trans phi2)
  | All phi => All (trans phi)
  | Pred P v => dnQ (Pred P v)
  | Pred Q v => Pred Q Vector.nil
  | Fal => Pred Q Vector.nil
  end.

Lemma trans_subst t (phi : form) :
  trans (subst_form t phi) = subst_form t (trans phi).
Proof.
  induction phi in t |- *; cbn; try congruence.
  now destruct P. 
Qed.

Lemma appCtx psi1 psi2 A :
  psi1 --> psi2 el A -> A ⊢IE psi1 -> A ⊢IE psi2.
Proof.
  intros. eapply (IE (phi := psi1) (psi := psi2)); eauto using Ctx.
Qed.

Lemma app1 psi1 psi2 A :
  (psi1 --> psi2 :: A) ⊢IE psi1 -> (psi1 --> psi2 :: A) ⊢IE psi2.
Proof.
  intros. eapply appCtx; eauto.
Qed.

Lemma app2 psi1 psi2 A phi :
  (phi :: psi1 --> psi2 :: A) ⊢IE psi1 -> (phi :: psi1 --> psi2 :: A) ⊢IE psi2.
Proof.
  intros. eapply appCtx; eauto.
Qed.

Lemma app3 psi1 psi2 A phi phi2 :
  (phi :: phi2 :: psi1 --> psi2 :: A) ⊢IE psi1 -> (phi :: phi2 :: psi1 --> psi2 :: A) ⊢IE psi2.
Proof.
  intros. eapply appCtx; eauto.
Qed.

Lemma nameless_equiv_all' A phi :
  exists t, A ⊢IE phi[t..] <-> [p[↑] | p ∈ A] ⊢IE phi.
Proof.
  destruct (find_unused_L (phi::A)) as [n HN].
  exists (var_term n). apply nameless_equiv.
  - intros psi H. apply HN; auto.
  - apply HN; auto.
Qed.

Lemma trans_trans (phi : form ) A :
  A ⊢IE ((dnQ (trans phi)) --> trans phi).
Proof.
  revert A. induction phi using form_ind_subst; cbn; intros.
  - ointros. oapply 0. ointros. ctx.
  - destruct p.
    + ointros. unfold dnQ at 3. ointros.
      oapply 1. ointros. oapply 0. ctx.
    + ointros. oapply 0. ointros. ctx.
  - oimport IHphi2. ointros. oapply 2.
    unfold dnQ. ointros. oapply 2. eapply II. oapply 1. oapply 0. ctx.
  - eapply II.
    eapply AllI.
    edestruct nameless_equiv_all' as [t]. eapply H0. clear H0.
    specialize (H t). oimport H. rewrite trans_subst. oapply 0.
    unfold dnQ. ointros. oapply 2. ointros.
    oapply 1. eapply AllE. ctx.
Qed.
        
Notation QQ := (Pred Q Vector.nil).

Lemma Double' A (phi : form) :
  A ⊢CE phi -> map trans A ⊢IE trans phi.
Proof.
  remember class as s; remember expl as e; induction 1; subst.
  1-5,7: cbn in *; subst; try congruence.
  - eapply II. eauto.
  - eapply IE; eauto.
  - eapply AllI.
    rewrite map_map in *. erewrite map_ext. eauto. intros. 
    now rewrite <- trans_subst. 
  - rewrite trans_subst. eapply AllE; eauto.
  - specialize (IHprv eq_refl eq_refl). eapply IE. eapply trans_trans.
    unfold dnQ. oimport IHprv. eauto.
  - eauto.
  - eapply IE. eapply trans_trans. cbn. unfold dnQ. ointros.
    oapply 0. ointros. oapply 0. ointros.
    eapply IE. eapply trans_trans. unfold dnQ. ointros. oapply 3.
    ointros. ctx.    
Qed.

Lemma Double (phi : form) :
  [] ⊢CE phi -> [] ⊢IE (trans phi).
Proof.
  eapply Double'. 
Qed.

(** ** Reduction **)
    
Section BPCP_CND.

  Variable R : BSRS.
  
  Lemma BPCP_to_CND :
    BPCP R -> [] ⊢CE (F R).
  Proof.
    intros H. rewrite BPCP_BPCP' in *. now apply BPCP_prv'.
  Qed.

  Lemma impl_trans A phi :
    trans (A ⟹ phi) = (map trans A) ⟹ trans phi.
  Proof.
    induction A; cbn; congruence.
  Qed.
    
  Lemma CND_BPCP :
    [] ⊢CE (F R) -> BPCP R.
  Proof.
    intros H % Double. eapply Soundness with (C := exploding_bot) in H.
    specialize (H _ (IB R) (ltac:(firstorder)) (fun _ => nil)).
    unfold F, F1, F2 in H. rewrite !impl_trans, !map_map, !impl_sat in H. cbn in H.
    eapply BPCP_BPCP'.  eapply H.
    - eauto.
    - intros ? [(x,y) [<- ?] ] % in_map_iff ?. cbn in *. eapply H1.
      left. now rewrite !IB_enc.
    - intros ? [(x,y) [<- ?] ] % in_map_iff ? ? ? ?. cbn in *. eapply H1. intros.
      eapply H2. rewrite !IB_prep. cbn. econstructor 2; trivial.
    - intros. eapply H0. intros []; eauto.
    - firstorder congruence.
    - firstorder.
  Qed.

  Lemma BPCP_CND :
    BPCP R <-> [] ⊢CE (F R).
  Proof. 
    split. eapply BPCP_to_CND. intros ? % CND_BPCP.  eauto.
  Qed.

End BPCP_CND.



(** ** Corollaries **)

Corollary cprv_red :
  BPCP ⪯ @prv min_sig class expl List.nil.
Proof.
  exists (fun R => F R). intros R. apply (BPCP_CND R).
Qed.

(* Corollary cprv_undec : *)
(*   UA -> ~ decidable (cprv nil). *)
(* Proof. *)
(*   intros H. now apply (not_decidable cprv_red). *)
(* Qed. *)

(* Corollary cprv_unenum : *)
(*   UA -> ~ enumerable (compl (@cprv nil)). *)
(* Proof. *)
(*   intros H. apply (not_coenumerable cprv_red); trivial. *)
(* Qed. *)
