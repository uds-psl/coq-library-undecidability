(** * Classical Natural Deduction *)

From Undecidability.FOL Require Export PCPb_to_FOL.
Require Import Undecidability.PCP.Reductions.PCPb_iff_dPCPb.
(** ** Double Negation Translation *)

Implicit Type b : falsity_flag.

Definition cprv := @prv _ _ falsity_on class.

Instance iUnit (P : Prop) : interp unit.
Proof.
  split; intros [] v.
  - exact tt.
  - exact tt.
  - exact True.
  - exact P.
Defined.

Hint Constructors prv : core.

Fixpoint cast {b} (phi : form b) : form falsity_on :=
  match phi with
  | atom P v => atom P v
  | falsity => falsity
  | bin Impl phi psi => bin (b := falsity_on) Impl (cast phi) (cast psi)
  | quant All phi => quant (b := falsity_on) All (cast phi)
  end.

Lemma subst_cast {b} sigma phi :
  cast (subst_form sigma phi) = subst_form sigma (cast phi).
Proof.
  induction phi in sigma |- *; cbn in *; trivial.
  - destruct b0. cbn. congruence.
  - destruct q. cbn. congruence.
Qed.
  
Lemma MND_CND A (phi : form falsity_off) :
  A ⊢M phi -> map cast A ⊢C cast phi.
Proof.
  revert A phi. remember falsity_off as b. intros.
  induction H; cbn in *; subst; try congruence.
  - eapply II; eauto.
  - eapply IE; try now apply IHprv1. now apply IHprv2.
  - eapply AllI. rewrite map_map. rewrite map_map in IHprv.
    erewrite map_ext; try now apply IHprv. intros psi. cbn. now rewrite subst_cast.
  - setoid_rewrite subst_cast. eapply AllE; eauto.
  - eapply Ctx, in_map_iff; eauto.
  - apply Pc.
Qed.

Lemma DN A phi :
  A ⊢C (¬¬phi) -> A ⊢C phi.
Proof.
  intros H. eapply IE with ((phi --> falsity) --> phi); try apply Pc.
  apply II, Exp. eapply IE. apply (Weak H); auto. now apply Ctx.
Qed.
                                                    
Lemma cnd_XM:
  (forall (phi : form falsity_on), cprv nil phi -> valid phi) ->
  forall P, ~~ P -> P.
Proof.
  intros H P. specialize (H ( (¬¬Q) --> Q)).
  refine (H _ unit (iUnit P) (fun _ => tt)).
  eapply II. eapply DN. eauto.
Qed.

Definition dnQ {b} (phi : form b) : form b := (phi --> Q) --> Q.

Fixpoint trans {b} (phi : form b) : form b :=
  match phi with
  | bin Impl phi1 phi2 => bin Impl (trans phi1) (trans phi2)
  | quant All phi => quant All (trans phi)
  | atom sPr v => dnQ (atom sPr v)
  | atom _ _ => atom sQ (Vector.nil _)
  | falsity => @atom _ _ _ falsity_on sQ (Vector.nil _)
  end.

Lemma trans_subst b sigma (phi : form b) :
  trans (subst_form sigma phi) = subst_form sigma (trans phi).
Proof.
  induction phi in sigma |- *; cbn; trivial.
  - now destruct P.
  - destruct b0. cbn. congruence.
  - destruct q. cbn. congruence.
Qed.

Lemma appCtx b psi1 psi2 A :
  In (psi1 --> psi2) A -> A ⊢I psi1 -> A ⊢I psi2.
Proof.
  intros. eapply (IE (phi := psi1) (psi := psi2)); eauto using Ctx.
Qed.

Lemma app1 b psi1 psi2 A :
  (psi1 --> psi2 :: A) ⊢I psi1 -> (psi1 --> psi2 :: A) ⊢I psi2.
Proof.
  intros. eapply appCtx; eauto.
Qed.

Lemma app2 b psi1 psi2 A phi :
  (phi :: psi1 --> psi2 :: A) ⊢I psi1 -> (phi :: psi1 --> psi2 :: A) ⊢I psi2.
Proof.
  intros. eapply appCtx; eauto.
Qed.

Lemma app3 b psi1 psi2 A phi phi2 :
  (phi :: phi2 :: psi1 --> psi2 :: A) ⊢I psi1 -> (phi :: phi2 :: psi1 --> psi2 :: A) ⊢I psi2.
Proof.
  intros. eapply appCtx; eauto.
Qed.

Lemma trans_trans b (phi : form b) A :
  A ⊢I ((dnQ (trans phi)) --> trans phi).
Proof.
  revert A. induction phi; cbn; intros; try destruct P; try destruct b0; try destruct q.
  - cbn. eapply II. eapply app1. eapply II. eapply Ctx. eauto.
  - eapply II. eapply II. eapply app2. eapply II.
    eapply app1. eapply Ctx. eauto.
  - eapply II. eapply app1. eapply II. eapply Ctx. eauto.
  - eapply II. eapply II. eapply IE. eapply IHphi2.
    eapply II. eapply app3. eapply II. eapply app2. eapply app1. eapply Ctx. eauto.
  - admit.
Admitted.
        
Lemma Double' b A (phi : form b) :
  A ⊢C phi -> map trans A ⊢I trans phi.
Proof.
  remember class as s; induction 1; cbn in *; subst; try congruence.
  - eapply II. eauto.
  - eapply IE; eauto.
  - apply AllI. rewrite map_map. rewrite map_map in IHprv.
    erewrite map_ext; try now apply IHprv. intros psi. cbn. now rewrite trans_subst.
  - setoid_rewrite trans_subst. eapply AllE; eauto.
  - specialize (IHprv eq_refl). eapply IE. eapply trans_trans.
    apply II. apply (Weak IHprv). auto.
  - eapply Ctx. now eapply in_map.
  - admit.
Admitted.

Lemma Double b (phi : form b) :
  [] ⊢C phi -> [] ⊢I (trans phi).
Proof.
  eapply Double'. 
Qed.


(** ** Reduction **)
    
Section BPCP_CND.
  Local Definition BSRS := list (card bool).
  Variable R : BSRS.
  Context {ff : falsity_flag}.

  Lemma BPCP_to_CND :
    PCPb R -> [] ⊢C (F R).
  Proof.
    intros H. rewrite PCPb_iff_dPCPb in *. now apply BPCP_prv'.
  Qed.

  Lemma impl_trans A phi :
    trans (A ==> phi) = (map trans A) ==> trans phi.
  Proof.
    induction A; cbn; congruence.
  Qed.
    
  Lemma CND_BPCP :
    [] ⊢C (F R) -> PCPb R.
  Proof.
    intros H % Double % soundness.
    specialize (H _ (IB R) (fun _ => nil)).
    unfold F, F1, F2 in H. rewrite !impl_trans, !map_map, !impl_sat in H. cbn in H.
    eapply PCPb_iff_dPCPb. eapply H; try tauto.
    - intros ? [(x,y) [<- ?] ] % in_map_iff ?. cbn in *. eapply H1.
      left. now rewrite !IB_enc.
    - intros ? [(x,y) [<- ?] ] % in_map_iff ? ? ? ?. cbn in *. eapply H1. intros.
      eapply H2. rewrite !IB_prep. cbn. econstructor 2; trivial.
    - intros. eapply H0. intros. unfold dPCPb, dPCP. eauto.
  Qed.

  Lemma BPCP_CND :
    PCPb R <-> [] ⊢C (F R).
  Proof. 
    split. eapply BPCP_to_CND. intros ? % CND_BPCP. eauto.
  Qed.

End BPCP_CND.

Theorem cprv_red :
  PCPb ⪯ FOL_prv_class.
Proof.
  exists (fun R => F R). intros R. apply (BPCP_CND R).
Qed.


(** ** Corollaries **)


Corollary cprv_undec :
  UA -> ~ decidable (cprv nil).
Proof.
  intros H. now apply (not_decidable cprv_red).
Qed.

Corollary cprv_unenum :
  UA -> ~ enumerable (compl (@cprv nil)).
Proof.
  intros H. apply (not_coenumerable cprv_red); trivial.
Qed.
