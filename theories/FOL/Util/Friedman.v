Require Import List Lia.
From Undecidability.FOL.Util Require Import Syntax Syntax_facts FullTarski FullTarski_facts FullDeduction_facts FullDeduction.
From Undecidability.FOL.Reductions Require Import H10p_to_FA. 
Import Vector.VectorNotations.



Section Signature.

  
  (* Assume some signature and corresponding arity functions *)
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  (* Add one more 0-ary predicate (i.e. propositional variable) to the predicates *)
  Inductive new_preds : Type :=
    Q_ : new_preds
  | old_preds (P : Σ_preds) : new_preds. 

  Definition new_preds_ar (P : new_preds) :=
    match P with
    | Q_ => 0
    | old_preds P => ar_preds P
    end.

  Existing Instance Σ_funcs.
  Instance extended_preds : preds_signature :=
    {| preds := new_preds ; ar_preds := new_preds_ar |}.


  (* New propositional variable and "double negation" with respect to it *)
  Definition Q := (@atom Σ_funcs extended_preds _ falsity_off Q_ ([])).
  Definition dn {ff} F phi : @form Σ_funcs extended_preds _ ff :=
    (phi ~> F) ~> F.

  Fixpoint cast {ff} (phi : @form Σ_funcs Σ_preds _ ff) : @form Σ_funcs extended_preds _ falsity_off :=
    match phi with
    | falsity => Q
    | atom P v => (@atom _ _ _ falsity_off (old_preds P) v)
    | bin b phi psi => bin b (cast phi) (cast psi)
    | quant q phi => quant q (cast phi)
    end.
  
  Fixpoint Fr {ff} (phi : @form Σ_funcs Σ_preds _ ff) : @form Σ_funcs extended_preds _ falsity_off :=
    match phi with
    | falsity => Q
    | atom P v => dn Q (@atom _ _ _ falsity_off (old_preds P) v)
    | bin Impl phi psi => (Fr phi) ~> (Fr psi)
    | bin Conj phi psi => (Fr phi) ∧ (Fr psi)
    | bin Disj phi psi => dn Q ((Fr phi) ∨ (Fr psi))
    | quant All phi => ∀ (Fr phi)
    | quant Ex phi => dn Q (∃ (Fr phi))
    end.
  
  Definition Fr_ {ff} Gamma := map (@Fr ff) Gamma.
  
  Fact subst_Fr {ff} (phi : @form Σ_funcs Σ_preds _ ff) sigma:
    subst_form sigma (Fr phi) = Fr (subst_form sigma phi).
  Proof.
    revert sigma.
    induction phi; cbn.
    - reflexivity.
    - now unfold dn. 
    - destruct b0; cbn; unfold dn, Q; congruence.
    - destruct q; cbn; intros sigma; unfold dn, Q; congruence.
  Qed.

  Fact subst_Fr_ {ff} L sigma :
    map (subst_form sigma) (map (@Fr ff) L) = map Fr (map (subst_form sigma) L).
  Proof.
    induction L.
    - reflexivity.
    - cbn. now rewrite IHL, subst_Fr.
  Qed.
      

  Lemma double_dn Gamma F phi :
    Gamma ⊢M dn F (dn F phi) ~> dn F phi.
  Proof.
    apply II, II. eapply IE with (phi0:= _ ~> _). { apply Ctx; firstorder. }
    apply II. apply IE with (phi0:= phi ~> F). all: apply Ctx; auto.
  Qed.

  Lemma rm_dn Gamma F alpha beta :
    (alpha :: Gamma) ⊢M beta -> (dn F alpha :: Gamma) ⊢I dn F beta.
  Proof.
    intros H.
    apply II. eapply IE with (phi:= _ ~> _). { apply Ctx; firstorder. }
    apply II. eapply IE with (phi:= beta). {apply Ctx; auto. }
    eapply Weak; [eassumption|auto].
  Qed.
      
  Lemma form_up_var0_invar {ff} (phi : @form _ _ _ ff) :
    phi[up ↑][$0..] = phi.
  Proof.
    cbn. repeat setoid_rewrite subst_comp.
    rewrite <-(subst_var phi) at 2.
    apply subst_ext. intros n. unfold funcomp. cbn.
    change ((up (fun x : nat => $(S x)) n)) with ($n`[up ↑]).
    rewrite subst_term_comp.
    apply subst_term_id. now intros [].
  Qed.                             
  
  Lemma dn_forall {F} Gamma phi :
    F[↑] = F -> Gamma ⊢M dn F (∀ phi) ~> ∀ dn F phi.
  Proof.
    intros HF.
    apply II. constructor. apply II. cbn.
    change ((∀ phi[up ↑])) with ((∀ phi)[↑]).
    rewrite !HF.
    eapply IE with (phi0:= _ ~> _). { apply Ctx; auto. }
    apply II. eapply IE with (phi0:= phi). { apply Ctx; auto. }
    cbn. rewrite <-form_up_var0_invar.
    apply AllE, Ctx; auto.
  Qed.

  Fixpoint exist_times' {ff} N (phi : form ff) :=
    match N with
      0 => phi
    | S n => ∃ exist_times' n phi
    end.
  
  Lemma exist_dn phi Gamma:
    Gamma ⊢M ((∃ (dn Q phi)) ~> dn Q (∃ phi)). 
  Proof.
    apply II, II. eapply ExE. {apply Ctx; auto. }
    cbn; fold Q. apply IE with (phi0:= phi ~> Q).
    {apply Ctx; auto. }
    apply II. eapply IE with (phi0:= ∃ _).
    {apply Ctx; auto. }
    eapply ExI. rewrite form_up_var0_invar.
    apply Ctx; auto.
  Qed.
  
  Lemma DNE_Fr {ff} :
    forall phi Gamma, Gamma ⊢M dn Q (Fr phi) ~> @Fr ff phi. 
  Proof.
    refine (size_ind size _ _). intros phi sRec.
    destruct phi; intros Gamma; unfold dn.
    - apply II. eapply IE; cbn. { apply Ctx; auto. }
      apply II, Ctx; auto.
    - apply double_dn.
    - destruct b0; cbn.
      + apply II, CI.
        * eapply IE. apply sRec; cbn. 1: lia.
          apply rm_dn. eapply CE1, Ctx; auto.
        * eapply IE. apply sRec; cbn. 1: lia.
          apply rm_dn. eapply CE2, Ctx; auto.
      + apply double_dn.
      + apply II, II. eapply IE. apply sRec; cbn. 1: lia.
        apply II. eapply IE with (phi:= _ ~> _). { apply Ctx; auto. }
        apply II. eapply IE with (phi:= Fr phi2). { apply Ctx; auto. }
        eapply IE with (phi:= Fr phi1); apply Ctx; auto.
    - destruct q.      
      + cbn. apply II. apply IE with (phi0:= ∀ dn Q (Fr phi)).
        { apply II. constructor. cbn; fold Q.
          eapply IE. apply sRec; auto.
          rewrite <-form_up_var0_invar.
          apply AllE, Ctx; auto. }
        constructor.
        cbn; fold Q. rewrite <- form_up_var0_invar.
        apply AllE. cbn; fold Q.
        now apply imps, dn_forall.
      + apply double_dn.
  Qed.
  
  Lemma Peirce_Fr {ff} Gamma phi psi : Gamma ⊢M @Fr ff (((phi ~> psi) ~> phi) ~> phi).
  Proof.
    eapply IE. apply DNE_Fr. cbn.
    apply II. eapply IE. { apply Ctx; auto. }
    apply II. eapply IE. { apply Ctx; auto. }
    apply II. eapply IE. apply DNE_Fr. cbn; fold Q.
    apply II. eapply IE with (phi0:= _ ~> _). {apply Ctx; auto. }
    apply II, Ctx; auto.
  Qed.
    
  
  Lemma Fr_cl_to_min {ff} Gamma phi  :
    Gamma ⊢C phi -> (@Fr_ ff Gamma) ⊢M Fr phi.
  Proof.
    intros H. induction H; unfold Fr_ in *; cbn in *.
    - now constructor.
    - econstructor; eassumption.
    - constructor. now rewrite subst_Fr_.
    - eapply AllE with (t0:=t) in IHprv.
      now rewrite subst_Fr in IHprv. 
    - apply II.
      eapply IE.
      + apply Ctx. firstorder.
      + apply Weak with (A0 := map Fr A); [|auto].
        apply ExI with (t0:=t). now rewrite subst_Fr.
    - eapply IE. apply DNE_Fr. unfold dn in *; cbn.
      apply II. eapply IE.
      { eapply Weak; [apply IHprv1|auto]. }
      apply II. eapply IE. { apply Ctx; auto. }
      rewrite <-subst_Fr, <-subst_Fr_ in IHprv2.
      eapply ExE. { apply Ctx; auto. }
      cbn. eapply Weak; [apply IHprv2|auto].
    - specialize (DNE_Fr phi (map Fr A)) as H'.
      eapply IE; [eassumption|].
      cbn; apply II. eapply Weak; eauto.
    - now apply Ctx, in_map.
    - now apply CI.
    - eapply CE1; eauto.
    - eapply CE2; eauto.
    - apply II. eapply IE.
      + apply Ctx. auto.
      + apply DI1. eapply Weak; eauto.
    - apply II. eapply IE.
      + apply Ctx; auto.
      + apply DI2. eapply Weak; eauto.
    - eapply IE. apply DNE_Fr.
      apply II. eapply IE.
      { eapply Weak; [apply IHprv1|auto]. }
      apply II. eapply IE. { apply Ctx; auto. }
      apply imps in IHprv2. apply imps in IHprv3.
      eapply DE.
      1 : apply Ctx; firstorder.
      1,2 : apply imps; eapply Weak; [eassumption|auto].
    - apply Peirce_Fr.
  Qed.
  
End Signature.



Section FA.

  From Undecidability.FOL.Util Require Import FA_facts.
  From Undecidability.FOL.Reductions Require Import H10p_to_FA.
  From Undecidability.H10 Require Import H10p.
  Require Import Undecidability.FOL.PA.

  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  Existing Instance falsity_on.

  
  (* For every H10 problem we define an interpretation, where the new symbol Q is interpretated as the satisfaction of the H10 porblem in the standard model and everything else is interpreted as in the standard model. *)
  Definition interp_nat_H10p (E : H10p_PROBLEM) (rho : env nat) :
    @interp PA_funcs_signature extended_preds nat.
  Proof.
    split.
    - exact (@i_func _ _ _ interp_nat).
    - destruct P eqn:?.
      + intros _. exact (sat interp_nat rho (embed E)).
      + destruct P0. intros v. exact (@i_atom _ _ _ interp_nat Eq v).
  Defined.      


  Lemma Fr_exists_eq N s t (I : @interp PA_funcs_signature extended_preds nat) :
    forall rho, sat I rho (Fr (exist_times N (s == t))) <-> rho ⊨ (dn Friedman.Q (cast (exist_times N (s == t)))).
  Proof.
    induction N; cbn; intros ?.
    - tauto.
    - setoid_rewrite IHN. firstorder.
  Qed.
  
  Lemma extended_sat_eq N s t E rho sigma:
    sat (interp_nat_H10p E sigma) rho (cast (exist_times N (s == t))) -> sat interp_nat rho (exist_times N (s == t)).
  Proof.
    revert rho sigma. induction N.
    - tauto.
    - cbn. intros rho sigma [d Hd]. exists d.
      eapply IHN. unfold exist_times. apply Hd.
  Qed.
  

  Theorem Name (E : H10p_PROBLEM) :
    FAeq ⊢C embed E -> FAeq ⊢I embed E.
  Proof.
    intros H % Fr_cl_to_min % soundness.
    apply H10p_to_FA_prv, nat_H10. intros rho.
    specialize (H nat (interp_nat_H10p E rho)).
    refine (let H' := H rho _ in _).
    unfold embed, embed_problem in H'; destruct E as [a b].
    apply Fr_exists_eq in H'.
    simpl in H'. apply H'.
    apply extended_sat_eq.
    Unshelve.
    clear H. cbn -[Fr]. intros ? H.
    repeat (destruct H as [<-|H]); cbn; intuition.
  Qed.
  

End FA.
