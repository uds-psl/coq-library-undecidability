Require Import List Lia.
From Undecidability.FOL.Util Require Import Syntax Syntax_facts FullTarski FullTarski_facts FullDeduction_facts FullDeduction.
Import Vector.VectorNotations.

Notation "I ⊨= phi" := (forall rho, sat I rho phi) (at level 20).
Notation "I ⊨=T T" := (forall psi, T psi -> I ⊨= psi) (at level 20).
Notation "I ⊫= Gamma" := (forall rho psi, In psi Gamma -> sat I rho psi) (at level 20).

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


  Definition extend_interp {D} :
    @interp Σ_funcs Σ_preds D -> Prop -> interp D.
  Proof.
    intros I Q. split.
    - exact (@i_func _ _ _ I).
    - intros P. destruct P as [|P0] eqn:?.
      + intros _. exact Q.
      + exact (@i_atom _ _ _ I P0).
  Defined.
  

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

  Lemma sat_cast {ff : falsity_flag} D (I : interp Σ_funcs Σ_preds D) rho phi P :
    rho ⊨ phi <-> sat (@extend_interp D I P) rho (cast phi).
  Proof.
  Admitted.

  (* Firedman translation *)
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
    
  
  Theorem Fr_cl_to_min {ff} Gamma phi  :
    Gamma ⊢C phi -> (@Fr_ ff Gamma) ⊢M Fr phi.
  Proof.
    induction 1; unfold Fr_ in *; cbn in *.
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



From Undecidability.Synthetic Require Import Definitions Undecidability.
From Undecidability.FOL.Util Require Import FA_facts Axiomatisations.
From Undecidability.Synthetic Require Import Definitions EnumerabilityFacts.
From Undecidability.FOL.Reductions Require Import H10p_to_FA.
From Undecidability.H10 Require Import H10p H10p_undec.
Require Import Undecidability.FOL.PA.

Section Arithmetic.

  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Section Model.

    Variable D : Type.
    Variable I : @interp PA_funcs_signature _ D.
    Variable ext_I : @interp PA_funcs_signature extended_preds D.
    
    Lemma Fr_exists_eq N s t :
      forall rho, sat ext_I rho (Fr (exist_times N (s == t))) <-> rho ⊨ (dn Friedman.Q (cast (exist_times N (s == t)))).
    Proof.
      induction N; cbn; intros ?.
      - tauto.
      - setoid_rewrite IHN. firstorder.
    Qed.

    Corollary Fr_embed E :
      forall rho, sat ext_I rho (Fr (embed E)) <-> rho ⊨ (dn Friedman.Q (cast (embed E))).
    Proof.
      unfold embed, embed_problem; destruct E as [a b].
      apply Fr_exists_eq.
    Qed.

    Definition ext_nat := extend_interp interp_nat.
    
    Lemma extended_sat_eq N s t P rho :
      sat (extend_interp I P) rho (cast (exist_times N (s == t))) -> sat rho (exist_times N (s == t)).
    Proof.
      revert rho. induction N.
      - tauto.
      - cbn. intros rho [d Hd]. exists d.
        eapply IHN. unfold exist_times. apply Hd.
    Qed.

    Corollary extended_sat_embed E P rho :
      sat (extend_interp I P) rho (cast (embed E)) -> sat I rho (embed E).
    Proof.
      unfold embed, embed_problem; destruct E as [a b].
      apply extended_sat_eq.
    Qed.

    Lemma sat_Fr_formula {P} phi rho :
      I ⊨=T Q' -> Q' phi -> sat (extend_interp I P) rho (Fr phi).
    Proof.
      intros axioms H.
      specialize (axioms phi). revert axioms.
      repeat (destruct H as [<-|H]).
      all: cbn -[FAeq]; refine (fun A => let F := A _ rho in _); intuition.
      destruct H.
      Unshelve. all: cbn; try tauto.
    Qed.

    Lemma sat_Fr_context {P} Gamma rho :
      I ⊨=T Q' -> (forall psi : form, In psi Gamma -> Q' psi) -> (forall psi, In psi (Fr_ Gamma) -> sat (extend_interp I P) rho psi).
    Proof.
      intros axioms.
      induction Gamma as [| alpha Gamma IH]; cbn -[FAeq].
      - tauto.
      - intros H beta [<-| [phi [<- ]] % in_map_iff ].
        + specialize (H alpha (or_introl eq_refl)).
          now apply sat_Fr_formula.          
        + apply IH; [|now apply in_map].
          intros psi Hp. apply H; tauto.
    Qed.
    
  End Model.
  
  
  Theorem sat_embed Gamma (E : H10p_PROBLEM) D (I : interp D) :
    I ⊨=T Q' -> (forall psi : form, In psi Gamma -> Q' psi) -> Gamma ⊢C embed E -> I ⊨= embed E.
  Proof.
    intros HI Hg H % Fr_cl_to_min % soundness rho.
    refine (let H' := H D (extend_interp I _) rho _ in _).
    apply Fr_embed in H'.
    simpl in H'. apply H'.
    apply extended_sat_embed. exact I.
    Unshelve.
    apply sat_Fr_context; auto.
  Qed.
    
  Theorem class_Q_to_H10p Gamma (E : H10p_PROBLEM) :
    (forall psi : form, In psi Gamma -> Q' psi) -> Gamma ⊢C embed E -> H10p E.
  Proof.
    intros Hg H. apply nat_H10.
    eapply sat_embed; eauto.
    clear H; intros alpha H rho.
    repeat (destruct H as [<-|H]; cbn; intuition).
    destruct H.
  Qed.

  Corollary T_class_Q_to_H10p (T : form -> Prop) (E : H10p_PROBLEM) :
    T <<= Q' -> T ⊢TC embed E -> H10p E.
  Proof.
    intros ? [Gamma []]. eapply class_Q_to_H10p; intuition.
  Qed.

  Lemma H10p_to_class_Q :
    reduction embed H10p (tprv_class Q').
  Proof.
    intros E; split.
    + intros H. exists FAeq. split; [intuition|].
      now apply H10p_to_FA_prv'.
    + intros H. eapply T_class_Q_to_H10p.
      2 : apply H. auto.
   Qed.

  Lemma undec_class_Q :
    undecidable (tprv_class Q').
  Proof.
    refine (undecidability_from_reducibility _ _).
    2 : exists embed; apply H10p_to_class_Q.
    apply H10p_undec.
  Qed.
  
  
  Definition Fr_pres T :=
    forall D (I : interp D) P, I ⊨=T T -> forall Gamma, (forall psi, In psi Gamma -> T psi) -> (extend_interp I P) ⊫= Fr_ Gamma.

  Section Theory.

    Variable T : form -> Prop.
    Variable Incl : Q' <<= T.
    Variable Std : interp_nat ⊨=T T.
    Variable Pres : Fr_pres T.
    
    Lemma reduction_theorem :
      reduction embed H10p (tprv_class T).
    Proof.
      intros E; split.
      - intros H % (@H10p_to_FA_prv' class).
        exists FAeq; split; [intros ?|auto].
        apply Incl.
      - intros [Gamma [H2 H % Fr_cl_to_min % soundness]].
        apply nat_H10. intros rho.
        specialize (H _ (ext_nat (sat interp_nat rho (embed E))) rho).
        apply Fr_embed in H.
        + simpl in H. apply H.
          apply extended_sat_embed.
        + exact interp_nat.
        + eapply Pres; eauto.
    Qed.  

    Lemma undec_class_T :
      undecidable (tprv_class T).
    Proof.
      refine (undecidability_from_reducibility H10p_undec _).
      exists embed. apply reduction_theorem.
    Qed.
    
    Lemma std_T_consistent :
      ~ T ⊢TC ⊥.
    Proof.
      intros [Gamma [H2 H % Fr_cl_to_min % soundness]].
      specialize (H nat (ext_nat False) (fun _ => 0)).
      apply H. eapply Pres; eauto.
    Qed.
    
    Theorem incompleteness_Q :
      enumerable T -> complete T -> decidable (TM.HaltTM 1).
    Proof.
      intros HE HC. apply H10p_undec.
      apply (@complete_reduction _ _ enum_PA_syms _ enum_PA_preds _ T HE) with embed.
      - now apply std_T_consistent.
      - apply HC.
      - now apply reduction_theorem.
      - apply embed_is_closed.
    Qed.

  End Theory.
  
End Arithmetic.



(* Failed attempt to verify Friedman translation for ZF *)

From Undecidability.FOL Require Import ZF Reductions.PCPb_to_ZF Reductions.PCPb_to_ZF.
From Undecidability.FOL.Util Require Import FullDeduction.

Lemma Fr_combinations D (I : @interp ZF_func_sig (@extended_preds ZF_pred_sig) D) x y z :
  forall rho, rho ⊨ (Fr (combinations x y z)) <-> rho ⊨ (dn Friedman.Q (cast (combinations x y z))).
Proof.
Admitted.

Lemma M_combinations_equiv D (I : @interp ZF_func_sig ZF_pred_sig D) rho B a b :
  extensional I -> M_combinations B (eval rho $a) (eval rho $b) <-> rho ⊨ combinations B $a $b.
Proof.
  intros HI. induction B as [|[s t] B IH]; cbn.
  - rewrite HI. reflexivity.
  - admit.
Admitted.

Lemma Fr_solvable D (I : @interp ZF_func_sig (@extended_preds ZF_pred_sig) D) B :
  forall rho, rho ⊨ (Fr (solvable B)) <-> rho ⊨ (dn Friedman.Q (cast (solvable B))).
Proof.
  intros rho. cbn. setoid_rewrite (Fr_combinations). cbn. intuition.
Admitted.

Theorem ZF_Friedman' B :
  ZFeq' ⊢C (solvable B) -> entailment_ZFeq' (solvable B).
Proof.
  intros H % Fr_cl_to_min % soundness. intros D I rho HI.
  specialize (H D (extend_interp I (rho ⊨ solvable B)) rho).
  rewrite Fr_solvable in H. cbn in H. apply H.
  - admit.
  - clear H. cbn. setoid_rewrite <- (sat_cast D I). tauto.
Admitted.

Theorem ZF_Friedman B :
  ZFeq' ⊢C (solvable B) -> entailment_ZFeq' (solvable B).
Proof.
  intros H % Fr_cl_to_min % soundness. intros D I rho HI.
  specialize (H D (extend_interp I (rho ⊨ solvable B)) rho). cbn in H.
  apply H.
  - admit.
  - clear H. cbn. setoid_rewrite (Fr_combinations). cbn.
    setoid_rewrite <- (sat_cast D I). cbn.

    (*setoid_rewrite (@eval_enc_stack D I).
    setoid_rewrite <- (M_combinations_equiv I).*)
Abort.
