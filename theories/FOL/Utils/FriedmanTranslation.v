(** ** Eliminating excluded middle *)

Require Import List Lia.

From Undecidability.FOL Require Import FullSyntax.
From Undecidability.FOL.Arithmetics Require Import Robinson NatModel.
Import Vector.VectorNotations.
From Undecidability Require Import Synthetic.Undecidability.

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
    (phi → F) → F.

  Fixpoint cast {ff} (phi : @form Σ_funcs Σ_preds _ ff) : @form Σ_funcs extended_preds _ falsity_off :=
    match phi with
    | falsity => Q
    | atom P v => (@atom _ _ _ falsity_off (old_preds P) v)
    | bin b phi psi => bin b (cast phi) (cast psi)
    | quant q phi => quant q (cast phi)
    end.

  (* Firedman translation *)
  Fixpoint Fr {ff} (phi : @form Σ_funcs Σ_preds _ ff) : @form Σ_funcs extended_preds _ falsity_off :=
    match phi with
    | falsity => Q
    | atom P v => dn Q (@atom _ _ _ falsity_off (old_preds P) v)
    | bin Impl phi psi => (Fr phi) → (Fr psi)
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
    Gamma ⊢M dn F (dn F phi) → dn F phi.
  Proof.
    apply II, II. eapply IE with (phi:= _ → _). { apply Ctx; firstorder. }
    apply II. apply IE with (phi:= phi → F). all: apply Ctx; cbv;eauto.
  Qed.

  Lemma rm_dn Gamma F alpha beta :
    (alpha :: Gamma) ⊢M beta -> (dn F alpha :: Gamma) ⊢I dn F beta.
  Proof.
    intros H.
    apply II. eapply IE with (phi:= _ → _). { apply Ctx; firstorder. }
    apply II. eapply IE with (phi:= beta). {apply Ctx; cbv;eauto. }
    eapply Weak. 1:eassumption. apply ListAutomation.incl_shift, incl_tl, incl_tl, incl_refl.
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
    F[↑] = F -> Gamma ⊢M dn F (∀ phi) → ∀ dn F phi.
  Proof.
    intros HF.
    apply II. constructor. apply II. cbn.
    change ((∀ phi[up ↑])) with ((∀ phi)[↑]).
    rewrite !HF.
    eapply IE with (phi:= _ → _). { apply Ctx; auto. right. left. easy. }
    apply II. eapply IE with (phi:= phi). { apply Ctx; auto. right. left. easy. }
    cbn. rewrite <-form_up_var0_invar.
    apply AllE, Ctx; auto. left. easy.
  Qed.

  Fixpoint exist_times' {ff} N (phi : form ff) :=
    match N with
      0 => phi
    | S n => ∃ exist_times' n phi
    end.
  
  Lemma exist_dn phi Gamma:
    Gamma ⊢M ((∃ (dn Q phi)) → dn Q (∃ phi)). 
  Proof.
    apply II, II. eapply ExE. {apply Ctx; auto. right. now left. }
    cbn; fold Q. apply IE with (phi:= phi → Q).
    {apply Ctx; auto. now left. }
    apply II. eapply IE with (phi:= ∃ _).
    {apply Ctx; auto. do 2 right. now left. }
    eapply ExI. rewrite form_up_var0_invar.
    apply Ctx; auto. now left.
  Qed.

  Ltac try_lr := let rec H f := match f with S ?n => (try now left); right; H n | _ => idtac end in H 100.

  Lemma DNE_Fr {ff} :
    forall phi Gamma, Gamma ⊢M dn Q (Fr phi) → @Fr ff phi. 
  Proof.
    refine (@size_ind _ size _ _). intros phi sRec.
    destruct phi; intros Gamma; unfold dn.
    - apply II. eapply IE; cbn. { apply Ctx; auto. now left. }
      apply II, Ctx; auto. now left.
    - apply double_dn.
    - destruct b0; cbn.
      + apply II, CI.
        * eapply IE. apply sRec; cbn. 1: lia.
          apply rm_dn. eapply CE1, Ctx; auto. now left.
        * eapply IE. apply sRec; cbn. 1: lia.
          apply rm_dn. eapply CE2, Ctx; auto. now left.
      + apply double_dn.
      + apply II, II. eapply IE. apply sRec; cbn. 1: lia.
        apply II. eapply IE with (phi:= _ → _). { apply Ctx; auto. try_lr. }
        apply II. eapply IE with (phi:= Fr phi2). { apply Ctx; auto. try_lr. }
        eapply IE with (phi:= Fr phi1); apply Ctx; auto. all: try_lr.
    - destruct q.
      + cbn. apply II. apply IE with (phi:= ∀ dn Q (Fr phi)).
        { apply II. constructor. cbn; fold Q.
          eapply IE. apply sRec; auto.
          rewrite <-form_up_var0_invar.
          apply AllE, Ctx; auto. try_lr. }
        constructor.
        cbn; fold Q. rewrite <- form_up_var0_invar.
        apply AllE. cbn; fold Q.
        now apply imps, dn_forall.
      + apply double_dn.
  Qed.
  
  Lemma Peirce_Fr {ff} Gamma phi psi : Gamma ⊢M @Fr ff (((phi → psi) → phi) → phi).
  Proof.
    eapply IE. apply DNE_Fr. cbn.
    apply II. eapply IE. { apply Ctx; auto. try_lr. }
    apply II. eapply IE. { apply Ctx; auto. try_lr. }
    apply II. eapply IE. apply DNE_Fr. cbn; fold Q.
    apply II. eapply IE with (phi:= _ → _). {apply Ctx; auto. try_lr. }
    apply II, Ctx; auto. try_lr.
  Qed.
    
  
  Theorem Fr_cl_to_min {ff} Gamma phi  :
    Gamma ⊢C phi -> (@Fr_ ff Gamma) ⊢M Fr phi.
  Proof.
    induction 1; unfold Fr_ in *; cbn in *.
    - now constructor.
    - econstructor; eassumption.
    - constructor. now rewrite subst_Fr_.
    - eapply AllE with (t:=t) in IHprv.
      now rewrite subst_Fr in IHprv. 
    - apply II.
      eapply IE.
      + apply Ctx. firstorder.
      + apply Weak with (A := map Fr A); [|apply incl_tl, incl_refl].
        apply ExI with (t:=t). now rewrite subst_Fr.
    - eapply IE. apply DNE_Fr. unfold dn in *; cbn.
      apply II. eapply IE.
      { eapply Weak; [apply IHprv1|auto]. apply incl_tl,incl_refl. }
      apply II. eapply IE. { apply Ctx; auto. try_lr. }
      rewrite <-subst_Fr, <-subst_Fr_ in IHprv2.
      eapply ExE. { apply Ctx; auto. try_lr. }
      cbn. eapply Weak; [apply IHprv2|auto]. apply ListAutomation.incl_shift, incl_tl, incl_tl, incl_refl.
    - specialize (DNE_Fr phi (map Fr A)) as H'.
      eapply IE; [eassumption|].
      cbn; apply II. eapply Weak; eauto. apply incl_tl, incl_refl.
    - now apply Ctx, in_map.
    - now apply CI.
    - eapply CE1; eauto.
    - eapply CE2; eauto.
    - apply II. eapply IE.
      + apply Ctx. auto. try_lr.
      + apply DI1. eapply Weak; eauto. apply incl_tl, incl_refl.
    - apply II. eapply IE.
      + apply Ctx; auto. try_lr.
      + apply DI2. eapply Weak; eauto. apply incl_tl, incl_refl.
    - eapply IE. apply DNE_Fr.
      apply II. eapply IE.
      { eapply Weak; [apply IHprv1|auto]. apply incl_tl, incl_refl. }
      apply II. eapply IE. { apply Ctx; auto. try_lr. }
      apply imps in IHprv2. apply imps in IHprv3.
      eapply DE.
      1 : apply Ctx; firstorder.
      1,2 : apply imps; eapply Weak; [eassumption|auto]; apply incl_tl, incl_tl, incl_refl.
    - apply Peirce_Fr.
  Qed.

  Lemma bounded_Fr {ff : falsity_flag} N ϕ :
    bounded N ϕ -> bounded N (Fr ϕ).
  Proof.
    induction 1; cbn; solve_bounds; auto.
    - destruct binop; now solve_bounds.
    - destruct quantop; now solve_bounds.
  Qed.

End Signature.


Section Arithmetic.

  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Lemma nat_sat_Fr_Q P :
    (extend_interp interp_nat P) ⊫= Fr_ Qeq.
  Proof.
    intros ρ a Qa.
    repeat (destruct Qa as [<-|Qa]).
    all: cbn -[FAeq]; try refine (fun A => let F := A _ rho in _); intuition.
    - apply H. intros ->. apply H0. intros ->. auto.
    - now apply H.
    - destruct d; eauto.
    - destruct Qa.
  Qed.

End Arithmetic.

