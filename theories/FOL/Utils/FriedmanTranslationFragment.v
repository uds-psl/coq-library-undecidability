(** ** Eliminating excluded middle *)

Require Import List Lia.

From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationFacts ListAutomationInstances.
From Undecidability.FOL Require Import FragmentSyntax.
Import Vector.VectorNotations.
From Undecidability Require Import Synthetic.Undecidability.

Notation "I ⊨= phi" := (forall rho, sat I rho phi) (at level 20).
Notation "I ⊨=T T" := (forall psi, T psi -> I ⊨= psi) (at level 20).
Notation "I ⊫= Gamma" := (forall rho psi, In psi Gamma -> sat I rho psi) (at level 20).

Section Signature.
  Import FragmentSyntax.
  Existing Instance frag_operators | 0.
  
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

  (* Friedman translation *)
  Fixpoint Fr {ff} (phi : @form Σ_funcs Σ_preds _ ff) : @form Σ_funcs extended_preds _ falsity_off :=
    match phi with
    | falsity => Q
    | atom P v => dn Q (@atom _ _ _ falsity_off (old_preds P) v)
    | bin Impl phi psi => (Fr phi) → (Fr psi)
    | quant All phi => ∀ (Fr phi)
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
    Gamma ⊢M (dn F (dn F phi) → dn F phi).
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
    eapply Weak. 1:eassumption. apply cons_incl_proper, incl_tl, incl_tl, incl_refl.
  Qed.
      
  Lemma form_up_var0_invar {ff} (phi : @form _ _ _ ff) :
    phi[up ↑][$0..] = phi.
  Proof.
    asimpl. reflexivity.
  Qed.
  
  Lemma dn_forall {F} Gamma phi :
    F[↑] = F -> Gamma ⊢M (dn F (∀ phi) → ∀ dn F phi).
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

  Ltac try_lr := let rec H f := match f with S ?n => (try now left); right; H n | _ => idtac end in H 100.

  Lemma DNE_Fr {ff} :
    forall phi Gamma, Gamma ⊢M (dn Q (Fr phi) → @Fr ff phi). 
  Proof.
    refine (@size_ind _ size _ _). intros phi sRec.
    destruct phi; intros Gamma; unfold dn.
    - apply II. eapply IE; cbn. { apply Ctx; auto. now left. }
      apply II, Ctx; auto. now left.
    - apply double_dn.
    - destruct b0; cbn.
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
    - specialize (DNE_Fr phi (map Fr A)) as H'.
      eapply IE; [eassumption|].
      cbn; apply II. eapply Weak; eauto. apply incl_tl, incl_refl.
    - now apply Ctx, in_map.
    - apply Peirce_Fr.
  Qed.

  Lemma bounded_Fr {ff : falsity_flag} N ϕ :
    bounded N ϕ -> bounded N (Fr ϕ).
  Proof.
    induction 1; cbn; solve_bounds; auto.
    - econstructor; apply H.
    - destruct binop; now solve_bounds.
    - destruct quantop; now solve_bounds.
  Qed.
End Signature.