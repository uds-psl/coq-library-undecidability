Require Import List Lia.
From Undecidability.FOL.Util Require Import Syntax Syntax_facts FullTarski FullTarski_facts FullDeduction_facts FullDeduction.
Import Vector.VectorNotations.

Section Signature.

  
 (* Assume some signature and corresponding arity functions *)
 Context {Σ_funcs : funcs_signature}.
 Context {Σ_preds : preds_signature}.
 
 Variable Σ_funcs_ar : Σ_funcs -> nat.
 Variable Σ_preds_ar : Σ_preds -> nat.

 
Section Expanded.

  (* Add one more 0-ary predicate (i.e. propositional variable) to the predicates *)
  Inductive new_preds : Type :=
    Q_ : new_preds
  | old_preds (P : Σ_preds) : new_preds. 

  Definition new_preds_ar (P : new_preds) :=
    match P with
    | Q_ => 0
    | old_preds P => Σ_preds_ar P
    end.

  Instance funcs_signature : funcs_signature :=
    {| syms := Σ_funcs ; ar_syms := Σ_funcs_ar |}.

  Instance preds_signature : preds_signature :=
    {| preds := new_preds ; ar_preds := new_preds_ar |}.


  Definition Q {ff} := (@atom funcs_signature preds_signature _ ff Q_ ([])).
  Definition dnQ {ff} phi : form := (phi ~> @Q ff) ~> Q.

  Fixpoint Friedman {ff} (phi : @form funcs_signature preds_signature _ ff) : form ff :=
    match phi with
    | falsity => Q
    | atom P v => match P with Q_ => Q | _ => dnQ (atom P v) end
    | bin Impl phi psi => (Friedman phi) ~> (Friedman psi)
    | bin Conj phi psi => (Friedman phi) ∧ (Friedman psi)
    | bin Disj phi psi => dnQ ((Friedman phi) ∨ (Friedman psi))
    | quant All phi => ∀ (Friedman phi)
    | quant Ex phi => dnQ (∃ (Friedman phi))
    end.

                      
  Notation "'Fr' f" := (Friedman f) (at level 30).
  
  Definition List_Fr {ff} Gamma := map (@Friedman ff) Gamma.
  
  Lemma subst_Fr {ff} (phi : @form funcs_signature preds_signature _ ff) sigma:
    subst_form sigma (Fr phi) = Fr (subst_form sigma phi).
  Proof.
    revert sigma.
    induction phi; cbn.
    - reflexivity.
    - destruct P; reflexivity.
    - destruct b0; cbn; unfold dnQ, Q; congruence.
    - destruct q; cbn; intros sigma; unfold dnQ, Q; congruence.
  Qed.
  
  
  Lemma DNE_Q {ff} Gamma phi : Gamma ⊢I Fr (dnQ phi) ~> @Friedman ff phi. 
  Proof. Admitted.

  
  Lemma Friedman_cl_to_intu {ff} Gamma phi :
    Gamma ⊢C phi -> (List_Fr Gamma) ⊢I @Friedman ff phi.
  Proof.
    intros H. induction H; unfold List_Fr in *.
    - cbn. now constructor.
    - econstructor; eassumption.
    - cbn. constructor. admit.
    - cbn in *. eapply AllE with (t0:=t) in IHprv.
      cbn in *. now rewrite subst_Fr in IHprv. 
    - cbn. apply II.
      eapply IE.
      + apply Ctx. firstorder.
      + apply Weak with (A0 := map Friedman A); [|firstorder].
        apply ExI with (t0:=t). now rewrite subst_Fr.
    - admit.
    - cbn in *.
      specialize (DNE_Q (map Friedman A) phi) as H'.
      eapply IE; [eassumption|].
      cbn; apply II. eapply Weak; eauto.
    - now apply Ctx, in_map.
    - cbn. now apply CI.
    - cbn in *. eapply CE1; eauto.
    - cbn in *. eapply CE2; eauto.
    - cbn. apply II. eapply IE.
      + apply Ctx. firstorder.
      + apply DI1. eapply Weak; eauto.
    - cbn. apply II. eapply IE.
      + apply Ctx. firstorder.
      + apply DI2. eapply Weak; eauto.
    - cbn in *. admit.
    - specialize (DNE_Q (map Friedman A) (((phi ~> psi) ~> phi) ~> phi)) as H'.
      eapply IE; [eassumption|]. cbn. apply gen_peirce.
  Admitted.

    
End Expanded.
End Signature.
