Require Import Undecidability.FOL.Utils.FriedmanTranslation.
Require Import Undecidability.FOL.Incompleteness.Axiomatisations.
Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.FOL.FullSyntax.
Require Import Undecidability.FOL.Arithmetics.Problems.
Require Import Undecidability.FOL.Arithmetics.Models.NatModel.
From Undecidability.Synthetic Require Import Definitions EnumerabilityFacts.
From Undecidability.FOL.Undecidability.Reductions Require Import H10p_to_FA.
From Undecidability.H10 Require Import H10p H10p_undec.
Require Import List Lia.
Section Arithmetic.

  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Section Model.

    Variable D : Type.
    Variable I : @interp PA_funcs_signature _ D.
    Variable ext_I : @interp PA_funcs_signature extended_preds D.

    Lemma Fr_exists_eq N s t :
      forall rho, sat ext_I rho (Fr (exist_times N (s == t))) <-> rho ⊨ (dn FriedmanTranslation.Q (cast (exist_times N (s == t)))).
    Proof.
      induction N; cbn; intros ?.
      - tauto.
      - setoid_rewrite IHN. firstorder.
    Qed.

    Corollary Fr_embed E :
      forall rho, sat ext_I rho (Fr (embed E)) <-> rho ⊨ (dn FriedmanTranslation.Q (cast (embed E))).
    Proof.
      unfold embed, embed_problem; destruct E as [a b].
      apply Fr_exists_eq.
    Qed.

    Definition ext_nat := extend_interp interp_nat.
    
    Lemma cast_extists_eq N s t P rho :
      sat (extend_interp I P) rho (cast (exist_times N (s == t))) -> sat rho (exist_times N (s == t)).
    Proof.
      revert rho. induction N.
      - tauto.
      - cbn. intros rho [d Hd]. exists d.
        eapply IHN. unfold exist_times. apply Hd.
    Qed.

    Corollary cast_embed E P rho :
      sat (extend_interp I P) rho (cast (embed E)) -> sat I rho (embed E).
    Proof.
      unfold embed, embed_problem; destruct E as [a b].
      apply cast_extists_eq.
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
    apply cast_embed. exact I.
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
    forall D (I : interp D) P, 
      I ⊨=T T -> 
      forall Gamma, (forall psi, In psi Gamma -> T psi) -> 
                    (extend_interp I P) ⊫= Fr_ Gamma.

  Section Theory.

    Variable T : form -> Prop.
    Variable Incl : Q' <<= T.
    Variable Std : 
      forall Gamma P, (forall psi, In psi Gamma -> T psi) -> (extend_interp interp_nat P) ⊫= Fr_ Gamma.
    
    Lemma extract_from_class E :
      T ⊢TC embed E -> interp_nat ⊨= embed E.
    Proof.
      intros [Gamma [H2 H % Fr_cl_to_min % soundness]] rho.
      refine (let H' := H nat (extend_interp interp_nat _) rho _ in _).
      apply Fr_embed in H'.
      simpl in H'. apply H'.
      apply cast_embed. exact interp_nat.
      Unshelve.
      now apply Std.
    Qed.
        
    Lemma reduction_theorem :
      reduction embed H10p (tprv_class T).
    Proof.
      intros E; split.
      - intros H % (@H10p_to_FA_prv' class).
        exists FAeq; split; [intros ?|auto].
        apply Incl.
      - intros H. apply nat_H10.
        now apply extract_from_class.
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
      apply H. eapply Std; eauto.
    Qed.
    
    Theorem incompleteness_Q :
      enumerable T -> complete T -> computational_explosion.
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
