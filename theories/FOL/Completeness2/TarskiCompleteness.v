From Undecidability.FOL Require Import Syntax.Facts Deduction.FragmentNDFacts Syntax.Theories Semantics.Tarski.FragmentFacts Semantics.Tarski.FragmentSoundness.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation Shared.Dec.
From Undecidability Require Import Shared.Libs.PSL.Vectors.Vectors Shared.Libs.PSL.Vectors.VectorForall.
Import ListAutomationNotations.
From Undecidability.FOL.Completeness2 Require Export TarskiConstructions.
(** ** Completeness *)

(* ** Standard Models **)

Section Completeness.
  Context {Σf : funcs_signature} {Σp : preds_signature}.
  Context {HdF : eq_dec Σf} {HdP : eq_dec Σp}.
  Variable eF : nat -> option Σf.
  Context {HeF : enumerator__T eF Σf}.
  Variable eP : nat -> option Σp.
  Context {HeP : enumerator__T eP Σp}.

  #[local] Hint Constructors bounded : core.

  Section BotModel.
    #[local] Existing Instance falsity_on | 0.
    Variable T : theory.
    Hypothesis T_closed : closed_T T.
    Hypothesis Hcon : consistent class T.

    Definition list_enum_to_enum {X} (L : nat -> list X) (n : nat) : option X :=
      let (n, m) := Cantor.of_nat n in nth_error (L n) m.

    Definition form_list_enum := (@L_form _ _ _
                                  _ (enumerator__T_of_list HeF) _ (enumerator__T_of_list HeP)
                                  _ enum_frag_logic_binop _ enum_frag_logic_quant).

    Definition form_list_enum_bounded {ff:falsity_flag} (n:nat) : list form := 
      (flat_map (fun f => if bounded_dec f n then [f] else []) (form_list_enum ff n)).

    Lemma form_list_is_enum {ff:falsity_flag} : list_enumerator__T (form_list_enum ff) _.
    Proof.
      apply enum_form.
    Qed.

    Lemma form_list_bounded_is_enum {ff:falsity_flag} : list_enumerator__T (@form_list_enum_bounded ff) _.
    Proof.
      intros f. destruct (form_list_is_enum f) as [m Hm].
      destruct (find_bounded f) as [m2 Hm2].
      exists (max m m2).
      unfold form_list_enum_bounded. eapply in_flat_map. exists f; split.
      - unfold form_list_enum. eapply cum_ge'. 1: apply L_form_cml. 1: apply Hm. lia.
      - destruct bounded_dec as [Hl|Hr]. 1:now left. exfalso. apply Hr. eapply bounded_up. 1: apply Hm2. lia.
    Qed.

    Definition form_enum_with_default {ff} d n := match list_enum_to_enum (@form_list_enum_bounded ff) n with Some k => k | _ => d end.

    Lemma form_default_is_enum {ff:falsity_flag} d : forall f, exists n, (@form_enum_with_default ff d n) = f.
    Proof.
      intros f. destruct (form_list_bounded_is_enum f) as [m Hm].
      unfold form_enum_with_default, list_enum_to_enum.
      destruct (In_nth_error _ _ Hm) as [n Hn].
      exists (Cantor.to_nat (m, n)). rewrite Cantor.cancel_of_to.
      rewrite Hn. easy.
    Qed.

    Lemma form_default_is_bounded {ff:falsity_flag} d : bounded 0 d -> forall n, bounded n (@form_enum_with_default ff d n).
    Proof.
      intros Hb n.
      unfold form_enum_with_default, list_enum_to_enum.
      destruct (Cantor.of_nat n) as [n' m'] eqn:Hn.
      pose proof (Cantor.to_nat_non_decreasing n' m'). rewrite <- Hn in H.
      rewrite Cantor.cancel_to_of in H.
      unfold form_list_enum_bounded.
      generalize (form_list_enum ff n'); intros l.
      destruct (nth_error _ _) as [k|] eqn:Heq.
      2: eapply bounded_up; [apply Hb|lia].
      apply nth_error_In in Heq.
      apply in_flat_map in Heq.
      destruct Heq as [x [Hx1 Hx2]].
      destruct (bounded_dec x n') as [Hbo|]. 2:easy.
      destruct Hx2 as [->|[]]. eapply bounded_up. 1: apply Hbo. lia.
    Qed.


    Definition input_bot : ConstructionInputs :=
      {|
        NBot := ⊥ ;
        NBot_closed := bounded_falsity 0;

        variant := falsity_on ;

        In_T := T ;
        In_T_closed := T_closed ;
        TarskiConstructions.enum := form_enum_with_default ⊥;
        TarskiConstructions.enum_enum := form_default_is_enum _;
        TarskiConstructions.enum_bounded := form_default_is_bounded (bounded_falsity _)
      |}.

    Definition output_bot := construct_construction input_bot.

    Instance model_bot : interp term :=
      {| i_func := func; i_atom := fun P v => atom P v ∈ Out_T output_bot|}.

    Lemma eval_ident rho (t : term) :
      eval rho t = subst_term rho t.
    Proof.
      induction t in rho|-*.
      - easy.
      - cbn. easy.
    Qed.

    Lemma help5 phi t sigma :
      phi[up sigma][t..] = phi[t.:sigma].
    Proof.
      rewrite subst_comp. apply subst_ext. intros [|]; cbn; trivial. unfold funcomp.
      rewrite subst_term_comp. apply subst_term_id. now intros [].
    Qed.

    Lemma model_bot_correct phi rho :
      (phi[rho] ∈ Out_T output_bot <-> rho ⊨ phi).
    Proof.
      revert rho. induction phi using form_ind_falsity; intros rho. 1,2,3: cbn.
      - split; try tauto. intros H. apply Hcon.
        apply Out_T_econsistent with output_bot. exists [⊥]. split; try apply Ctx. 2: now left. intros a [<-|[]]; easy.
      - erewrite (Vector.map_ext_in _ _ _ (eval rho)). 1:easy.
        easy.
      - destruct b0. rewrite <- IHphi1. rewrite <- IHphi2. apply Out_T_impl.
      - destruct q. cbn. setoid_rewrite <- IHphi. setoid_rewrite Out_T_all.
        setoid_rewrite help5. easy.
    Qed.

    Lemma model_bot_classical :
      classical model_bot.
    Proof.
      intros rho phi psi. apply model_bot_correct, Out_T_prv.
      use_theory (nil : list form). apply Pc.
    Qed.

    Lemma valid_T_model_bot phi :
      phi ∈ T -> var ⊨ phi.
    Proof.
      intros H % (Out_T_sub output_bot). apply model_bot_correct. now rewrite subst_id.
    Qed.
  End BotModel.

  Section StandardCompletenes.
    Variables (T : @theory _ _ _ falsity_on) (phi : @form _ _ _ falsity_on).
    Hypothesis (HT : closed_T T) (Hphi : closed phi).

    Lemma semi_completeness_standard :
      valid_theory T phi -> ~ ~ T ⊢TC phi.
    Proof.
      intros Hval Hcons. rewrite refutation_prv in Hcons. 
      assert (Hcl : closed_T (T ⋄ (¬ phi))) by (apply closed_T_extend; try econstructor; eauto).
      unshelve eapply (model_bot_correct (T_closed := Hcl) Hcons (¬ phi) var).
      - apply Out_T_sub. cbn. right. now rewrite subst_id.
      - apply Hval. intros ? ?. apply valid_T_model_bot; intuition.
    Qed.

    Definition stable P := ~~P -> P.

    Lemma completeness_standard_stability :
      stable (T ⊢TC phi) -> valid_theory T phi -> T ⊢TC phi.
    Proof.
      intros Hstab Hsem. now apply Hstab, semi_completeness_standard.
    Qed.

    Lemma completeness_standard_stability' :
      (valid_theory_C (classical (ff := falsity_on)) T phi -> T ⊢TC phi) -> stable (T ⊢TC phi).
    Proof.
      intros Hcomp Hdn. apply Hcomp.
      intros D I rho Hclass Hsat. unfold classical in Hclass. cbn in Hclass.
      eapply (Hclass _ _ ⊥). intros Hsat2. exfalso. apply Hdn. intros [A [HA Hc]]. apply Hsat2.
      eapply sound_for_classical_model.
      - easy.
      - exact Hc.
      - intros a Ha. apply Hsat. apply HA, Ha.
    Qed.
  End StandardCompletenes. (*

  Section MPStrongCompleteness.
    Hypothesis mp : MP.
    Variable (T : theory) (phi : form) (L : nat -> list form).
    Hypothesis (HT : closed_T T) (Hphi : closed phi).
    Hypothesis (He : DecidableEnumerable.enum T L).

    Lemma mp_tprv_stability {p : peirce} {b : bottom} :
      ~ ~ T ⊩ phi -> T ⊩ phi.
    Proof.
      apply (enumeration_stability mp (enum_tprv He) (dec_form HdF HdP)).
    Qed.

    Lemma mp_standard_completeness :
      T ⊫S phi -> T ⊢TC phi.
    Proof.
      intros Hprv % semi_completeness_standard. 2,3: assumption.
      now apply mp_tprv_stability.
    Qed.
  End MPStrongCompleteness.

(* *** Exploding Models **)

  Section ExplodingCompletenes.
    Variables (T : theory) (phi : form).
    Hypothesis (HT : closed_T T) (Hphi : closed phi).

    Lemma completeness_expl :
      T ⊫E phi -> T ⊢TC phi.
    Proof.
      intros Hval. assert (Hcl : closed_T (T ⋄ (¬ phi))) by (intros ? ? [] ; subst; eauto).
      apply refutation_prv. apply (@Out_T_econsistent _ _ (output_bot Hcl)); cbn. use_theory [⊥]. 2: ctx.
      intros ? [<- | []]. apply (model_bot_correct _ ⊥ ids).
      specialize (Hval term (model_bot Hcl) (model_bot_exploding Hcl) ids).
      assert (@sat _ _ (model_bot Hcl) ids (¬ phi)) by (apply model_bot_correct, Out_T_sub; comp; firstorder).
      apply H, Hval. intros ? ?. apply valid_T_model_bot; intuition.
    Qed.

    Lemma valid_standard_expld_stability :
      (T ⊫S phi -> T ⊫E phi) <-> stable (T ⊢TC phi).
    Proof.
      rewrite <- completeness_standard_stability. 2,3: assumption. split.
      - intros Hincl Hval % Hincl. now apply completeness_expl.
      - intros Hcomp Hprv % Hcomp. apply (StrongSoundness Hprv).
        all: now intros _ ? ? [].
    Qed.
  End ExplodingCompletenes.

(* *** Minimal Models **)

  Section FragmentModel.
    Variable T : theory.
    Hypothesis T_closed : closed_T T.

    Variable GBot : form.
    Hypothesis GBot_closed : closed GBot.

    Definition input_fragment :=
      {|
        NBot := GBot ;
        NBot_closed := GBot_closed ;

        variant := lconst ;

        In_T := T ;
        In_T_closed := T_closed ;

        GenConstructions.enum := form_enum ;
        enum_enum := form_enum_enumerates ;
        enum_unused := form_enum_fresh
      |}.

    Definition output_fragment := construct_construction input_fragment.

    Instance model_fragment : interp term :=
      {| i_f := Func; i_P := fun P v => Pred P v ∈ Out_T output_fragment ;
        i_F := ⊥ ∈ Out_T output_fragment |}.

    Lemma eval_ident_fragment rho (t : term) :
      eval rho t = subst_term rho t.
    Proof.
      induction t using strong_term_ind; comp; asimpl; try congruence. f_equal.
    Qed.

    Lemma model_fragment_correct phi rho :
      (phi[rho] ∈ Out_T output_fragment <-> rho ⊨ phi).
    Proof.
      induction phi in rho |-*. 1,2,3: comp.
      - tauto.
      - now rewrite <- (vec_ext (fun x => eval_ident_fragment rho x)).
      - rewrite <-IHphi1, <-IHphi2. now apply Out_T_impl.
      - cbn. setoid_rewrite <-IHphi. rewrite Out_T_all.
        split; intros H d; specialize (H d); comp; now asimpl in H.
    Qed.

    Lemma model_fragment_classical :
      BLM model_fragment.
    Proof.
      intros rho phi psi. apply model_fragment_correct, Out_T_prv.
      use_theory (nil : list form). apply Pc.
    Qed.

    Lemma valid_T_fragment phi :
      phi ∈ T -> ids ⊨ phi.
    Proof.
      intros H % (Out_T_sub output_fragment). apply model_fragment_correct; now comp.
    Qed.
  End FragmentModel.

  Section FragmentCompleteness.

    Lemma semi_completeness_fragment T phi :
      closed_T T -> closed phi -> T ⊫M phi -> T ⊩CL phi.
    Proof.
      intros HT Hphi Hval. replace phi with (phi[ids]) in * by now comp.
      apply (@Out_T_econsistent _ _ (output_fragment HT Hphi)); cbn. use_theory [phi[ids]]. 2: ctx.
      intros ? [<- | []]. apply (model_fragment_correct HT Hphi phi ids). comp. rewrite instId_form in Hval.
      apply Hval. 1: apply model_fragment_classical. intros ? ?. apply valid_T_fragment; intuition.
    Qed.
  End FragmentCompleteness. *)
End Completeness.

(* ** Extending the Completeness Results *)
(*
Section FiniteCompleteness.
  Context {Sigma : Signature}.
  Context {HdF : eq_dec Funcs} {HdP : eq_dec Preds}.
  Context {HeF : enumT Funcs} {HeP : enumT Preds}.

  Lemma list_completeness_standard A phi :
    ST__f -> valid_L SM A phi -> A ⊢CE phi.
  Proof.
    intros stf Hval % valid_L_to_single. apply prv_from_single.
    apply con_T_correct. apply completeness_standard_stability.
    1: intros ? ? []. 1: apply close_closed. 2: now apply valid_L_valid_T in Hval.
    apply stf, fin_T_con_T.
    - intros ? ? [].
    - eapply close_closed.
  Qed.

  Lemma list_completeness_expl A phi :
    valid_L EM A phi -> A ⊢CE phi.
  Proof.
    intros Hval % valid_L_to_single. apply prv_from_single.
    apply tprv_list_T. apply completeness_expl. 1: intros ? ? [].
    1: apply close_closed. now apply valid_L_valid_T in Hval.
  Qed.

  Lemma list_completeness_fragment A phi :
    valid_L BLM A phi -> A ⊢CL phi.
  Proof.
    intros Hval % valid_L_to_single. apply prv_from_single.
    apply tprv_list_T. apply semi_completeness_fragment. 1: intros ? ? [].
    1: apply close_closed. now apply valid_L_valid_T in Hval.
  Qed.
End FiniteCompleteness.

Section StrongCompleteness.
  Context {Sigma : Signature}.
  Context {HdF : eq_dec Funcs} {HdP : eq_dec Preds}.
  Context {HeF : enumT Funcs} {HeP : enumT Preds}.

  Lemma dn_inherit (P Q : Prop) :
    (P -> Q) -> ~ ~ P -> ~ ~ Q.
  Proof. tauto. Qed.

  Lemma strong_completeness_standard (S : stab_class) T phi :
    (forall (T : theory) (phi : form), S Sigma T -> stable (tmap (fun psi : form => (sig_lift psi)[ext_c]) T ⊢TC phi)) -> @map_closed S Sigma (sig_ext Sigma) (fun phi => (sig_lift phi)[ext_c]) -> S Sigma T -> T ⊫S phi -> T ⊢TC phi.
  Proof.
    intros sts cls HT Hval. apply sig_lift_out_T. apply completeness_standard_stability.
    1: apply lift_ext_c_closes_T. 1: apply lift_ext_c_closes. 2: apply (sig_lift_subst_valid droppable_S Hval).
    now apply sts.
  Qed.

  Lemma strong_completeness_expl T phi :
    T ⊫E phi -> T ⊢TC phi.
  Proof.
    intros Hval. apply sig_lift_out_T, completeness_expl.
    1: apply lift_ext_c_closes_T. 1: apply lift_ext_c_closes.
    apply (sig_lift_subst_valid droppable_E Hval).
  Qed.

  Lemma strong_completeness_fragment T phi :
    T ⊫M phi -> T ⊩CL phi.
  Proof.
    intros Hval. apply sig_lift_out_T, semi_completeness_fragment.
    1: apply lift_ext_c_closes_T. 1: apply lift_ext_c_closes.
    apply (sig_lift_subst_valid droppable_BL Hval).
  Qed.

End StrongCompleteness.

*)
