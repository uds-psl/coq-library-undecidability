From Undecidability.FOLC Require Export GenConstructions.
From Undecidability.FOLC Require Export Consistency.
From Undecidability.FOLC Require Export GenTarski.
From Undecidability.FOLC Require Import Stability.

(** ** Completeness *)

(* ** Standard Models **)

Section Completeness.
  Context {Sigma : Signature}.
  Context {HdF : eq_dec Funcs} {HdP : eq_dec Preds}.
  Context {HeF : enumT Funcs} {HeP : enumT Preds}.

  Hint Constructors unused.

  Section BotModel.
    Variable T : theory.
    Hypothesis T_closed : closed_T T.

    Definition input_bot :=
      {|
        NBot := Fal ;
        NBot_closed := (fun n => uf_Fal n) ;

        variant := expl ;

        In_T := T ;
        In_T_closed := T_closed ;

        enum := form_enum ;
        enum_enum := form_enum_enumerates ;
        enum_unused := form_enum_fresh
      |}.

    Definition output_bot := construct_construction input_bot.

    Instance model_bot : interp term :=
      {| i_f := Func; i_P := fun P v => Pred P v ∈ Out_T output_bot ;
        i_F := ⊥ ∈ Out_T output_bot |}.

    Lemma eval_ident rho (t : term) :
      eval rho t = subst_term rho t.
    Proof.
      induction t using strong_term_ind; comp; asimpl; try congruence. f_equal.
    Qed.

    Lemma model_bot_correct phi rho :
      (phi[rho] ∈ Out_T output_bot <-> rho ⊨ phi).
    Proof.
      induction phi in rho |-*. 1,2,3: comp.
      - tauto.
      - now rewrite <- (vec_ext (fun x => eval_ident rho x)).
      - rewrite <-IHphi1, <-IHphi2. now apply Out_T_impl.
      - cbn. setoid_rewrite <-IHphi. rewrite Out_T_all.
        split; intros H d; specialize (H d); comp; now asimpl in H.
    Qed.

    Lemma model_bot_classical :
      classical model_bot.
    Proof.
      intros rho phi psi. apply model_bot_correct, Out_T_prv.
      use_theory (nil : list form). apply Pc.
    Qed.

    Lemma model_bot_standard :
      consistent T -> SM model_bot.
    Proof.
      intros Hcon. split. 1: exact model_bot_classical. intros Hin. apply Hcon.
      apply Out_T_econsistent with output_bot. use_theory [⊥]. ctx.
    Qed.

    Lemma model_bot_exploding :
      EM model_bot.
    Proof.
      split. 1: exact model_bot_classical. intros rho phi. apply model_bot_correct.
      comp. apply Out_T_prv. use_theory (nil : list form). ointros. oexfalso. ctx.
    Qed.

    Lemma valid_T_model_bot phi :
      phi ∈ T -> ids ⊨ phi.
    Proof.
      intros H % (Out_T_sub output_bot). apply model_bot_correct; now comp.
    Qed.
  End BotModel.

  Section StandardCompletenes.
    Variables (T : theory) (phi : form).
    Hypothesis (HT : closed_T T) (Hphi : closed phi).

    Lemma semi_completeness_standard :
      T ⊫S phi -> ~ ~ T ⊩CE phi.
    Proof.
      intros Hval Hcons. rewrite refutation_prv in Hcons. 
      assert (Hcl : closed_T (T ⋄ (¬ phi))) by ( intros ? ? [] ; subst; eauto).
      destruct (model_bot_standard Hcl Hcons) as [Hclass Hb]. apply Hb.
      apply (model_bot_correct Hcl (¬ phi) ids). apply Out_T_sub. right. now comp. refine (Hval _ _ _ _ _).
      - now apply model_bot_standard.
      - intros ? ?. apply valid_T_model_bot; intuition.
    Qed.

    Lemma completeness_standard_stability :
      (T ⊫S phi -> T ⊩CE phi) <-> stable (T ⊩CE phi).
    Proof.
      split.
      - intros Hcomp Hdn. apply Hcomp, valid_T_standard_dm. 1: firstorder. intros Hsem.
        apply Hdn. intros H. apply Hsem, (StrongSoundness H).
        + now intros _ ? ? []. 
        + intros _ ? ? []. firstorder.
      - intros Hstab Hsem. now apply Hstab, semi_completeness_standard.
    Qed.
  End StandardCompletenes.

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
      T ⊫S phi -> T ⊩CE phi.
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
      T ⊫E phi -> T ⊩CE phi.
    Proof.
      intros Hval. assert (Hcl : closed_T (T ⋄ (¬ phi))) by (intros ? ? [] ; subst; eauto).
      apply refutation_prv. apply (@Out_T_econsistent _ _ (output_bot Hcl)); cbn. use_theory [⊥]. 2: ctx.
      intros ? [<- | []]. apply (model_bot_correct _ ⊥ ids).
      specialize (Hval term (model_bot Hcl) (model_bot_exploding Hcl) ids).
      assert (@sat _ _ (model_bot Hcl) ids (¬ phi)) by (apply model_bot_correct, Out_T_sub; comp; firstorder).
      apply H, Hval. intros ? ?. apply valid_T_model_bot; intuition.
    Qed.

    Lemma valid_standard_expld_stability :
      (T ⊫S phi -> T ⊫E phi) <-> stable (T ⊩CE phi).
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

        enum := form_enum ;
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
  End FragmentCompleteness.
End Completeness.

(* ** Extending the Completeness Results *)

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

  Lemma strong_completeness_standard S T phi :
    ST S -> @map_closed S Sigma (sig_ext Sigma) (fun phi => (sig_lift phi)[ext_c]) -> S Sigma T -> T ⊫S phi -> T ⊩CE phi.
  Proof.
    intros sts cls HT Hval. apply sig_lift_out_T. apply completeness_standard_stability.
    1: apply lift_ext_c_closes_T. 1: apply lift_ext_c_closes. 2: apply (sig_lift_subst_valid droppable_S Hval).
    now apply sts, cls.
  Qed.

  Lemma strong_completeness_expl T phi :
    T ⊫E phi -> T ⊩CE phi.
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
