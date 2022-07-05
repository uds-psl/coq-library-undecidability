(** ** Completeness **)

From Undecidability.FOL Require Import Syntax.Facts Deduction.FragmentNDFacts Syntax.Theories Semantics.Kripke.FragmentCore Semantics.Kripke.FragmentSoundness 
                                       Semantics.Kripke.FragmentToTarski Deduction.FragmentSequent Deduction.FragmentSequentFacts.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation Shared.Dec.
From Undecidability Require Import Shared.Libs.PSL.Vectors.Vectors Shared.Libs.PSL.Vectors.VectorForall.
Import ListAutomationNotations.
From Undecidability.FOL.Completeness2 Require Export TarskiCompleteness.
(* From Undecidability.FOLC Require Export Gentzen. *)

(* *** Exploding and Minimal Models *)

Section KripkeCompleteness.
  Context {Σf : funcs_signature} {Σp : preds_signature}. (*
  Variable eF : nat -> option Σf.
  Context {HeF : enumerator__T eF Σf}.
  Variable eP : nat -> option Σp.
  Context {HeP : enumerator__T eP Σp}. *)

(*  Hint Constructors sprv. *)
  Instance model_bot : interp term :=
    {| i_func := func; i_atom := fun P v => False|}.
  Lemma universal_interp_eval rho t :
    eval rho t = t`[rho].
  Proof.
    now induction t; cbn.
  Qed.

  Section Contexts.

    Program Instance K_ctx {ff:falsity_flag} : kmodel term :=
      {|
        nodes := list form ;
        reachable := @incl form ;
        k_interp := model_bot ;
        k_P := fun A P v => sprv A None (atom P v) ;
      |}.
    Next Obligation.
      abstract (intuition; now apply (incl_tran H)).
    Qed.
    Next Obligation.
      abstract (eauto using seq_Weak).
    Qed.

    Definition F_P {ff} : list (@form _ _ _ ff) -> Prop := match ff with falsity_on => fun n => sprv n None ⊥ | _ => fun _ => False end.
    Lemma mon_F {ff:falsity_flag} (u v : @nodes _ _ _ K_ctx) : reachable u v -> F_P u -> F_P v.
    Proof.
      cbn. unfold F_P. destruct ff; try easy. intros H H1. eapply seq_Weak; [ exact H1| exact H].
    Qed.

    Notation "rho '⊩⊥(' u , M ')' phi" :=  (@ksat_bot _ _ _ M _ F_P mon_F u rho phi) (at level 20).

    Lemma K_ctx_correct {ff:falsity_flag} (A : list form) rho phi :
      (rho ⊩⊥(A, K_ctx ) phi-> A ⊢S phi[rho]) /\
      ((forall B psi, A <<= B -> B ;; phi[rho] ⊢s psi -> B ⊢S psi) -> rho ⊩⊥(A, K_ctx) phi).
    Proof.
      revert A rho; enough ((forall A rho, rho ⊩⊥( A, K_ctx) phi -> A ⊢S phi[rho]) /\
                          (forall A rho, (forall B psi, A <<= B -> B;; phi[rho] ⊢s psi -> B ⊢S psi)
                                  -> rho ⊩⊥( A, K_ctx) phi)) by intuition.
      induction phi as [|t1 t2|ff [] phi IHphi psi IHpsi|ff [] phi IHphi]; cbn; split; intros A rho.
      - tauto.
      - eauto.
      - erewrite Vector.map_ext. 1: eauto. apply universal_interp_eval.
      - intros H. erewrite Vector.map_ext. 1: now apply H. apply universal_interp_eval.
      - intros Hsat. apply IR, IHpsi. apply Hsat, IHphi. 1: intuition. eauto.
      - intros H B HB Hphi % IHphi. apply IHpsi. intros C xi HC Hxi. apply H.
        1: now transitivity B. eauto using seq_Weak.
      - intros Hsat. apply AllR.
        pose (phi' := subst_form ($0 .: (rho >> subst_term (S >> var))) phi).
        destruct (find_bounded_L (phi' :: A)).
        eapply seq_nameless_equiv_all' with (n := x) (phi := phi').
        + intros xi Hxi. apply b. now right.
        + eapply bounded_up. 1: apply b; now left. lia.
        + unfold phi'. rewrite subst_comp. erewrite subst_ext.
          * eapply IHphi. apply Hsat.
          * intros [|n]; cbn. 1:reflexivity.
            unfold funcomp. rewrite subst_term_comp. apply subst_term_id.
            intros [|m]; easy.
      - intros H t. apply IHphi. intros B psi HB Hpsi. apply H. assumption.
        apply AllL with (t := t). now rewrite help5.
    Qed.

    Corollary K_ctx_sprv {ff:falsity_flag} A rho phi :
      rho ⊩⊥(A, K_ctx) phi -> A ⊢S phi[rho].
    Proof.
      now destruct (K_ctx_correct A rho phi).
    Qed.

    Lemma K_ctx_subst {ff:falsity_flag} A phi rho :
      rho ⊩⊥( A, K_ctx) phi <-> var ⊩⊥( A, K_ctx) phi[rho].
    Proof.
      unfold ksat_bot, falsity_to_pred.
      rewrite <- atom_subst_comp_strong. 2:easy.
      assert (forall {ff:falsity_flag} rho, (atom (Σ_preds := Σ_preds_bot) (inl tt) (Vector.nil _)) = (atom (Σ_preds := Σ_preds_bot) (inl tt) (Vector.nil _))[rho]) as Heq by easy.
      erewrite Heq.
      rewrite <- subst_falsity_comm. cbn.
      rewrite (ksat_comp A var rho).
      apply ksat_ext. intros x. unfold funcomp. induction (rho x); cbn; try easy.
      erewrite <- map_ext_forall. 2: apply Forall_in, IH. 
      now rewrite Vector.map_id.
    Qed.

    Lemma K_ctx_constraint {ff:falsity_flag} A rho psi:
      rho ⊩⊥(A, K_ctx) (⊥ → psi).
    Proof.
      destruct ff eqn : Hff; try now intros.
      intros v B HB. cbn in HB. apply K_ctx_correct.
      intros B' psi' HB' Hprv. subst. eauto using seq_Weak.
    Qed.



  Ltac clean_ksoundness :=
    match goal with
    | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
    | [ H : (?A -> ?B), H2 : (?A -> ?B) -> _ |- _] => specialize (H2 H)
    end.

  Lemma ksoundness_f2p_model {ff1 ff2 : falsity_flag} A phi:
    A ⊢I phi -> 
    forall u rho, 
    (forall psi', psi' el A -> rho ⊩⊥(u,K_ctx) psi') -> 
    rho ⊩⊥(u,K_ctx) phi.
  Proof.
    intros Hprv. remember intu as s. induction Hprv; subst; cbn; intros u rho HA.
    all: repeat (clean_ksoundness + discriminate). all: (eauto || cbn -[F_P]; eauto).
    - intros v Hr Hpi. eapply IHHprv. intros ? []; subst; eauto using ksat_mon. eapply ksat_mon. 2: now apply HA. easy.
    - eapply IHHprv1. 3: eapply IHHprv2. all: eauto. apply K_ctx.
    - intros d. apply IHHprv. intros psi [psi' [<- Hp]] % in_map_iff. cbn.
      unfold ksat_bot. rewrite falsity_to_pred_subst.
      rewrite ksat_comp. apply HA, Hp.
    - unfold ksat_bot. rewrite falsity_to_pred_subst.
      rewrite ksat_comp. eapply ksat_ext. 2: eapply (IHHprv u rho HA (eval rho t)). 
      unfold funcomp. now intros [].
    - apply (@K_ctx_constraint _ u rho phi). 1:reflexivity.
      cbn. apply (IHHprv u rho). apply HA.
  Qed.

    Fact K_ctx_sprv' {ff:falsity_flag}  A rho phi :
      A ⊢S phi[rho] -> rho ⊩⊥(A, K_ctx) phi.
    Proof.
      intros H % seq_ND. apply K_ctx_subst.
      eapply ksoundness_f2p_model.
      - apply H.
      - cbn in H. intros psi HP. apply K_ctx_correct.
        intros B theta H1 H2. eapply Contr; eauto.
        rewrite subst_id. 1: now apply H1. easy.
    Qed.

    Corollary K_ctx_ksat {ff:falsity_flag} A rho phi :
      (forall B psi, A <<= B -> B ;; phi[rho] ⊢s psi -> B ⊢S psi) -> rho ⊩⊥(A, K_ctx) phi.
    Proof.
      now destruct (K_ctx_correct A rho phi).
    Qed.
  End Contexts.
(*
  Section ExplodingCompleteness.

    Lemma K_ctx_exploding :
      kexploding (@K_ctx expl).
    Proof.
      apply (@K_ctx_constraint expl).
    Qed.

    Lemma K_exp_completeness A phi :
      A ⊫KE phi -> A ⊢SE phi.
    Proof.
      intros Hsat. erewrite <-idSubst_form. apply K_ctx_sprv with (rho := ids). 2: reflexivity.
      apply Hsat. 1: apply K_ctx_exploding. intros psi Hpsi. apply K_ctx_ksat. intros B xi HB Hxi.
      asimpl in Hxi. eauto.
    Qed.

    Lemma K_exp_seq_ksoundness A phi :
      A ⊢SE phi -> A ⊫KE phi.
    Proof.
      intros H % seq_ND. apply @ksoundness with (b := expl). 2: apply H. firstorder.
    Qed.

    Fact SE_cut A phi psi :
      A ⊢SE phi -> A;;phi ⊢sE psi -> A ⊢SE psi.
    Proof.
      intros H1 % seq_ND H2 % seq_ND; cbn in *.
      apply H2 in H1. apply K_exp_completeness.
      apply @ksoundness with (b := expl); firstorder.
    Qed.
    
  End ExplodingCompleteness. *)

  Section BottomlessCompleteness.
    #[local] Existing Instance falsity_off | 0.
    Lemma K_bottomless_completeness A phi :
      True -> A ⊢ phi.
    Proof.
      intros Hsat. erewrite <-idSubst_form. apply K_ctx_sprv with (rho := ids). 2: reflexivity.
      apply Hsat. 1: apply I. intros psi Hpsi. apply K_ctx_ksat. intros B xi HB Hxi.
      asimpl in Hxi. eauto.
    Qed.
  End BottomlessCompleteness.

(* *** Standard Models *)

  Section StandardCompleteness.
    Context {HdF : eq_dec Funcs} {HdP : eq_dec Preds}.
    Context {HeF : enumT Funcs} {HeP : enumT Preds}.

    Definition cons A := ~ A ⊢SE ⊥.
    Definition cons_ctx := { A | cons A }.
    Definition ctx_incl (A B : cons_ctx) := incl (proj1_sig A) (proj1_sig B).

    Hint Unfold cons cons_ctx ctx_incl.

    Notation "A <<=C B" := (ctx_incl A B) (at level 20).
    Notation "A ⊢SC phi" := (proj1_sig A ⊢SE phi) (at level 20).
    Notation "A ;; psi ⊢sC phi" := (proj1_sig A ;; psi ⊢sE phi) (at level 20).

    Ltac dest_con_ctx :=
      match goal with
      | [ |- forall u : cons_ctx, _] => let Hu := fresh "H" u in intros [u Hu]
      | [ A : cons_ctx |- _] => let HA := fresh "H" A in destruct A as [A HA]
      end.

    Ltac cctx := repeat (progress dest_con_ctx); comp.

    Hint Extern 1 => cctx.

    Program Instance K_std : kmodel term :=
      {|
        reachable := ctx_incl ;
        k_interp := universal_interp ;
        k_P := fun A P v => ~ ~ A ⊢SC (Pred P v) ;
        k_Bot := fun _ => False
      |}.
    Next Obligation.
      abstract (cctx; firstorder).
    Qed.
    Next Obligation.
      intros H2. apply H0. intros H3. apply H2.
      abstract (eauto using seq_Weak).
    Qed.

    Lemma K_std_standard :
      kstandard K_std.
    Proof.
      intros []. cbn. trivial.
    Qed.

    Lemma K_std_correct (A : cons_ctx) rho phi :
      (rho ⊩(A, K_std) phi -> ~ ~ A ⊢SC phi[rho]) /\
      ((forall B psi, A <<=C B -> B ;; phi[rho] ⊢sC psi -> ~ ~ B ⊢SC psi) -> rho ⊩(A, K_std) phi).
    Proof.
      revert A rho; enough ((forall A rho, rho ⊩( A, K_std) phi -> ~ ~ A ⊢SC phi[rho])
                          /\ (forall A rho, (forall B psi, A <<=C B -> B;; phi[rho] ⊢sC psi -> ~ ~ B ⊢SC psi)
                                    -> rho ⊩( A, K_std) phi)) by firstorder.
      induction phi as [| t1 t2 | phi [IHphi1 IHphi2] psi [IHpsi1 IHpsi2] | phi [IHphi1 IHphi2]].
      all: cbn; asimpl; split; intros A rho.
      - tauto.
      - intros H. exfalso. apply (H A ⊥); auto.
      - now rewrite (vec_ext (fun x => universal_interp_eval rho x)).
      - rewrite (vec_ext (fun x => universal_interp_eval rho x)). intros H H'.
        eapply H. 3: { intros H1. apply H', H1. } all: auto.
      - intros Hsat H.
        assert (HA : ~ ~ ((phi[rho] :: proj1_sig A) ⊢SE ⊥ \/ ~ (phi[rho] :: proj1_sig A) ⊢SE ⊥)) by tauto.
        apply HA. clear HA. intros [HA|HA].
        + apply H. apply IR. apply Absurd. assumption.
        + pose (A' := exist cons (phi[rho] :: proj1_sig A) HA). apply (IHpsi1 A' rho).
          * apply Hsat; auto 3. apply IHphi2. intros B theta HB HT.
            intros H'. apply H'. eauto.
          * intros H'. apply H. apply IR, H'.
      - intros H B HB Hphi % IHphi1. apply IHpsi2. intros C xi HC Hxi.
        intros HX. apply Hphi. intros Hphi'. apply (H C xi); trivial.
        + cctx. now transitivity B.
        + apply IL; trivial. eapply seq_Weak; eauto.
      - pose (phi' := subst_form (var_term 0 .: (rho >> subst_term (S >> var_term))) phi).
        intros Hsat. intros H. cctx. destruct (find_unused_L (phi' :: A)).
        apply (IHphi1 (exist cons A HA) (var_term x.:rho)).
        rewrite ksat_ext. 2: reflexivity. now apply Hsat.
        intros H'. apply H, AllR.
        eapply seq_nameless_equiv with (n := x) (phi0 := phi').
        + intros xi Hxi. apply u. constructor. intuition.
        + apply u. omega. intuition.
        + unfold phi'. asimpl. apply H'.
      - intros H t. apply IHphi2. intros B psi HB Hpsi. apply H. assumption.
        apply AllL with (t0 := t). now asimpl in *.
    Qed.

    Corollary K_std_sprv A rho phi :
      rho ⊩(A, K_std) phi -> ~ ~ A ⊢SC phi[rho].
    Proof.
      now destruct (K_std_correct A rho phi).
    Qed.

    Corollary K_std_sprv' A rho phi :
       ~ ~ A ⊢SC phi[rho] -> rho ⊩(A, K_std) phi.
    Proof.
      intros H. apply (K_std_correct A rho phi).
      intros B psi H1 H2 H3. apply H. intros H'.
      apply H3. eapply SE_cut; try eassumption.
      now apply (seq_Weak H').
    Qed.

    Corollary K_std_ksat A rho phi :
      (forall B psi, A <<=C B -> B ;; phi[rho] ⊢sC psi -> ~ ~ B ⊢SC psi) -> rho ⊩(A, K_std) phi.
    Proof.
      now destruct (K_std_correct A rho phi).
    Qed.

    Lemma K_std_completeness A phi :
      A ⊫KS phi -> ~ ~ A ⊢SE phi.
    Proof.
      intros Hsat H.
      assert (HA : ~ ~ (A ⊢SE ⊥ \/ ~ A ⊢SE ⊥)) by tauto.
      apply HA. clear HA. intros [HA|HA].
      - apply H. apply Absurd. assumption.
      - specialize (Hsat _ K_std K_std_standard (exist cons A HA) ids).
        apply K_std_sprv in Hsat.
        + apply Hsat. intros Hsat'. apply H.
          rewrite <- idSubst_form with ids phi; trivial.
        + intros psi Hpsi. apply K_std_ksat.
          intros B xi HB Hxi. asimpl in Hxi. eauto.
    Qed.

    Lemma K_std_seq_ksoundness A phi :
      A ⊢SE phi -> A ⊫KS phi.
    Proof.
      intros H % seq_ND. apply @ksoundness with (b := expl). 2: apply H. firstorder.
    Qed.
  End StandardCompleteness.

  (* *** MP is required *)

  Section MPRequired.
    Variable C : stab_class.
    Hypothesis HC : map_closed C dnt.
    Variable K_completeness : forall T phi, C T -> closed_T T -> closed phi -> kvalid_T kstandard T phi -> T ⊩SE phi.

    Lemma cend_dn T phi :
      closed_T T -> closed phi ->
      C T -> ~ ~ T ⊩CE phi -> T ⊩CE phi.
    Proof.
      intros clT clphi HT Hdn. apply DN_T, dnt_to_TCE. cbn. apply (@seq_ND_T _ _ (tmap dnt T) (¬ (¬ dnt phi))). 
      apply K_completeness. 1: apply HC, HT.
      - intros ? ? (? & ? & <-). eapply dnt_unused. now eapply clT.
      - intros n. repeat econstructor. eapply dnt_unused; eauto. 
      - intros D M St u rho HT' v Hv Hn. contradict Hdn. intros Hphi % dnt_to_TIE.
        apply strong_ksoundness with (C0 := kstandard) in Hphi. apply (St v), Hn. 1: reflexivity.
        2: intros; apply kstandard_explodes. 1: apply (Hphi D M St v rho).
        intros psi Hpsi % HT'. apply (ksat_mon Hv Hpsi).
    Qed.
  End MPRequired.
  
End KripkeCompleteness.
