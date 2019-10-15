(** ** Constructive Analysis of Completeness Theorems **)

From Undecidability.FOLC Require Export Gentzen.
From Undecidability.FOLC Require Export Kripke.
From Undecidability.FOLC Require Export GenCompleteness.
From Undecidability.FOLC Require Export Stability.

(** *** Exploding and Minimal Models *)

Section KripkeCompleteness.
  Context {Sigma : Signature}.

  Hint Constructors sprv.

  Instance universal_interp : interp term :=
    {| i_f := Func ; i_F := False ; i_P := fun _ _ => False |}.

  Lemma universal_interp_eval rho t :
    eval rho t = t[rho].
  Proof.
    induction t using strong_term_ind; comp; asimpl; try congruence. f_equal.
  Qed.

  Section Contexts.
    Context {b : bottom}.

    Instance K_ctx : kmodel term :=
      {|
        reachable := @incl form ;
        k_interp := universal_interp ;
        k_P := fun A P v => sprv b A None (Pred P v) ;
        k_Bot := fun A => sprv b A None ⊥
      |}.
    Proof.
      1,3,4: abstract (eauto using seq_Weak).
      - abstract (intuition; now apply (incl_tran H)).
    Defined.

    Lemma K_ctx_correct (A : list form) rho phi :
      (rho ⊨(A, K_ctx ) phi -> A ⊢S phi[rho]) /\
      ((forall B psi, A <<= B -> B ;; phi[rho] ⊢s psi -> B ⊢S psi) -> rho ⊨(A, K_ctx) phi).
    Proof.
      revert A rho; enough ((forall A rho, rho ⊨( A, K_ctx) phi -> A ⊢S phi[rho]) /\ (forall A rho, (forall B psi, A <<= B -> B;; phi[rho] ⊢s psi -> B ⊢S psi) -> rho ⊨( A, K_ctx) phi)) by intuition.
      induction phi as [| t1 t2 | phi [IHphi1 IHphi2] psi [IHpsi1 IHpsi2] | phi [IHphi1 IHphi2]]; cbn; asimpl; split; intros A rho.
      - tauto.
      - eauto.
      - now rewrite (vec_ext (fun x => universal_interp_eval rho x)).
      - rewrite (vec_ext (fun x => universal_interp_eval rho x)). eauto.
      - intros Hsat. apply IR, IHpsi1. apply Hsat, IHphi2. 1: intuition. eauto.
      - intros H B HB Hphi % IHphi1. apply IHpsi2. intros C xi HC Hxi. apply H.
        1: now transitivity B. eauto using seq_Weak.
      - intros Hsat. apply AllR. pose (phi' := subst_form (var_term 0 .: (rho >> subst_term (S >> var_term))) phi).
        destruct (find_unused_L (phi' :: A)). eapply seq_nameless_equiv with (n := x) (phi0 := phi').
        + intros xi Hxi. apply u. constructor. intuition.
        + apply u. omega. intuition.
        + asimpl. apply IHphi1. rewrite ksat_ext. 2: reflexivity. now apply Hsat.
      - intros H t. apply IHphi2. intros B psi HB Hpsi. apply H. assumption.
        apply AllL with (t0 := t). now asimpl in *.
    Qed.

    Corollary K_ctx_sprv A rho phi :
      rho ⊨(A, K_ctx) phi -> A ⊢S phi[rho].
    Proof.
      now destruct (K_ctx_correct A rho phi).
    Qed.

    Corollary K_ctx_ksat A rho phi :
      (forall B psi, A <<= B -> B ;; phi[rho] ⊢s psi -> B ⊢S psi) -> rho ⊨(A, K_ctx) phi.
    Proof.
      now destruct (K_ctx_correct A rho phi).
    Qed.
  End Contexts.

  Section ExplodingCompleteness.
    Lemma K_ctx_exploding :
      kexploding (@K_ctx expl).
    Proof.
      intros A rho P v B HB. apply K_ctx_ksat.
      intros B' psi HB' Hprv. comp. eauto using seq_Weak.
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
  End ExplodingCompleteness.

  Section BottomlessCompleteness.
    Lemma K_bottomless_completeness A phi :
      A ⊫KBL phi -> A ⊢SL phi.
    Proof.
      intros Hsat. erewrite <-idSubst_form. apply K_ctx_sprv with (rho := ids). 2: reflexivity.
      apply Hsat. 1: apply I. intros psi Hpsi. apply K_ctx_ksat. intros B xi HB Hxi.
      asimpl in Hxi. eauto.
    Qed.
  End BottomlessCompleteness.

(** *** Standard Models *)

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

    Instance K_std : kmodel term :=
      {|
        reachable := ctx_incl ;
        k_interp := universal_interp ;
        k_P := fun A P v => ~ ~ A ⊢SC (Pred P v) ;
        k_Bot := fun _ => False
      |}.
    Proof.
      - abstract eauto.
      - abstract (cctx; firstorder).
      - intros A B H P t H1 H2. apply H1. intros H3. apply H2.
        abstract (eauto using seq_Weak).
      - abstract (cctx; firstorder).
    Defined.

    Lemma nsprv_cons A phi :
      (forall H, (exist cons A H) ⊢SC phi) -> ~ ~ A ⊢SE phi.
    Proof.
      intros Hsat H.
      assert (HA : ~ ~ (A ⊢SE ⊥ \/ ~ A ⊢SE ⊥)) by tauto.
      apply HA. clear HA. intros [HA|HA].
      - apply H. apply Absurd. assumption.
      - apply H, (Hsat HA).
    Qed.

    Lemma K_std_correct (A : cons_ctx) rho phi :
      (rho ⊨(A, K_std) phi -> ~ ~ A ⊢SC phi[rho]) /\
      ((forall B psi, A <<=C B -> B ;; phi[rho] ⊢sC psi -> B ⊢SC psi) -> rho ⊨(A, K_std) phi).
    Proof.
      revert A rho; enough ((forall A rho, rho ⊨( A, K_std) phi -> ~ ~ A ⊢SC phi[rho])
                          /\ (forall A rho, (forall B psi, A <<=C B -> B;; phi[rho] ⊢sC psi -> ~ ~ B ⊢SC psi)
                                    -> rho ⊨( A, K_std) phi)) by firstorder.
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
        + asimpl. apply H'.
      - intros H t. apply IHphi2. intros B psi HB Hpsi. apply H. assumption.
        apply AllL with (t0 := t). now asimpl in *.
    Qed.

    Corollary K_std_sprv A rho phi :
      rho ⊨(A, K_std) phi -> ~ ~ A ⊢SC phi[rho].
    Proof.
      now destruct (K_std_correct A rho phi).
    Qed.

    Corollary K_std_ksat A rho phi :
      (forall B psi, A <<=C B -> B ;; phi[rho] ⊢sC psi -> B ⊢SC psi) -> rho ⊨(A, K_std) phi.
    Proof.
      now destruct (K_std_correct A rho phi).
    Qed.

    Lemma K_std_standard :
      kstandard K_std.
    Proof.
      intros []. cbn. trivial.
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

  (** *** MP is required *)

  Section MPRequired.
    Variable C : stab_class.
    Hypothesis HC : map_closed C dnt.
    Variable K_completeness : forall T phi, C T -> kvalid_T kstandard T phi -> T ⊩SE phi.

    Lemma cend_dn T phi :
      C T -> ~ ~ T ⊩CE phi -> T ⊩CE phi.
    Proof.
      intros HT Hdn. apply DN_T, dnt_to_TCE. cbn. apply (@seq_ND_T _ _ (tmap dnt T) (¬ (¬ dnt phi))). 
      apply K_completeness. 1: apply HC, HT. intros D M St u rho HT' v Hv Hn. contradict Hdn. intros Hphi % dnt_to_TIE.
      apply strong_ksoundness with (C0 := kstandard) in Hphi. apply (St v), Hn. 1: reflexivity.
      2: intros; apply kstandard_explodes. 1: apply (Hphi D M St v rho).
      intros psi Hpsi % HT'. apply (ksat_mon Hv Hpsi).
    Qed.
  End MPRequired.
  
End KripkeCompleteness.
