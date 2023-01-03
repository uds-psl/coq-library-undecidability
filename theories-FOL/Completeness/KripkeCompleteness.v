(** ** Kripke Completeness **)

From FOL Require Import FragmentSyntax Theories Deduction.FragmentSequentFacts.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts MPFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation Shared.Dec.
From Undecidability Require Import Shared.Libs.PSL.Vectors.Vectors Shared.Libs.PSL.Vectors.VectorForall.
Import ListAutomationNotations.
From FOL.Completeness Require Export TarskiCompleteness.

(* ** Universal Models *)

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
      abstract (eauto using seq_Weak).
    Qed.

    Definition F_P {ff} : list (@form _ _ _ ff) -> Prop := match ff with falsity_on => fun n => sprv n None ⊥ | _ => fun _ => False end.
    Lemma mon_F {ff:falsity_flag} (u v : @nodes _ _ _ K_ctx) : reachable u v -> F_P u -> F_P v.
    Proof.
      cbn. unfold F_P. destruct ff; try easy. intros H H1. eapply seq_Weak; [ exact H1| exact H].
    Qed.

    Notation "rho '⊩⊥(' u , M ')' phi" :=  (@ksat_bot _ _ _ M _ F_P mon_F u rho phi) (at level 20).

    Lemma K_ctx_correct_exp {ff:falsity_flag} (A : list form) rho phi :
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
        pose (phi' := phi[up rho]).
        destruct (find_bounded_L (phi' :: A)).
        eapply seq_nameless_equiv_all' with (n := x) (phi := phi').
        + intros xi Hxi. apply b. now right.
        + eapply bounded_up. 1: apply b; now left. lia.
        + unfold phi'. asimpl. apply IHphi, Hsat.
      - intros H t. apply IHphi. intros B psi HB Hpsi. apply H. assumption.
        apply AllL with (t := t). now asimpl.
    Qed.

    Corollary K_ctx_sprv_exp {ff:falsity_flag} A rho phi :
      rho ⊩⊥(A, K_ctx) phi -> A ⊢S phi[rho].
    Proof.
      now destruct (K_ctx_correct_exp A rho phi).
    Qed.

    Lemma K_ctx_subst_exp {ff:falsity_flag} A phi rho :
      rho ⊩⊥( A, K_ctx) phi <-> var ⊩⊥( A, K_ctx) phi[rho].
    Proof.
      unfold ksat_bot, falsity_to_pred.
      rewrite <- atom_subst_comp. 2:easy.
      assert (forall {ff:falsity_flag} rho, (atom (Σ_preds := Σ_preds_bot) (inl tt) (Vector.nil _)) = (atom (Σ_preds := Σ_preds_bot) (inl tt) (Vector.nil _))[rho]) as Heq by easy.
      erewrite Heq.
      rewrite <- subst_falsity_comm. cbn.
      rewrite (ksat_comp A var rho).
      apply ksat_ext. intros x. unfold funcomp. induction (rho x); cbn; try easy.
      erewrite <- map_ext_forall. 2: apply Forall_in, IH. 
      now rewrite Vector.map_id.
    Qed.

    Lemma K_ctx_constraint_exp {ff:falsity_flag} A rho psi:
      rho ⊩⊥(A, K_ctx) (⊥ → psi).
    Proof.
      destruct ff eqn : Hff; try now intros.
      intros v B HB. cbn in HB. apply K_ctx_correct_exp.
      intros B' psi' HB' Hprv. subst. eauto using seq_Weak.
    Qed.

    Corollary K_ctx_ksat_exp {ff:falsity_flag} A rho phi :
      (forall B psi, A <<= B -> B ;; phi[rho] ⊢s psi -> B ⊢S psi) -> rho ⊩⊥(A, K_ctx) phi.
    Proof.
      now destruct (K_ctx_correct_exp A rho phi).
    Qed.
 
    #[local] Existing Instance falsity_off.

    Lemma K_ctx_correct (A : list form) rho phi :
      (rho ⊩(A, K_ctx ) phi-> A ⊢S phi[rho]) /\
      ((forall B psi, A <<= B -> B ;; phi[rho] ⊢s psi -> B ⊢S psi) -> rho ⊩(A, K_ctx) phi).
    Proof.
      revert phi. remember falsity_off as ff eqn:Heqff. intros phi.
      revert A rho; enough ((forall A rho, rho ⊩( A, K_ctx) phi -> A ⊢S phi[rho]) /\
                          (forall A rho, (forall B psi, A <<= B -> B;; phi[rho] ⊢s psi -> B ⊢S psi)
                                  -> rho ⊩( A, K_ctx) phi)) by intuition.
      induction phi as [|t1 t2|ff [] phi IHphi psi IHpsi|ff [] phi IHphi]; cbn; split; intros A rho.
      - tauto.
      - congruence.
      - erewrite Vector.map_ext. 1: eauto. apply universal_interp_eval.
      - intros H. erewrite Vector.map_ext. 1: now apply H. apply universal_interp_eval.
      - intros Hsat. apply IR, IHpsi. 1:easy. apply Hsat, IHphi. 1: intuition. 1:easy. eauto.
      - intros H B HB Hphi % IHphi. 2:easy. apply IHpsi. 1:easy. intros C xi HC Hxi. apply H.
        1: now transitivity B. eauto using seq_Weak.
      - intros Hsat. apply AllR.
        pose (phi' := phi[up rho]).
        destruct (find_bounded_L (phi' :: A)).
        eapply seq_nameless_equiv_all' with (n := x) (phi := phi').
        + intros xi Hxi. apply b. now right.
        + eapply bounded_up. 1: apply b; now left. lia.
        + unfold phi'. asimpl. apply IHphi, Hsat. easy.
      - intros H t. apply IHphi. 1:easy. intros B psi HB Hpsi. apply H. assumption.
        apply AllL with (t := t). now asimpl.
    Qed.

    Corollary K_ctx_sprv A rho phi :
      rho ⊩(A, K_ctx) phi -> A ⊢S phi[rho].
    Proof.
      now destruct (K_ctx_correct A rho phi).
    Qed.

    Lemma K_ctx_subst A phi rho :
      rho ⊩( A, K_ctx) phi <-> var ⊩( A, K_ctx) phi[rho].
    Proof.
      rewrite (ksat_comp A var rho).
      apply ksat_ext. intros x. unfold funcomp. induction (rho x); cbn; try easy.
      erewrite <- map_ext_forall. 2: apply Forall_in, IH. 
      now rewrite Vector.map_id.
    Qed.

    Corollary K_ctx_ksat A rho phi :
      (forall B psi, A <<= B -> B ;; phi[rho] ⊢s psi -> B ⊢S psi) -> rho ⊩(A, K_ctx) phi.
    Proof.
      now destruct (K_ctx_correct A rho phi).
    Qed.
  End Contexts.

  Section ExplodingCompleteness.

    Lemma K_ctx_exploding {ff:falsity_flag}:
      kexploding mon_F.
    Proof.
      unfold kexploding.
      apply K_ctx_constraint_exp.
    Qed.

    Lemma K_exp_completeness A phi :
      kvalid_exploding_ctx A phi -> A ⊢SE phi.
    Proof.
      intros Hsat. erewrite <-subst_id. 1: apply K_ctx_sprv_exp with (rho := var). 2: reflexivity.
      apply Hsat. 1: apply K_ctx_exploding. intros psi Hpsi. apply K_ctx_ksat_exp. intros B xi HB Hxi.
      rewrite subst_id in Hxi. 2:reflexivity. eauto.
    Qed.

    Ltac clean_ksoundness :=
      match goal with
      | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
      | [ H : (?A -> ?B), H2 : (?A -> ?B) -> _ |- _] => specialize (H2 H)
      end.
    Lemma K_exp_ksoundness {ff:falsity_flag} A phi :
      A ⊢I phi -> kvalid_exploding_ctx A phi.
    Proof.
      intros Hprv. cbn in Hprv. intros D M F_P mon_F u rho Hexpl. revert u rho.
      remember intu as s in Hprv. induction Hprv; subst; cbn; intros u rho HA.
      all: repeat (clean_ksoundness + discriminate). all: (eauto || cbn ; eauto).
      - intros v Hr Hpi. eapply IHHprv. intros ? []; subst; eauto using ksat_mon. eapply ksat_mon. 2: now apply HA. easy.
      - eapply IHHprv1. 3: eapply IHHprv2. all: eauto. apply M.
      - intros d. apply IHHprv. intros psi [psi' [<- Hp]] % in_map_iff. cbn.
        unfold ksat_bot. rewrite falsity_to_pred_subst.
        rewrite ksat_comp. apply HA, Hp.
      - unfold ksat_bot. rewrite falsity_to_pred_subst.
        rewrite ksat_comp. eapply ksat_ext. 2: eapply (IHHprv u rho HA (eval rho t)). 
        unfold funcomp. now intros [].
      - apply (Hexpl u rho phi u (ltac:(apply M))).
        specialize (IHHprv u rho HA). cbn in IHHprv. apply IHHprv.
    Qed.

    Lemma K_exp_seq_ksoundness {ff:falsity_flag} A phi :
      A ⊢SE phi -> kvalid_exploding_ctx A phi.
    Proof.
      intros H%seq_ND. now apply K_exp_ksoundness.
    Qed.

    Fact SE_cut A phi psi :
      A ⊢SE phi -> A;;phi ⊢sE psi -> A ⊢SE psi.
    Proof.
      intros H1 % seq_ND H2 % seq_ND; cbn in *.
      apply H2 in H1. apply K_exp_completeness.
      apply K_exp_ksoundness. firstorder.
    Qed.
    
  End ExplodingCompleteness.

  Section BottomlessCompleteness.
    #[local] Existing Instance falsity_off.

    Lemma K_bottomless_completeness A phi :
      kvalid_ctx A phi -> A ⊢S phi.
    Proof.
      intros Hsat. erewrite <- subst_id. apply K_ctx_sprv with (rho := var). 2: reflexivity.
      apply Hsat. intros psi Hpsi. apply K_ctx_ksat. intros B xi HB Hxi.
      rewrite subst_id in Hxi. 2:easy. eauto.
    Qed.
  End BottomlessCompleteness.

(* *** Standard Models *)

  Section StandardCompleteness.
    #[local] Existing Instance falsity_on.

    Definition cons A := ~ A ⊢SE ⊥.
    Definition cons_ctx := { A | cons A }.
    Definition ctx_incl (A B : cons_ctx) := incl (proj1_sig A) (proj1_sig B).

    #[local] Hint Unfold cons cons_ctx ctx_incl : core.

    Notation "A <<=C B" := (ctx_incl A B) (at level 20).
    Notation "A ⊢SC phi" := ((proj1_sig A) ⊢SE phi) (at level 20).
    Notation "A ;; psi ⊢sC phi" := ((proj1_sig A) ;; psi ⊢sE phi) (at level 20).

    Ltac dest_con_ctx :=
      match goal with
      | [ |- forall u : cons_ctx, _] => let Hu := fresh "H" u in intros [u Hu]
      | [ A : cons_ctx |- _] => let HA := fresh "H" A in destruct A as [A HA]
      end.

    Ltac cctx := repeat (progress dest_con_ctx; unfold ctx_incl); cbn.

    Hint Extern 1 => cctx : core.

    Program Instance K_std : kmodel term :=
      {|
        reachable := ctx_incl ;
        k_interp := model_bot ;
        k_P := fun A P v => ~ ~ A ⊢SC (@atom _ _ _ _ P v) 
      |}.
    Next Obligation.
      abstract (apply H0; intros K; apply H1; eapply seq_Weak; eauto).
    Qed.

    Lemma K_std_correct (A : cons_ctx) rho phi :
      (rho ⊩(A, K_std) phi -> ~ ~ A ⊢SC phi[rho]) /\
      ((forall B psi, A <<=C B -> B ;; phi[rho] ⊢sC psi -> ~ ~ B ⊢SC psi) -> rho ⊩(A, K_std) phi).
    Proof.
      revert A rho; enough ((forall A rho, rho ⊩( A, K_std) phi -> ~ ~ A ⊢SC phi[rho])
                          /\ (forall A rho, (forall B psi, A <<=C B -> B;; phi[rho] ⊢sC psi -> ~ ~ B ⊢SC psi)
                                    -> rho ⊩( A, K_std) phi)) by firstorder.
      induction phi as [| t1 t2 | [ ] phi [IHphi1 IHphi2] psi [IHpsi1 IHpsi2] | [ ] phi [IHphi1 IHphi2] ] using form_ind_falsity.
      all: cbn; split; intros A rho.
      - tauto.
      - intros H. exfalso. apply (H A ⊥); auto.
      - now rewrite (Vector.map_ext _ _ _ _ (universal_interp_eval rho)).
      - rewrite <- (Vector.map_ext _ _ _ _ (universal_interp_eval rho)). intros H H'.
        eapply H. 3: { intros H1. apply H', H1. } all: auto.
      - intros Hsat H.
        assert (HA : ~ ~ ((phi[rho] :: proj1_sig A) ⊢SE ⊥ \/ ~ (phi[rho] :: proj1_sig A) ⊢SE ⊥)) by tauto.
        apply HA. clear HA. intros [HA|HA].
        + apply H. apply IR. apply Absurd. assumption.
        + pose (A' := exist cons (phi[rho] :: proj1_sig A) HA). apply (IHpsi1 A' rho).
          * apply Hsat. 1: now apply incl_tl. apply IHphi2. intros B theta HB HT.
            intros H'. apply H'. eauto.
          * intros H'. apply H. apply IR, H'.
      - intros H B HB Hphi % IHphi1. apply IHpsi2. intros C xi HC Hxi.
        intros HX. apply Hphi. intros Hphi'. apply (H C xi); trivial.
        + cctx. now transitivity B.
        + apply IL; trivial. eapply seq_Weak; eauto.
      - pose (phi' := subst_form ($0 .: (rho >> subst_term (S >> var))) phi).
        intros Hsat. intros H. cctx. destruct (find_bounded_L (phi' :: A)) as [x b].
        apply (IHphi1 (exist cons A HA) ($x.:rho)).
        rewrite ksat_ext. 2: reflexivity. now apply Hsat.
        intros H'. apply H, AllR. cbn.
        eapply seq_nameless_equiv_all' with (n := x) (phi := phi').
        + intros xi Hxi. apply b. now right.
        + eapply bounded_up. 1: apply b; now left. lia.
        + unfold phi'. cbn in H'. now asimpl.
      - intros H t. apply IHphi2. intros B psi HB Hpsi. apply H. assumption.
        apply AllL with (t := t). now asimpl.
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
      kvalid_ctx A phi -> ~ ~ A ⊢SE phi.
    Proof.
      intros Hsat H.
      assert (HA : ~ ~ (A ⊢SE ⊥ \/ ~ A ⊢SE ⊥)) by tauto.
      apply HA. clear HA. intros [HA|HA].
      - apply H. apply Absurd. assumption.
      - specialize (Hsat _ K_std (exist cons A HA) var).
        apply K_std_sprv in Hsat.
        + apply Hsat. intros Hsat'. apply H.
          erewrite <- subst_id; trivial. apply Hsat'.
        + intros psi Hpsi. apply K_std_ksat.
          intros B xi HB Hxi. asimpl in Hxi. eauto.
    Qed.

    Lemma K_std_seq_ksoundness A phi :
      A ⊢SE phi -> kvalid_ctx A phi.
    Proof.
      intros H % seq_ND. apply ksoundness, H.
    Qed.
  End StandardCompleteness.


  Section Stability.
    Existing Instance falsity_on.
    Context (T_kind : theory -> Prop).
    Definition K_completeness := forall T phi, T_kind T -> closed_T T -> closed phi -> 
                  kvalid_theo T phi -> T ⊩SE phi.
    Lemma kcompleteness_implies_stability T phi : K_completeness ->
      T_kind (tmap negative_translation T) ->
      closed_T T -> closed phi ->
      ~ ~ T ⊢TC phi -> T ⊢TC phi.
    Proof.
      intros Hcomp kindT clT clphi HTDN.
      apply DN_T. apply nt_correct_theory. cbn. apply seq_ND_T.
      apply Hcomp.
      - easy.
      - apply tmap_closed. 1: apply nt_bounded. easy.
      - unfold closed. solve_bounds. apply nt_bounded. apply clphi.
      - intros D M u rho HT.
        intros v Huv Hphiv. cbn. apply HTDN.
        intros (A & HTA & HTphi). eapply nt_Cprv_to_Iprv in HTphi.
        eapply DN_into in HTphi.
        apply ksoundness in HTphi.
        unshelve eapply (@HTphi D M u rho _ v Huv Hphiv).
        intros ? (psi & <- & HApsi) %in_map_iff. apply HT.
        exists psi. split; try easy. now apply HTA.
    Qed.
  End Stability.

  Section MP_Equivalence.
    Definition kcompleteness_enumerable := K_completeness enumerable.

    Lemma bot_deriv_stable_enum_k (T : @theory _ _ _ falsity_on) : kcompleteness_enumerable -> closed_T T -> enumerable T ->
      stable (@FragmentND.tprv _ _ _ class T ⊥).
    Proof.
      intros Hcomp Hclosed Henum HC.
      apply (kcompleteness_implies_stability Hcomp); try easy. 2: econstructor.
      now apply enum_tmap.
    Qed.

(*
    Lemma MP_implies_kcompleteness_enum : MP -> kcompleteness_enumerable.
    Proof.
      intros Hmp T phi HT Hphi Henum Hvalid.
      apply completeness_classical_stability; eauto. unfold stable.
      eapply mp_tprv_stability; try tauto. now eapply enumerable_list_enumerable.
    Qed.
*)
    Lemma kcompleteness_enum_implies_MP : kcompleteness_enumerable -> MP.
    Proof.
      intros HC f Hf.
      pose (fun x : form => exists n, x = ⊥ /\ f n = true) as T.
      assert (closed_T T) as Hclosed by (now intros k [n [-> Hn]]; econstructor).
      assert (enumerable T) as Henum.
      { exists (fun n => if f n then Some (⊥) else None). intros phi; split; intros H.
        + destruct H as (n & Heq & Hfn). exists n. rewrite Hfn. now rewrite Heq.
        + destruct H as (n & Hn). unfold T. exists n. destruct (f n); try congruence.
          split; try easy. congruence.
       }
      pose proof (@bot_deriv_stable_enum_k T HC Hclosed Henum).
      enough (T ⊢TC ⊥) as [[|lx lr] [HL HL']].
      - exfalso. eapply consistent_ND. apply HL'.
      - destruct (HL lx) as (n & Heq & Hfn). 1:now left. now exists n.
      - apply H. intros Hc. apply Hf. intros [n Hn]. apply Hc. exists [⊥]. split.
        + intros ? [<- | []]. unfold T. exists n. split; try easy.
        + apply Ctx; now left.
    Qed.

  End MP_Equivalence.

  Section LEM_Equivalence.
    Definition kcompleteness_arbitrary := K_completeness (fun x => True).
    Definition LEM := forall (P:Prop), P \/ ~ P.

    Lemma bot_valid_stable (T : @theory _ _ _ falsity_on) : closed_T T -> stable (valid_theory_C (classical (ff := falsity_on)) T ⊥).
    Proof.
      intros Hclosed HH D I rho Hclass H.
      apply HH. intros Hc. apply (Hc D I rho Hclass H).
    Qed.
    Lemma bot_deriv_stable_k (T : @theory _ _ _ falsity_on) : kcompleteness_arbitrary -> 
      closed_T T -> stable (@FragmentND.tprv _ _ _ class T ⊥).
    Proof.
      intros Hcomp Hclosed HC.
      apply (kcompleteness_implies_stability Hcomp); try easy. econstructor.
    Qed.
    Existing Instance falsity_on.
    Lemma kcompleteness_implies_LEM : kcompleteness_arbitrary -> LEM.
    Proof.
      intros HC P.
      pose (fun x : form => closed x /\ (P \/ ~P)) as T.
      assert (closed_T T) as Hclosed by (intros k; cbv; tauto).
      pose proof (@bot_deriv_stable_k T HC Hclosed).
      enough (T ⊢TC ⊥) as [[|lx lr] [HL HL']].
      - exfalso. eapply consistent_ND. apply HL'.
      - eapply HL. now left.
      - enough (~~ (P \/ ~P)).
        + apply H. intros Hc. apply H0. intros Hc2. apply Hc. exists [⊥]. split; try (apply Ctx; now left).
          intros ? [<- | []]. cbv. split; try apply Hc2. econstructor.
        + tauto.
    Qed.
(*
    Lemma LEM_implies_kcompleteness : LEM -> kcompleteness_arbitrary.
    Proof.
      intros Hlem T phi HT Hphi Hvalid Htheo.
      destruct (Hlem (T ⊩SE phi)); try easy. exfalso.
      apply K_std_completeness.
      intros H. destruct (Hlem (T ⊢TC phi)); tauto.
    Qed.
*)
  End LEM_Equivalence.

End KripkeCompleteness.
