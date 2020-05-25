From Undecidability.FOLC Require Import ND GenTarski GenCompleteness FullND FullTarski.

Section DM.

  Context { Sigma : Signature }.

  Fixpoint DM (phi : form) : form :=
    match phi with 
    | Pred P v => Pred P v
    | ⊥ => ⊥
    | phi --> psi => DM phi --> DM psi
    | phi ∧ psi => ¬ (DM phi --> ¬ DM psi)
    | phi ∨ psi => ¬ DM phi --> DM psi
    | ∀ phi => ∀ DM phi
    | ∃ phi => ¬ (∀ ¬ DM phi)
    end.

  Lemma DM_prv A phi :
    A ⊢CE phi <-> A ⊢CE DM phi.
  Proof.
    induction phi in A |- *; cbn; try tauto.
    - split; intros H.
      + ointros. oimport H. apply IHphi2. oapply 0. apply IHphi1. ctx.
      + ointros. oimport H. apply IHphi2. oapply 0. apply IHphi1. ctx.
    - split; intros H.
      + ointros. eapply IE. oapply 0.
        * apply IHphi1. eapply CE1, (Weak H). auto.
        * apply IHphi2. eapply CE2, (Weak H). auto.
      + oimport H. osplit; oindirect.
        * oapply 1. ointros. oapply 2. apply IHphi1. ctx.
        * oapply 1. ointros. oapply 2. apply IHphi2. ctx.
    - split; intros H.
      + ointros. eapply DE. apply (Weak H). auto.
        * oexfalso. oapply 1. apply IHphi1. ctx.
        * apply IHphi2. ctx.
      + oxm phi1. oleft. ctx.
        oright. apply IHphi2. oimport H. oapply 0.
        ointros. oapply 2. apply IHphi1. ctx.
    - split; intros H.
      + oimport H. ointros. ospecialize 0 (var_term 0). apply IHphi. ctx.
      + oimport H. ointros. ospecialize 0 (var_term 0). apply IHphi. ctx.
    - split; intros H.
      + apply (ExE H). asimpl. ointros. cbn. ointros.
        ospecialize 0 (var_term 0). oapply 0. apply IHphi. ctx.
      + oindirect. oimport H. oapply 0. ointros. oapply 2.
        apply (ExI (t:=var_term 0)). asimpl. apply IHphi. ctx.
  Qed.
  
  Fixpoint convert (phi : form) : Syntax.form :=
    match phi with 
    | Pred P v => Syntax.Pred P v
    | phi --> psi => Syntax.Impl (convert phi) (convert psi)
    | ∀ phi => Syntax.All (convert phi)
    | _ => Syntax.Fal
    end.

  Fixpoint embed (phi : Syntax.form) : form :=
    match phi with 
    | Syntax.Pred P v => Pred P v
    | Syntax.Impl phi psi => embed phi --> embed psi
    | Syntax.All phi => ∀ embed phi
    | Syntax.Fal => ⊥
    end.

  Lemma convert_embed phi :
    convert (embed phi) = phi.
  Proof.
    induction phi; cbn; intuition congruence.
  Qed.

  Definition DMT phi :=
    convert (DM phi).

  Lemma embed_DMT phi :
    embed (DMT phi) = DM phi.
  Proof.
    unfold DMT. induction phi; cbn; intuition congruence.
  Qed.

  Lemma DMT_subst sigma phi :
    DMT phi[sigma] = (DMT phi)[sigma].
  Proof.
    induction phi in sigma |- *; cbn; unfold DMT in *.
    1, 2: reflexivity.
    1, 2, 3: now rewrite IHphi1, IHphi2.
    1, 2: now rewrite IHphi.
  Qed.

  Lemma incl_eq X (A B : list X) :
    A = B -> A <<= B.
  Proof.
    now intros ->.
  Qed.

  Lemma DMT_prv A phi :
    A ⊢CE phi -> @ND.prv _ ND.class ND.expl (map DMT A) (DMT phi).
  Proof.
    induction 1; cbn in *.
    - apply ND.II. apply (ND.Weak IHprv). auto.
    - apply (ND.IE IHprv1 IHprv2).
    - apply ND.AllI. apply (ND.Weak IHprv).
      rewrite !map_map. apply incl_eq, map_ext, DMT_subst.
    - rewrite DMT_subst. eapply ND.AllE. apply IHprv.
    - eapply ND.ExI. rewrite DMT_subst in IHprv. apply IHprv.
    - eapply (ND.ExE IHprv1); fold DM convert. rewrite <- DMT_subst.
      apply (ND.Weak IHprv2). cbn. apply incl_shift.
      rewrite !map_map. apply incl_eq, map_ext, DMT_subst.
    - eapply ND.Exp. apply IHprv.
    - apply ND.Ctx. now apply in_map.
    - ND.ointros. eapply ND.IE. ND.oapply 0.
      + ND.ouse IHprv1.
      + ND.ouse IHprv2.
    - ND.oindirect. ND.oimport IHprv. ND.oapply 0.
      ND.ointros. ND.oapply 3. ND.ctx.
    - ND.oindirect. ND.oimport IHprv. ND.oapply 0.
      ND.ointros. ND.oapply 3. ND.ctx.
    - ND.ointros. ND.oexfalso. ND.oapply 0. ND.ouse IHprv.
    - ND.ointros. ND.ouse IHprv.
    - ND.oxm (DMT phi); try apply IHprv2. ND.oxm (DMT psi).
      + ND.ouse IHprv3.
      + ND.oexfalso. ND.oapply 0. ND.oimport IHprv1. ND.oapply 0. ND.ctx.
    - apply ND.Pc.
  Qed.

  Lemma embed_subst sigma phi :
    embed phi[sigma] = (embed phi)[sigma].
  Proof.
    induction phi in sigma |- *; cbn; try reflexivity.
    - now rewrite IHphi1, IHphi2.
    - now rewrite IHphi.
  Qed.

  Lemma embed_prv A phi :
    @ND.prv _ ND.class ND.expl A phi -> (map embed A) ⊢CE (embed phi).
  Proof.
    induction 1; cbn.
    - apply II. apply (Weak IHprv). reflexivity.
    - apply (IE IHprv1 IHprv2).
    - apply AllI. apply (Weak IHprv).
      rewrite !map_map. apply incl_eq, map_ext, embed_subst.
    - setoid_rewrite embed_subst. apply (AllE t IHprv).
    - apply Exp, IHprv.
    - apply Pc.
    - apply Ctx, in_map, H.
  Qed.

  Definition DN := forall P, ~ ~ P -> P.

  Definition XM := forall P, P \/ ~ P.

  Lemma XM_DN :
    XM <-> DN.
  Proof.
    split.
    - intros H X HX. destruct (H X); tauto.
    - intros H X. apply H. tauto.
  Qed.

  Lemma DMT_sat D (I : interp D) rho phi :
    DN -> standard_bot I -> sat rho phi <-> GenTarski.sat rho (DMT phi).
  Proof.
    intros HDN HI. unfold standard_bot in HI.
    induction phi in rho |- *; cbn; try specialize (IHphi1 rho); try specialize (IHphi2 rho); try tauto.
    - split; try tauto. split; apply HDN; tauto.
    - split; try tauto. intros H. apply HDN. tauto.
    - firstorder tauto.
    - split; try firstorder tauto. intros H. apply HDN. firstorder tauto.
  Qed.

  Definition DMTT T :=
    fun phi => exists psi, T psi /\ phi = DMT psi.

  Lemma DMT_valid T phi :
    DN -> valid_T classical T phi -> DMTT T ⊫S DMT phi.
  Proof.
    intros HDN H D I [H1 H2] rho HT. apply DMT_sat; trivial. apply H.
    - intros rho' psi theta. cbn. apply HDN. tauto.
    - intros psi HP. apply DMT_sat; trivial. apply HT. now exists psi.
  Qed.

  Lemma DMT_incl T A :
    FOL.contains_L A (DMTT T) -> exists B, B ⊏ T /\ A = map DMT B.
  Proof.
    induction A; intros H.
    - exists nil. split; trivial. now intros phi [].
    - assert (DMTT T a) as [phi[HP ->]] by now apply H.
      destruct IHA as [B[HB ->]]. firstorder.
      exists (phi::B). split; trivial. intros psi [->|]; auto.
  Qed.

  Lemma prv_cut_list {p b} A B phi :
    A ⊢(p, b) phi -> (forall psi, psi el A -> B ⊢(p, b) psi) -> B ⊢(p, b) phi.
  Proof.
    induction 1 in B |- *; intros HA.
    - apply II, IHprv. intros theta [->|HT]; try now ctx. ouse (HA theta HT).
    - eapply IE; eauto.
    - apply AllI, IHprv. intros psi [theta[<- HT]] % in_map_iff. now apply subst_Weak, HA.
    - now apply AllE, IHprv.
    - now eapply ExI, IHprv.
    - eapply ExE; try now apply IHprv1. apply IHprv2. intros psi' [<-|[theta[<- HT]] % in_map_iff]; try now ctx.
      eapply Weak; try now apply incl_tl; try reflexivity. now apply subst_Weak, HA.
    - now apply Exp, IHprv.
    - now apply HA.
    - apply CI; auto.
    - now eapply CE1, IHprv.
    - now eapply CE2, IHprv.
    - now eapply DI1, IHprv.
    - now eapply DI2, IHprv.
    - eapply DE; try now apply IHprv1.
      + apply IHprv2. intros theta' [->|HT]; try now ctx. ouse (HA theta' HT).
      + apply IHprv3. intros theta' [->|HT]; try now ctx. ouse (HA theta' HT).
    - apply Pc.
  Qed.

  Lemma DMT_unused phi n :
    unused n phi -> FOL.unused n (DMT phi).
  Proof.
    induction 1; cbn; repeat constructor; assumption.
  Qed.

  Lemma DMT_closed phi :
    closed phi -> FOL.closed (DMT phi).
  Proof.
    intros H n. apply DMT_unused, H.
  Qed.
  
  Context {HdF : eq_dec Funcs} {HdP : eq_dec Preds}.
  Context {HeF : enumT Funcs} {HeP : enumT Preds}.

  Theorem full_completeness T phi :
    DN -> closed_T T -> closed phi -> valid_T classical T phi -> T ⊩CE phi.
  Proof.
    intros HDN HT HP H % DMT_valid; trivial.
    apply semi_completeness_standard in H.
    - apply HDN in H as [A[H1 H2 % embed_prv]]. apply DMT_incl in H1 as [B[HB ->]].
      exists B. split; trivial. apply DM_prv. rewrite embed_DMT in H2. apply (prv_cut_list H2).
      rewrite map_map. intros psi [theta[<- H]] % in_map_iff. rewrite embed_DMT. apply -> DM_prv. now apply Ctx.
    - intros psi n [theta[H' ->]]. now apply DMT_unused, HT.
    - now apply DMT_closed.
  Qed.

End DM.

Print Assumptions full_completeness.

Lemma DMT_sat_back :
  (forall (Sigma : Signature) D (I : interp D) rho phi, standard_bot I -> sat rho phi <-> GenTarski.sat rho (DMT phi)) -> XM.
Proof.
  intros H P.
  pose (Sigma := B_S False (@except nat) unit (fun _ => 0)).
  pose (I := B_I (fun _ _ => tt) (fun _ _ => P) False).
  pose (phi := Pred tt Vector.nil).
  apply (H Sigma unit I (fun _ => tt) (phi ∨ ¬ phi)).
  - intros [].
  - cbn. tauto.
Qed.
