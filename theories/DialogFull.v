(* *** Translating between LJ and LJD *)

From Undecidability.FOLC Require Export Sorensen.
From Undecidability.FOLC Require Export FullSequent.

Section DialogFull.
  Context {Sigma : Signature}.
  Hypothesis eq_dec_Funcs : eq_dec Funcs.
  Hypothesis eq_dec_Preds : eq_dec Preds.

  Definition atomic_form (phi : form) : Prop :=
    match phi with
    | Pred _ _ => True
    | _ => False
    end.

  Lemma atomic_dec phi :
    atomic_form phi \/ ~ atomic_form phi.
  Proof.
    destruct phi; cbn; intuition.
  Qed.

  Inductive attack_form : form -> option form -> Type :=
  | ABot : attack_form ⊥ None
  | AImpl phi psi : attack_form (phi --> psi) (Some phi)
  | AAnd phi psi : bool -> attack_form (phi ∧ psi) None
  | AOr phi psi : attack_form (phi ∨ psi) None
  | AAll phi : term -> attack_form (∀ phi) None
  | AExt phi : attack_form (∃ phi) None.

  Lemma attack_form_inv_impl phi psi adm (atk : attack_form (phi --> psi) adm)
        (P : forall chi adm, attack_form chi adm -> Type) :
    P (phi --> psi) (Some phi) (AImpl phi psi) -> P (phi --> psi) adm atk.
  Proof.
    enough (H : forall chi adm (atk : attack_form chi adm),
                chi = (phi --> psi) -> P (phi --> psi) (Some phi) (AImpl phi psi) -> P chi adm atk)
      by now apply (H (phi --> psi) adm atk).
    intros chi adm' atk' Hchi Hadm. destruct atk'; try discriminate. injection Hchi. now intros -> ->.
  Qed.

  Lemma attack_form_inv_and phi psi adm (atk : attack_form (phi ∧ psi) adm)
        (P : forall chi adm, attack_form chi adm -> Type) :
    (forall l, P (phi ∧ psi) None (AAnd phi psi l)) -> P (phi ∧ psi) adm atk.
  Proof.
    enough (H : forall chi adm (atk : attack_form chi adm),
                chi = (phi ∧ psi) -> (forall l, P (phi ∧ psi) None (AAnd phi psi l)) -> P chi adm atk)
      by now apply (H (phi ∧ psi) adm atk).
    intros chi adm' atk' Hchi Hadm. destruct atk'; try discriminate. injection Hchi. now intros -> ->.
  Qed.

  Lemma attack_form_inv_or phi psi adm (atk : attack_form (phi ∨ psi) adm)
        (P : forall chi adm, attack_form chi adm -> Type) :
    P (phi ∨ psi) None (AOr phi psi) -> P (phi ∨ psi) adm atk.
  Proof.
    enough (H : forall chi adm (atk : attack_form chi adm),
                chi = (phi ∨ psi) -> P (phi ∨ psi) None (AOr phi psi) -> P chi adm atk)
      by now apply (H (phi ∨ psi) adm atk).
    intros chi adm' atk' Hchi Hadm. destruct atk'; try discriminate. injection Hchi. now intros -> ->.
  Qed.

  Lemma attack_form_inv_all phi adm (atk : attack_form (∀ phi) adm) (P : forall chi adm, attack_form chi adm -> Type) :
    (forall t, P (∀ phi) None (AAll phi t)) -> P (∀ phi) adm atk.
  Proof.
    enough (H : forall chi adm (atk : attack_form chi adm),
                chi = ∀ phi -> (forall t, P (∀ phi) None (AAll phi t)) -> P chi adm atk)
      by now apply (H (∀ phi) adm atk).
    intros chi adm' atk' Hchi Hadm. destruct atk'; try discriminate. injection Hchi. now intros ->.
  Qed.

  Lemma attack_form_inv_ext phi adm (atk : attack_form (∃ phi) adm)
        (P : forall chi adm, attack_form chi adm -> Type) :
    P (∃ phi) None (AExt phi) -> P (∃ phi) adm atk.
  Proof.
    enough (H : forall chi adm (atk : attack_form chi adm),
                chi = (∃ phi) -> P (∃ phi) None (AExt phi) -> P chi adm atk)
      by now apply (H (∃ phi) adm atk).
    intros chi adm' atk' Hchi Hadm. destruct atk'; try discriminate. injection Hchi. now intros ->.
  Qed.

  Inductive defense_form : forall phi adm, attack_form phi adm -> form -> Prop :=
  | DImpl phi psi : defense_form (AImpl phi psi) psi
  | DAndL phi psi : defense_form (AAnd phi psi true) phi
  | DAndR phi psi : defense_form (AAnd phi psi false) psi
  | DOrL phi psi : defense_form (AOr phi psi) phi
  | DOrR phi psi : defense_form (AOr phi psi) psi
  | DAll phi t : defense_form (AAll phi t) (phi[t .: ids])
  | DExt phi t : defense_form (AExt phi) (phi [t .: ids]).

  Hint Constructors defense_form.

  Instance form_rules : rule_set form :=
    {| atomic := atomic_form ; attack := attack_form ; defense := defense_form ; dec_f := dec_form _ _ |}.

  Lemma sf_form_rules phi adm (atk : attack phi adm) :
    opred (fun a => sf a phi) adm /\ forall chi, defense atk chi -> sf chi phi.
  Proof.
    destruct atk; cbn; split; try discriminate; try (intros ?; inversion 1; constructor).
  Qed.

  Lemma eq_incl X (A B : list X) :
    A = B -> A <<= B.
  Proof.
    intros ->; intuition.
  Qed.

  Lemma fprv_Dprv A phi :
    A ⊢f phi -> forall rho, [psi[rho] | psi ∈ A] ⊢D (fun psi => psi = phi[rho]).
  Proof.
    induction 1; intros rho; cbn in *; asimpl in *.
    - apply Dprv_ax with (phi := phi[rho]) (Q := sf). apply sf_well_founded. apply sf_form_rules. all: intuition.
    - apply (Dprv_weak (IHfprv rho)). all: intuition.
    - apply (Dprv_weak (IHfprv rho)). all: intuition.
    - apply (Dprv_weak (IHfprv rho)). 2: tauto. repeat (rewrite map_app; cbn).
      intros a [? | [-> | [-> | ?]]] % in_app_or; apply in_or_app. all: eauto.
    - apply Dprv_exp with (T := @defense _ form_rules ⊥ None ABot).
      eapply (Dprv_defend (IHfprv rho)) with (adm := None). tauto. intros ?; inversion 1.
    - refine (@Dprv_just _ _ _ _ _ (phi [rho]) (Dprv_weak (IHfprv1 rho) _ (fun a H => H)) _ _);
        [intuition | intuition |]. intros B Hsub Hjust.
      apply (@Att _ form_rules _ _ (phi[rho] --> psi[rho]) (Some phi[rho]) (AImpl phi[rho] psi[rho]));
        [intuition | | |].
      + intros chi'. inversion 1; subst. apply (Dprv_weak (IHfprv2 rho)). 2: tauto. firstorder.
      + now intros ? [= <-].
      + intros ? [= <-] adm atk. refine (Dprv_weak (Dprv_defend (IHfprv1 rho) _ atk) _ _).
        tauto. destruct adm; cbn; firstorder. tauto.
    - apply (@Def _ _ _ _ (phi[rho] --> psi[rho])). reflexivity.
      firstorder. intros adm atk. apply (attack_form_inv_impl atk).
      apply (Dprv_weak (IHfprv rho)); intuition. subst. apply DImpl.
    - apply Att with (atk := AAnd phi[rho] psi[rho] true); [intuition | | discriminate | discriminate].
      intros ?. inversion 1; subst.
      apply Att with (atk := AAnd phi[rho] psi[rho] false); [intuition | | discriminate | discriminate].
      intros ?. inversion 1; subst. apply (Dprv_weak (IHfprv rho)); firstorder.
    - apply Def with (phi := phi[rho] ∧ psi[rho]). reflexivity. inversion 1.
      intros ? atk. apply (attack_form_inv_and atk); intros []; cbn.
      + apply (Dprv_weak (IHfprv1 rho)). intuition. intros ? ->. constructor.
      + apply (Dprv_weak (IHfprv2 rho)). intuition. intros ? ->. constructor.
    - apply Att with (atk := AOr phi[rho] psi[rho]); [intuition | | discriminate | discriminate].
      intros chi'; inversion 1; subst.
      + apply (Dprv_weak (IHfprv1 rho)). intuition. intros ? ->. constructor.
      + apply (Dprv_weak (IHfprv2 rho)). intuition. intros ? ->. constructor.
    - apply Def with (phi := phi[rho] ∨ psi[rho]). reflexivity. inversion 1.
      intros ? atk. apply (attack_form_inv_or atk); subst; cbn. apply (Dprv_weak (IHfprv rho)).
      reflexivity. intros ? ->; constructor.
    - apply Def with (phi := phi[rho] ∨ psi[rho]). reflexivity. inversion 1.
      intros ? atk. apply (attack_form_inv_or atk); subst; cbn. apply (Dprv_weak (IHfprv rho)).
      reflexivity. intros ? ->; constructor.
    - apply (@Att _ form_rules _ _ _ None (AAll (phi [var_term O .: rho >> (subst_term form_shift)]) (t [rho])));
        [intuition | | discriminate | discriminate].
      intros chi Hdef; inversion Hdef; subst; apply (Dprv_weak (IHfprv rho)); asimpl in *; firstorder. 
    - apply Def with (phi := ∀ (phi [var_term O .: rho >> (subst_term form_shift)])); [easy | firstorder |].
      intros adm atk. apply (attack_form_inv_all atk). intros t; cbn; asimpl.
      apply (Dprv_weak (IHfprv (t .: rho))).
      + rewrite map_map. apply eq_incl, map_ext. intros a. now asimpl.
      + intros ? ->. enough ((phi [var_term O .: rho >> (subst_term form_shift)]) [t .: ids] =
                              (subst_form (@scons term t rho) phi)) as <- by apply (DAll _ t).
        now asimpl.
    - apply Att with (atk := AExt phi[var_term O .: rho >> (subst_term form_shift)]);
        [intuition | | discriminate | discriminate].
      intros ?; inversion 1; subst; asimpl. apply (Dprv_weak (IHfprv (t .: rho))).
      + apply incl_shift, incl_tl. rewrite map_map. apply eq_incl, map_ext. intros a; now asimpl.
      + intros ? ->. now asimpl.
    - apply Def with (phi := ∃ phi[var_term O .: rho >> (subst_term form_shift)]); [easy | firstorder |].
      intros ? atk. apply (attack_form_inv_ext atk). cbn. apply (Dprv_weak (IHfprv rho)).
      reflexivity. intros ? ->. asimpl. enough ((phi [var_term O .: rho >> (subst_term form_shift)]) [t[rho] .: ids]
        = (subst_form (@scons term (subst_term rho t) rho) phi)) as <- by apply (DExt _ t[rho]).
      now asimpl.
  Qed.



  Hint Constructors fprv.

  Ltac Hatk_inv H := apply H; intros ?; inversion 1; subst; cbn; intuition.

  Lemma fprv_defend A phi :
    (forall (adm : option form) (atk : attack phi adm) (phi0 : form),
       (forall B psi, psi ∈ defense atk -> (adm o:: A) <<= B -> B ⊢f psi -> B ⊢f phi0) -> (adm o:: A) ⊢f phi0)
      -> justified _ A phi
      -> A ⊢f phi.
  Proof.
    destruct phi; intros Hatk Hjust.
    - Hatk_inv (Hatk None ABot ⊥).
    - apply (focus_el (Hjust I)), Ax.
    - apply IR. Hatk_inv (Hatk (Some phi1) (AImpl phi1 phi2)).
    - apply AR; [Hatk_inv (Hatk None (AAnd phi1 phi2 true)) | Hatk_inv (Hatk None (AAnd phi1 phi2 false))].
    - Hatk_inv (Hatk (@None form) (AOr phi1 phi2)).
    - destruct (find_unused_L (phi :: A)) as [x Hx]. apply AllR. cbn.
      apply nameless_equiv with (n := x) (A0 := A). use_free Hx. use_free Hx.
      Hatk_inv (Hatk None (AAll phi (var_term x))).
    - Hatk_inv (Hatk None (AExt phi)). eauto.
  Qed.

  Ltac use_inv H0 H1 H2 H3 H4 H :=
    revert H0 H1 H2 H3 H4; apply H; intros H0 H1 H2 H3 H4; cbn in *.

  Lemma Dprv_fprv' A T :
    A ⊢D T -> (forall phi, (forall B psi, psi ∈ T -> A <<= B -> B ⊢f psi -> B ⊢f phi) -> A ⊢f phi).
  Proof with eauto.
    induction 1.
    - intros psi Hpsi. apply (Hpsi _ _ H). 1: auto. now apply fprv_defend.
    - intros phi Hphi. destruct psi.
      + apply Exp, (focus_el H), Ax.
      + inversion atk.
      + use_inv H0 H1 H2 H3 H4 (attack_form_inv_impl atk). apply (focus_el H), IL.
        * specialize (H4 psi1 eq_refl). specialize (H2 psi1 eq_refl). now apply fprv_defend.
        * apply (H1 psi2 (DImpl psi1 psi2))...
      + use_inv H0 H1 H2 H3 H4 (attack_form_inv_and atk). intros H5. destruct H0.
        * eapply (focus_el H), AL, weaken. 1: apply (H2 psi1 (DAndL psi1 psi2))... intuition.
        * eapply (focus_el H), AL, weaken. 1: apply (H2 psi2 (DAndR psi1 psi2))... intuition.
      + use_inv H0 H1 H2 H3 H4 (attack_form_inv_or atk). apply (focus_el H), OL.
        * apply (H1 psi1 (DOrL psi1 psi2))...
        * apply (H1 psi2 (DOrR psi1 psi2))...
      + use_inv H0 H1 H2 H3 H4 (attack_form_inv_all atk). intros H5. rename H0 into t.
         apply (focus_el H), (@AllL _ _ _ _ t), (H2 (psi[t..]) (DAll psi t))...
      + use_inv H0 H1 H2 H3 H4 (attack_form_inv_ext atk). destruct (find_unused_L (psi :: phi :: A)) as [x Hx].
        apply (focus_el H), ExL, nameless_equiv' with (n := x) (A0 := A). use_free Hx. use_free Hx.
        apply (H1 (psi[(var_term x)..]) (DExt psi (var_term x)))...
  Qed.

  Lemma Dprv_fprv A phi :
    A ⊢D (fun psi => psi = phi) -> A ⊢f phi.
  Proof.
    intros H. apply (Dprv_fprv' H). now intros ? ? ->. 
  Qed.
End DialogFull.
