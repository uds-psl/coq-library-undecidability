(** ** Translating between LJT and LJD *)

From Undecidability.FOLC Require Import Sorensen.
From Undecidability.FOLC Require Import Gentzen.

Section DialogFragment.
  Context {Sigma : Signature}.
  Context {HdF : eq_dec Funcs} {HdP : eq_dec Preds}.

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
  | AAll phi : term -> attack_form (∀ phi) None.

  Lemma attack_form_inv_impl phi psi adm (atk : attack_form (phi --> psi) adm)
        (P : forall chi adm, attack_form chi adm -> Type) :
    P (phi --> psi) (Some phi) (AImpl phi psi) -> P (phi --> psi) adm atk.
  Proof.
    enough (H : forall chi adm (atk : attack_form chi adm),
                chi = (phi --> psi) -> P (phi --> psi) (Some phi) (AImpl phi psi) -> P chi adm atk)
      by now apply (H (phi --> psi) adm atk).
    intros chi adm' atk' Hchi Hadm. destruct atk'; [discriminate | | discriminate].
    injection Hchi. now intros -> ->.
  Qed.

  Lemma attack_form_inv_all phi adm (atk : attack_form (∀ phi) adm) (P : forall chi adm, attack_form chi adm -> Type) :
    (forall t, P (∀ phi) None (AAll phi t)) -> P (∀ phi) adm atk.
  Proof.
    enough (H : forall chi adm (atk : attack_form chi adm),
                chi = ∀ phi -> (forall t, P (∀ phi) None (AAll phi t)) -> P chi adm atk)
      by now apply (H (∀ phi) adm atk).
    intros chi adm' atk' Hchi Hadm. destruct atk'; [discriminate | discriminate |].
    injection Hchi. now intros ->.
  Qed.

  Inductive defense_form : forall phi adm, attack_form phi adm -> form -> Prop :=
  | DImpl phi psi : defense_form (AImpl phi psi) psi
  | DAll phi t : defense_form (AAll phi t) (phi[t .: ids]).

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

  Lemma sprv_Dprv A phi psi :
    sprv expl A phi psi -> forall rho, Dprv form_rules (List.map (subst_form rho) (phi o:: A)) (fun chi => chi = psi [rho]).
  Proof.
    induction 1; intros rho; cbn in *; asimpl in *.
    - apply (Dprv_weak (IHsprv rho)). intros x []; subst; intuition (now apply in_map). tauto.
    - apply (@Def _ _ _ _ (phi[rho] --> psi[rho])). reflexivity.
      firstorder. intros adm atk. apply (attack_form_inv_impl atk).
      apply (Dprv_weak (IHsprv rho)); intuition. subst. apply DImpl.
    - apply Def with (phi := ∀ (phi [var_term O .: rho >> (subst_term form_shift)])); [easy | firstorder |].
      intros adm atk. apply (attack_form_inv_all atk). intros t; cbn; asimpl.
      apply (Dprv_weak (IHsprv (t .: rho))).
      + rewrite map_map. apply eq_incl, map_ext. intros a. now asimpl.
      + intros ? ->. enough ((phi [var_term O .: rho >> (subst_term form_shift)]) [t .: ids] =
                              (subst_form (@scons term t rho) phi)) as <- by apply (DAll _ t).
        now asimpl.
    - apply Dprv_exp with (T := @defense _ form_rules ⊥ None ABot).
      eapply (Dprv_defend (IHsprv rho)) with (adm := None). tauto. intros ?; inversion 1.
    - apply (@Dprv_ax _ form_rules _ _ _ (phi [rho]) sf_well_founded sf_form_rules); intuition.
    - refine (@Dprv_just _ _ _ _ _ (phi [rho]) (Dprv_weak (IHsprv1 rho) _ (fun a H => H)) _ _);
        [intuition | intuition |]. intros B Hsub Hjust.
      apply (@Att _ form_rules _ _ (phi[rho] --> psi[rho]) (Some phi[rho]) (AImpl phi[rho] psi[rho]));
        [intuition | | |].
      + intros chi. inversion 1; subst. apply (Dprv_weak (IHsprv2 rho)). 2: tauto. firstorder.
      + now intros ? [= <-].
      + intros ? [= <-] adm atk. refine (Dprv_weak (Dprv_defend (IHsprv1 rho) _ atk) _ _).
        tauto. destruct adm; cbn; firstorder. tauto.
    - apply (@Att _ form_rules _ _ _ None (AAll (phi [var_term O .: rho >> (subst_term form_shift)]) (t [rho])));
        [intuition | | discriminate | discriminate].
      intros chi Hdef; inversion Hdef; subst; apply (Dprv_weak (IHsprv rho)); asimpl in *; firstorder. 
  Qed.

  Lemma ND_defend A phi :
    (forall adm (atk : attack phi adm), (exists psi, defense atk psi /\ (adm o:: A) ⊢IE psi) \/ forall phi, (adm o:: A) ⊢IE phi) ->
    justified _ A phi -> A ⊢IE phi.
  Proof.
    destruct phi; intros Hatk Hjust.
    - destruct (Hatk None ABot) as [(phi & Hdef & _) | Hprv]; [inversion Hdef | apply Hprv].
    - ctx. now apply Hjust.
    - destruct (Hatk (Some phi1) (AImpl phi1 phi2)) as [(psi & Hdef & Hprv) | Hprv];
      try inversion Hdef; subst; apply II, Hprv.
    - ointros. destruct (find_unused_L (phi :: A)) as [x Hx]. apply (@nameless_equiv _ intu expl A phi x).
      + intros psi Hel. apply (Hx x (le_n x)). now right.
      + apply (Hx (S x)). omega. now left.
      + destruct (Hatk None (AAll phi (var_term x))) as [(psi & Hdef & Hprv) | Hprv].
        try inversion Hdef; subst; apply Hprv. apply Hprv.
  Qed.

  Lemma Dprv_ND A T :
    Dprv form_rules A T -> (exists phi, T phi /\ A ⊢IE phi) \/ forall phi, A ⊢IE phi.
  Proof.
    induction 1.
    - left; exists phi; split; [assumption |]. now apply ND_defend.
    - destruct psi; inversion atk; subst.
      + right. intros phi. oexfalso. now ctx.
      + specialize (H4 psi1 eq_refl). specialize (H2 psi1 eq_refl). assert (A ⊢IE psi1) by now apply ND_defend.
        revert H1. apply (attack_form_inv_impl atk). intros IH.
        destruct (IH psi2 (DImpl psi1 psi2)) as [(phi & HT & Hprv) | Hprv].
        * left; exists phi; split; [exact HT |]. oassert psi2. eapply IE. ctx. assumption. assumption.
        * right. intros phi. oassert psi2. eapply IE. ctx. assumption. apply Hprv.
      + revert H1. apply (attack_form_inv_all atk). intros t IH.
        destruct (IH (psi [t .: ids]) (DAll psi t)) as [(phi & HT & Hprv) | Hprv]; [left | right].
        * exists phi; split; [exact HT |]. oassert (psi [t..]). apply (AllE t). now ctx. assumption.
        * intros phi. oassert (psi [t..]). apply (AllE t). now ctx. apply Hprv.
  Qed.
End DialogFragment.
