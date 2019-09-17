From Undecidability.FOL Require Export DecidableEnumerable.

(* * Dialogue Semantics *)

(* ** Generalized Intuitionistic E-Completeness *)

Definition ocons X (o : option X) A :=
  match o with
  | Some a => a :: A
  | None => A
  end.
Infix "o::" := ocons (at level 55).

Lemma ocons_sub X (a : option X) A B :
  A <<= B -> a o:: A <<= a o:: B.
Proof.
  intros H. destruct a; cbn.
  - intros y []; subst; intuition.
  - assumption.
Qed.

(* *** Generalized Intuitionistic E-Dialogues *)

Class rule_set (f : Type) :=
  {
    atomic : f -> Prop ;
    attack : f -> option f -> Type ;
    defense : forall phi adm, attack phi adm -> f -> Prop ;
    dec_f : eq_dec f
  }.

Definition opred X (p : X -> Prop) (o : option X) : Prop :=
  forall x, o = Some x -> p x.

Section EGame.
  Variable f : Type.
  Variable R : rule_set f.

  Definition justified A phi := atomic phi -> phi el A.

  Lemma justified_weak A B phi :
    justified A phi -> A <<= B -> justified B phi.
  Proof.
    intros Hjust Hsub Hin. intuition.
  Qed.

  Inductive challenge : Type :=
    C phi adm : attack phi adm -> challenge.

  Inductive opening phi : list f -> challenge -> Type :=
    OP (H : justified nil phi) adm (atk : attack phi adm) : opening phi (adm o:: nil) (C atk).

  Inductive epmove : list f -> challenge -> Type :=
  | EPAtk A c phi adm : phi el A -> opred (justified A) adm -> attack phi adm -> epmove A c
  | EPDef A phi adm (atk : attack phi adm) psi : justified A psi -> defense atk psi -> epmove A (C atk).

  Inductive eomove : forall A c,  epmove A c -> list f -> challenge -> Type :=
  | EODef A c phi adm H H' (atk : attack phi adm) psi :
      defense atk psi -> @eomove A _ (EPAtk c H H' atk) (psi :: A) c
  | EOCounter A c phi psi H H' (atk : attack phi (Some psi)) adm (atk' : attack psi adm) :
      @eomove A _ (EPAtk c H H' atk) (adm o:: A) (C atk')
  | EOAtk A phi adm (atk : attack phi adm) psi (H : justified A psi) (def : defense atk psi) adm'
         (atk' : attack psi adm') :
      eomove (EPDef H def) (adm' o:: A) (C atk').

  Inductive ewin_strat A c : Prop :=
    EWS (pm : epmove A c) : (forall A' c', eomove pm A' c' -> ewin_strat A' c') -> ewin_strat A c.

  Definition evalid phi :=
    justified nil phi /\ forall A c, opening phi A c -> ewin_strat A c.
End EGame.

(* *** Dialogical Sequent Calculus *)

Section LJD.
  Variable f : Type.
  Variable R : rule_set f.

  Inductive Dprv (A : list f) (T : f -> Prop): Prop :=
    Def phi :
      T phi ->
      justified _ A phi ->
      (forall adm (atk : attack phi adm), Dprv (adm o:: A) (defense atk)) ->
      Dprv A T
  | Att psi adm (atk : attack psi adm) :
      psi el A ->
      (forall chi, defense atk chi -> Dprv (chi :: A) T) ->
      opred (fun a => justified _ A a) adm ->
      opred (fun a => forall adm' (atk' : attack a adm'), Dprv (adm' o:: A) (defense atk')) adm ->
      Dprv A T.
  Notation "A '⊢D' T" := (Dprv A T) (at level 30).

(* *** Soundness and Completeness *)

  Lemma Dprv_ewin A T :
    A ⊢D T -> forall phi adm (atk : attack phi adm), (forall psi, T psi -> defense atk psi) -> ewin_strat A (C atk).
  Proof.
    induction 1.
    - intros psi adm atk Hdef. apply EWS with (pm := (EPDef H0 (Hdef _ H))).
      intros A' c'. inversion 1; subst. now apply (H2 adm' atk').
    - intros xi adm' atk' Hdef. apply EWS with (pm := (EPAtk _ H H2 atk)).
        intros A' c'. intros Hinv. revert H1 H4. inversion Hinv; subst; intros IH IH'.
        (* Opponent defends *)
        * enough (atk1 = atk) as -> by now apply IH.
          do 2 eapply Eqdep_dec.inj_pair2_eq_dec in H10.
          assumption. apply option_eq_dec. all: exact dec_f.
        (* Opponent countered  *)
        * now apply (IH' psi0 eq_refl adm0 atk'0).
  Qed.

  Lemma esoundsess phi :
    nil ⊢D (fun psi => psi = phi) -> evalid _ phi.
  Proof.
    inversion 1; subst.
    - split; [exact H1 |]; intros A c [Hjust adm atk].
      specialize (H2 adm atk); now apply (Dprv_ewin H2).
    - contradiction H0.
  Qed.

  Lemma ewin_Dprv A c :
    ewin_strat A c -> match c with C atk => A ⊢D (defense atk) end.
  Proof.
    induction 1. revert H H0; destruct pm; intros Hwin IH.
      (* Player attacks *)
    - destruct c as [psi adm' atk]. apply (@Att _ _ phi adm a); intuition.
      + apply (IH _ (C atk)). apply (EODef (C atk) i o H).
      + intros chi -> adm'' atk'. apply (IH _ (C atk')). apply EOCounter.
      (* Player defends *)
    - apply (@Def _ _ psi); intuition. apply (IH _ (C atk0)). apply EOAtk.
  Qed.

  Lemma ecompleteness phi :
    evalid _ phi -> nil ⊢D (fun psi => psi = phi).
  Proof.
    intros [Hjust Hwin]. apply (@Def _ _ phi); intuition. 
    specialize (Hwin _ _ (OP Hjust atk)).
    apply (ewin_Dprv Hwin).
  Qed.

  Lemma Dprv_weak A B (T T' : f -> Prop) :
    Dprv A T -> A <<= B -> (forall phi, T phi -> T' phi) -> Dprv B T'.
  Proof.
    intros H; revert T' B; induction H; intros T' B Hsub Himp.
    - apply (Def (Himp phi H)). now apply (justified_weak H0).
      intros. apply (H2 adm atk); eauto using ocons_sub.
    - apply (@Att _ _ _ _ atk). now apply Hsub.
      intros. apply (H1 chi). assumption. intuition.
      assumption. unfold opred. eauto using justified_weak.
      intros a Ha adm' atk'. apply (H4 _ Ha adm' atk'); eauto using ocons_sub.
  Qed.

  Lemma Dprv_defend A T phi :
    Dprv A T -> (forall psi, T psi -> psi = phi) -> forall adm (atk : attack phi adm), Dprv (adm o:: A) (defense atk).
  Proof.
    induction 1; intros HT adm' atk'.
    - rewrite (HT phi0 H) in *. apply H1.
    - apply Att with (atk := atk).
      + destruct adm'; cbn; intuition.
      + intros chi Hchi. apply (Dprv_weak (H1 chi Hchi HT adm' atk')).
        * destruct adm'; cbn; intuition.
        * intuition.
      + intros ? ->. apply (justified_weak (H2 x eq_refl)).
        destruct adm'; cbn; intuition.
      + intros ? -> adm1 atk1. apply (Dprv_weak (H3 x eq_refl adm1 atk1)).
        destruct adm1, adm'; cbn; intuition. intuition.
  Qed.

  Lemma Dprv_exp A T :
    Dprv A T -> (forall phi, ~ T phi) -> forall T', Dprv A T'.
  Proof.
    intros Hprv Hep T'. apply (Dprv_weak Hprv); firstorder.
  Qed.

  Lemma Dprv_echo (Q : f -> f -> Prop) phi :
    well_founded Q ->
    (forall phi adm (atk : attack phi adm), opred (fun a => Q a phi) adm /\ forall chi, defense atk chi -> Q chi phi) ->
    forall A, phi el A -> forall adm (atk : attack phi adm), Dprv (adm o:: A) (defense atk).
  Proof.
    intros Hwf Hdes. induction (Hwf phi) as [phi H IH]. intros A Hel.
    - intros adm atk. apply Att with (atk := atk); destruct (Hdes phi adm atk) as (Hadm & Hdefs).
      + destruct adm; cbn; intuition.
      + intros chi Hdef. apply Def with (phi := chi); unfold justified; intuition.
      + intros ? -> _; cbn; intuition.
      + intros ? -> adm' atk'; cbn. apply (IH x (Hadm x eq_refl)). intuition.
  Qed.

  Lemma Dprv_ax A (T : f -> Prop) (Q : f -> f -> Prop) phi :
    well_founded Q ->
    (forall phi adm (atk : attack phi adm), opred (fun a => Q a phi) adm /\ forall chi, defense atk chi -> Q chi phi) ->
    phi el A -> T phi -> Dprv A T.
  Proof.
    intros Hwf Hdes Hin HT. apply Def with (phi := phi); unfold justified; eauto using Dprv_echo.
  Qed.

  Lemma Dprv_just A T T' phi :
    Dprv A T -> (forall psi, T psi -> psi = phi) -> (forall B, A <<= B -> justified _ B phi -> Dprv B T') -> Dprv A T'.
  Proof.
    induction 1; intros HT HT'.
    - rewrite (HT _ H) in *; apply (HT' A); intuition.
    - apply Att with (atk := atk); intuition.
      apply H1. assumption. apply HT. intros. apply HT'; firstorder.
  Qed.


End LJD.
Notation "A '⊢D' T" := (Dprv _ A T) (at level 30).

(* ** Generalized Intuitionistic D-Completeness *)

(* *** Generalized Intuitionistic D-Dialogues *)

Section DGame.
  Variable f : Type.
  Variable R : rule_set f.

  Definition dstate : Type := list f * list (challenge _) * list f * list (challenge _).
  Inductive dpmove : dstate -> dstate -> Type :=
  | DPAtk pA pC oA oC phi adm (atk : attack phi adm) :
      phi el oA -> opred (justified _ oA) adm -> dpmove (pA, pC, oA, oC) (adm o:: pA, pC, oA, C atk :: oC)
  | DPDef pA pC oA oC phi adm (atk : attack phi adm) psi :
      justified _ oA psi -> defense atk psi -> dpmove (pA, C atk :: pC, oA, oC) (psi :: pA, pC, oA, oC).

  Inductive domove : dstate -> dstate -> Type :=
  | DOAtk pA pA' pC oA oC phi adm (atk : attack phi adm) :
      domove (pA ++ phi :: pA', pC, oA, oC) (pA ++ pA', C atk :: pC, adm o:: oA, oC)
  | DODef pA pC oA oC phi adm (atk : attack phi adm) psi :
      defense atk psi -> domove (pA, pC, oA, C atk :: oC) (pA, pC, psi :: oA, oC).

  Inductive dwin_strat s : Prop :=
    DWS s' : dpmove s s' -> (forall s'', domove s' s'' -> dwin_strat s'') -> dwin_strat s.

  Definition dvalid phi :=
    justified _ nil phi /\ forall A c, opening phi A c -> dwin_strat (nil, c :: nil, A, nil).

  Definition dwin_Dprv_embed (s : dstate) :=
    match s with
    | (_, C atk :: _, A, _) => A ⊢D (defense atk)
    | (_, nil, _, _) => True
    end.
  Lemma dwin_Dprv s :
    dwin_strat s -> dwin_Dprv_embed s.
  Proof.
    induction 1. revert H H0; destruct X; intros Hwin IH.
      (* Player attacks *)
    - destruct pC as [| [psi adm' atk'] pC]; [exact I |]; cbn.
      apply (@Att _ _ _ _ phi adm atk); intuition.
      + apply (IH (adm o:: pA, C atk' :: pC, chi :: oA, oC)). apply (DODef _ _ _ _  H).
      + intros chi -> adm'' atk''. apply (IH (pA, C atk'' :: C atk' :: pC, adm'' o:: oA, C atk :: oC)).
        cbn. apply (DOAtk nil pA _ _ _ atk'').
      (* Player defends *)
    - apply (@Def _ _ _ _ psi); intuition. apply (IH (pA, C atk0 :: pC, adm0 o:: oA, oC)).
      apply (DOAtk nil pA _ _ _ atk0).
  Qed.

  Lemma dcompleteness phi :
    dvalid phi -> nil ⊢D (fun psi => psi = phi).
  Proof.
    intros [Hjust Hwin]. apply (@Def _ _ _ _ phi); intuition.
    specialize (Hwin _ _ (OP Hjust atk)). apply (dwin_Dprv Hwin).
  Qed.

  Lemma split_right (X Y : Type) (A : list (X * Y)) b (B : list X) (C : list Y) :
    split A = (b :: B, C) -> exists A' c C', A = (b, c) :: A' /\ C = c :: C'.
  Proof.
    destruct A as [| [b' c] A']; cbn; try discriminate. destruct (split A'), C as [| c' C']; cbn; try discriminate.
    intros [= -> -> -> ->]. exists A'. exists c'. now exists C'.
  Qed.
End DGame.

(* *** Soundness and Completeness **)

Section SGame.
  Variable f : Type.
  Variable R : rule_set f.

  Definition deferred : Type := challenge _ * challenge _.
  Definition sstate : Type := list f * list f * list deferred.

  Inductive spmove : sstate -> challenge _ -> sstate -> Type :=
  | SPAtk pA oA ds c phi adm (atk : attack phi adm) :
      phi el oA -> opred (justified _ oA) adm -> spmove (pA, oA, ds) c (adm o:: pA, oA, (C atk, c) :: ds)
  | SPDef pA oA ds phi adm (atk : attack phi adm) psi :
      defense atk psi -> justified _ oA psi -> spmove (pA, oA, ds) (C atk) (psi :: pA, oA, ds).

  Inductive somove : sstate -> sstate -> challenge _ -> Type :=
  | SODef pA oA ds c phi adm (atk : attack phi adm) psi :
      defense atk psi -> somove (pA, oA, (C atk, c) :: ds) (pA, psi :: oA, ds) c
  | SOAtk pA phi pA' oA ds adm (atk : attack phi adm) :
      somove (pA ++ phi :: pA', oA, ds) (pA ++ pA', adm o:: oA, ds) (C atk).

  Inductive swin_strat s c : Prop :=
    SWS s' : spmove s c s' -> (forall s'' c', somove s' s'' c' -> swin_strat s'' c') -> swin_strat s c.

  Definition svalid phi :=
    justified _ nil phi /\ forall A c, opening phi A c -> swin_strat (nil, A, nil) c.

  Definition swin_dwin_embed s c :=
    match s with
    | (pA, oA, ds) => match split ds with (oC, pC) => dwin_strat (pA, c :: pC, oA, oC) end
    end.
  Lemma swin_dwin s c :
    swin_strat s c -> swin_dwin_embed s c.
  Proof.
    induction 1. inversion X; subst; cbn; destruct (split ds) as [oC pC] eqn:Hds.
    (* Player attacks *)
    - apply (DWS (DPAtk pA (c :: pC) oC atk H1 H2)).
      intros s''. inversion 1; subst.
      (* Opponent attacks *)
      + rewrite <- H4 in H0. specialize (H0 (pA0 ++ pA', adm0 o:: oA, (C atk, c) :: ds) (C atk0)).
        specialize (H0 (SOAtk pA0 pA' oA ((C atk, c) :: ds) atk0)). cbn in H0. now rewrite Hds in H0.
      (* Opponent defends *)
      + assert (atk1 = atk) as ->.
        { do 2 eapply Eqdep_dec.inj_pair2_eq_dec in H9. assumption. apply option_eq_dec. all: exact dec_f. }
        specialize (H0 (adm o:: pA, psi :: oA, ds) c (SODef (adm o:: pA) oA ds c H11)). cbn in H0.
        now rewrite Hds in H0.
    (* Player defends *)
    - apply (DWS (DPDef pA pC oC H2 H1)). intros s''. inversion 1; subst.
      (* Opponent attacks *)
      + rewrite <- H4 in *. specialize (H0 (pA0 ++ pA', adm0 o:: oA, ds) (C atk0)).
        specialize (H0 (SOAtk pA0 pA' oA ds atk0)). cbn in H0. now rewrite Hds in H0.
      (* Opponent defends *)
      + destruct (split_right Hds) as (ds' & [? ? atk'] & pC' & -> & ->).
        specialize (H0 (psi :: pA, psi0 :: oA, ds') (C atk') (SODef (psi :: pA) oA ds' (C atk') H8)). cbn in H0.
        enough (Heq : split ds' = (oC0, pC')) by now rewrite Heq in H0. cbn in Hds; destruct (split ds'); congruence.
  Qed.

  Lemma svalid_dvalid phi :
    svalid phi -> dvalid _ phi.
  Proof.
    intros []. constructor. assumption. intros. now apply (@swin_dwin ([], A, []) c), H0.
  Qed.
End SGame.
