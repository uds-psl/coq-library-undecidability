From Undecidability Require Import TM.Util.Prelim TM.Util.Relations TM.Util.TM_facts.

(* * Alphabet-Lift *)

Section SujectTape.
  Variable sig tau : Type.
  Variable g : tau -> option sig.
  Variable def : sig.

  Definition surject : tau -> sig := fun t => match (g t) with Some s => s | None => def end.

  Definition surjectTape := mapTape surject.

End SujectTape.

#[export] Hint Unfold surjectTape : tape.


Section lift_sigma_tau.
  Variable n : nat.
  Variable sig tau : Type.
  Variable g : tau -> option sig.
  Variable def : sig.
  Variable F : Type.

  Definition surjectTapes : tapes tau n -> tapes sig n :=
    Vector.map (surjectTape g def).
  
  Definition lift_sigma_tau_Rel (R : Rel (tapes sig n) (F * tapes sig n)) :
    Rel (tapes tau n) (F * tapes tau n) :=
    fun tin '(yout,tout) => R (surjectTapes tin) (yout, surjectTapes tout).

  Definition lift_sigma_tau_T (T : Rel (Vector.t (tape sig) n) nat) :
    Rel (Vector.t (tape tau) n) nat :=
    fun tin k => T (surjectTapes tin) k.

  Lemma surjectTapes_nth t i :
    (surjectTapes t)[@i] = surjectTape g def t[@i].
  Proof. unfold surjectTapes. now simpl_vector. Qed.

End lift_sigma_tau.

Arguments surjectTapes {n sig tau} (g) def !t.
Global Hint Rewrite surjectTapes_nth : tape.


Arguments lift_sigma_tau_Rel {n sig tau} (g def) {F} (R) x y /.
Arguments lift_sigma_tau_T {n sig tau} (g def T) x y /.


Section InjectTape.

  Variable sig tau : Type.
  Variable f : sig -> tau.

  Definition injectTape := mapTape f.
  Definition injectTapes {n: nat} := mapTapes (n := n) f.
End InjectTape.

Section InjectSurject.
  Variable sig tau : Type.
  Variable inj : Retract sig tau.
  Variable def : sig.

  Lemma surject_inject' (l : list sig) :
    List.map (fun t : tau => match Retr_g t with
                          | Some s => s
                          | None => def
                          end) (List.map Retr_f l) = l.
  Proof.
    induction l; cbn.
    - reflexivity.
    - retract_adjoint. f_equal. assumption.
  Qed.
  
  Lemma surject_inject_tape (t : tape sig) :
    surjectTape Retr_g def (injectTape Retr_f t) = t.
  Proof.
    unfold surjectTape, injectTape, surject.
    destruct t; cbn; f_equal; try rewrite retract_g_adjoint; auto; apply surject_inject'.
  Qed.

  (*
  Lemma surject_inject_tapes {n : nat} (t : Vector.t (tape sig) n) :
    surjectTapes g def (injectTapes f t) = t.
  Proof.
    unfold surjectTapes, injectTapes, mapTapes.
    apply Vector.eq_nth_iff. intros p ? <-. 
    erewrite !Vector.nth_map; eauto.
    apply surject_inject_tape.
  Qed.
*)
  
End InjectSurject.

Section TranslateAct.
  Variable X Y : Type.
  Definition map_act : (X -> Y) -> option X * move -> option Y * move := fun f => map_fst (map_opt f).
End TranslateAct.


Section LiftAlphabet.
  Variable sig tau : finType.
  Variable n : nat.
  Variable F : finType.
  Variable pMSig : pTM sig F n.

  Variable Inj : Retract sig tau.

  Variable def : sig.

  Definition surjectReadSymbols : Vector.t (option tau) n -> Vector.t (option sig) n :=
    Vector.map (map_opt (surject Retr_g def)).

  Definition lift_trans :=
    fun '(q, sym) =>
      let (q', act) := trans (m := projT1 pMSig) (q, surjectReadSymbols sym) in
      (q', Vector.map (map_act Retr_f) act).

  Definition LiftAlphabet_TM : TM tau n :=
    {| trans := lift_trans;
       start := start (projT1 pMSig);
       halt := halt (m := projT1 pMSig) |}.

  Definition LiftAlphabet :pTM tau F n :=
    (LiftAlphabet_TM; projT2 pMSig).

  
  Definition surjectConf : (mconfig tau (state LiftAlphabet_TM) n) -> (mconfig sig (state (projT1 pMSig)) n) :=
    fun c => mk_mconfig (cstate c) (surjectTapes Retr_g def (ctapes c)).

  (*
  Definition injectConf : (mconfig sig (state (projT1 pMSig)) n) -> (mconfig tau (state liftM) n) :=
    fun c => mk_mconfig (cstate c) (injectTapes Retr_f (ctapes c)).
*)

  Lemma doAct_surject :
    forall (tape : tape tau) (act : option sig * move) (d : sig),
      doAct (surjectTape Retr_g d tape) act =
      surjectTape Retr_g d (doAct tape (map_act Retr_f act)).
  Proof.
    intros tape. intros (w,m) d; cbn.
    unfold surjectTape, doAct, tape_move, tape_write, surject; cbn.
    destruct tape, m, w; cbn; f_equal; try retract_adjoint; auto.
    - destruct l; cbn; f_equal; now retract_adjoint.
    - destruct l; cbn; f_equal; now retract_adjoint.
    - destruct l0; cbn; f_equal; now retract_adjoint.
    - destruct l0; cbn; f_equal; now retract_adjoint.
  Qed.

  Lemma current_chars_surjectTapes (t : tapes tau n) :
    current_chars (surjectTapes Retr_g def t) = surjectReadSymbols (current_chars t).
  Proof.
    unfold current_chars, surjectTapes, surjectReadSymbols. apply Vector.eq_nth_iff; intros i ? <-. simpl_tape.
    unfold surjectTape, surject. now simpl_tape.
  Qed.

  Lemma LiftAlphabet_comp_step (c : mconfig tau (state (projT1 pMSig)) n) :
    step (M := projT1 pMSig) (surjectConf c) = surjectConf (step (M := LiftAlphabet_TM) c).
  Proof.
    unfold surjectConf. destruct c as [q t]. cbn in *.
    unfold step. cbn -[doAct_multi].
    rewrite current_chars_surjectTapes.
    destruct (trans (q, surjectReadSymbols (current_chars t))) eqn:E. cbn.
    f_equal. unfold doAct_multi, surjectTapes. apply Vector.eq_nth_iff; intros i ? <-. simpl_tape. apply doAct_surject.
  Qed.

  Lemma LiftAlphabet_lift (c1 c2 : mconfig tau (state LiftAlphabet_TM) n) (k : nat) :
    loopM (M := LiftAlphabet_TM) c1 k = Some c2 ->
    loopM (M := projT1 pMSig) (surjectConf c1) k = Some (surjectConf c2).
  Proof.
    unfold loopM. intros H. eapply loop_lift. 3: apply H. auto.
    - intros ? _. apply LiftAlphabet_comp_step.
  Qed.

  Lemma LiftAlphabet_Realise (R : Rel (tapes sig n) (F * tapes sig n)) :
    pMSig ⊨ R ->
    LiftAlphabet ⊨ lift_sigma_tau_Rel Retr_g def R.
  Proof.
    intros H. intros t i outc Hloop. unfold lift_sigma_tau_Rel. hnf in H.
    specialize (H (surjectTapes Retr_g def t) i (mk_mconfig (cstate outc) (surjectTapes Retr_g def (ctapes outc)))).
    cbn in H. apply H.
    now apply (@LiftAlphabet_lift (initc LiftAlphabet_TM t) outc i).
  Qed.

  Lemma LiftAlphabet_unlift (k : nat) iconf (oconf : mconfig sig (state (projT1 pMSig)) n) :
    loopM (surjectConf iconf) k = Some oconf ->
    exists oconf' : mconfig tau (state LiftAlphabet_TM) n,
      loopM iconf k = Some oconf'.
  Proof.
    intros HLoop. unfold loopM in *.
    apply loop_unlift with (f := step(M:=LiftAlphabet_TM)) (h:=haltConf(M:=LiftAlphabet_TM)) in HLoop as (c'&HLoop&->); eauto.
    - intros ? _. now apply LiftAlphabet_comp_step.
  Qed.

  Lemma LiftAlphabet_TerminatesIn (T : Rel (tapes sig n) nat) :
    projT1 pMSig ↓ T ->
    projT1 LiftAlphabet ↓ lift_sigma_tau_T Retr_g def T.
  Proof.
    intros H. hnf. intros tin k HTerm. hnf in HTerm, H. specialize (H _ _ HTerm) as (oconf&HLoop).
    eapply LiftAlphabet_unlift; eauto.
  Qed.

  Lemma LiftAlphabet_RealiseIn (R : Rel (tapes sig n) (F * tapes sig n)) (k : nat) :
    pMSig ⊨c(k) R ->
    LiftAlphabet ⊨c(k) lift_sigma_tau_Rel Retr_g def R.
  Proof.
    intros [H1 H2] % Realise_total. eapply Realise_total. split; cbn in *.
    - now eapply LiftAlphabet_Realise.
    - eapply LiftAlphabet_TerminatesIn in H2. auto.
  Qed.

End LiftAlphabet.

Arguments LiftAlphabet : simpl never.

Ltac smpl_TM_LiftAlphabetSigma :=
  once lazymatch goal with
  | [ |- LiftAlphabet _ _ _ ⊨ _] => eapply LiftAlphabet_Realise; swap 1 2
  | [ |- LiftAlphabet _ _ _ ⊨c(_) _] => eapply LiftAlphabet_RealiseIn; swap 1 2
  | [ |- projT1 (LiftAlphabet _ _ _) ↓ _] => eapply LiftAlphabet_TerminatesIn; swap 1 2
  end.
Smpl Add smpl_TM_LiftAlphabetSigma : TM_Correct.
