From Undecidability Require Export TM.Util.TM_facts.
Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.DepPairs EqdepFacts.

Section While.

  Variable n : nat.
  Variable sig : finType.

  Variable F : finType.
  (** Label [None] indicates continueing, [Some f] means breaking out of the loop and terminating in the label [f]. *)
  Variable pM : pTM sig (option F) n.

  Definition While_trans :
    (TM.state (projT1 pM)) * Vector.t (option sig) n ->
    (TM.state (projT1 pM)) * Vector.t (option sig * move) n :=
    fun '(q,s) =>
      if halt q
      then (start (projT1 pM), nop_action)
      else trans (q,s).

  Definition WhileTM : TM sig n :=
    Build_TM While_trans (start (projT1 pM))
              (fun q => halt q && match projT2 pM q with
                               | Some _ => true
                               | None => false
                               end).

  Hypothesis (defF : inhabitedC F).

  Definition While_part : state (projT1 pM) -> F :=
    fun q =>
      match projT2 pM q with
      | Some y => y
      | None => default
      end.

  Definition While : pTM sig F n :=
    (WhileTM; While_part).

  Local Arguments loopM {_ _} _ _ _.
  Local Arguments halt {_ _} _ _.
  Local Arguments step {_ _} _ _.

  Lemma step_comp (c : mconfig sig (state (projT1 pM)) n) :
    haltConf c = false ->
    step (projT1 pM) c = step WhileTM c.
  Proof.
    intros HHalt. unfold haltConf in HHalt.
    destruct c as [q t]. cbn in *.
    cbv [step]. cbn. rewrite HHalt. reflexivity.
  Qed.

  Lemma halt_comp (c : mconfig sig (state (projT1 pM)) n) :
    haltConf (M := projT1 pM) c = false ->
    haltConf (M := WhileTM)     c = false.
  Proof.
    intros HHalt. cbn in *.
    destruct c as [q t]. cbn in *.
    apply andb_false_iff. now left.
  Qed.

  Lemma While_trans_repeat (c : mconfig sig (state WhileTM) n) :
    haltConf (M := projT1 pM) c = true ->
    projT2 pM (cstate c) = None ->
    step WhileTM c = initc (WhileTM) (ctapes c).
  Proof.
    intros HHalt HRepeat. unfold haltConf in HHalt.
    destruct c as [q t]; cbn in *.
    unfold step. cbn -[doAct_multi] in *. rewrite HHalt. unfold initc. f_equal. apply doAct_nop.
  Qed.

  Lemma While_split k (c1 c3 : mconfig sig (state (projT1 pM)) n) :
    loopM WhileTM c1 k = Some c3 ->
    exists k1 k2 c2,
      loopM (projT1 pM) c1 k1 = Some c2 /\
      loopM WhileTM c2 k2 = Some c3 /\
      k1 + k2 <= k.
  Proof.
    unfold loopM. intros HLoop.
    apply loop_split with (h := haltConf (M := projT1 pM)) in HLoop as (k1&c2&k2&HLoop&HLoop'&Hk).
    - exists k1, k2, c2. repeat split; eauto.
      apply loop_lift with (lift := id) (f' := step (projT1 pM)) (h' := haltConf (M := projT1 pM)) in HLoop.
      + apply HLoop.
      + auto.
      + apply step_comp.
    - apply halt_comp.
  Qed.

  Lemma While_split_repeat k (c1 c2 : mconfig sig (state WhileTM) n) :
    loopM WhileTM c1 k = Some c2 ->
    haltConf (M := projT1 pM) c1 = true ->
    projT2 pM (cstate c1) = None ->
    exists k' : nat,
      k = S k' /\
      loopM WhileTM (initc WhileTM (ctapes c1)) k' = Some c2.
  Proof.
    intros HLoop HHalt HRepeat. unfold haltConf in HHalt.
    destruct k as [ | k']; cbn in *.
    - rewrite HHalt, HRepeat in HLoop. cbn in HLoop. inv HLoop.
    - rewrite HHalt, HRepeat in HLoop. cbn in HLoop. exists k'. split. reflexivity.
      now rewrite While_trans_repeat in HLoop by auto.
  Qed.

  Lemma While_split_term k (c1 c2 : mconfig sig (state WhileTM) n) (f : F) :
    loopM WhileTM c1 k = Some c2 ->
    haltConf (M := projT1 pM) c1 = true ->
    projT2 pM (cstate c1) = Some f ->
    c2 = c1.
  Proof.
    intros HLoop HHalt HTerm. unfold loopM in *.
    eapply loop_eq_0. 2: apply HLoop. unfold haltConf in *. cbn in *. now rewrite HHalt, HTerm.
  Qed.

  Lemma While_merge_repeat k1 k2 (c1 c2 c3 : mconfig sig (state WhileTM) n) :
    loopM (projT1 pM) c1 k1 = Some c2 ->
    (projT2 pM) (cstate c2) = None ->
    loopM WhileTM (initc WhileTM (ctapes c2)) k2 = Some c3 ->
    loopM WhileTM c1 (k1+(1+k2)) = Some c3.
  Proof.
    intros HLoop1 HRepeat HLoop2. unfold loopM in *.
    eapply loop_lift with (lift := id) (f' := step (WhileTM)) (h' := haltConf (M := projT1 pM)) in HLoop1; cbv [id] in *; cbn; auto; cycle 1.
    { intros. symmetry. now apply step_comp. }
    apply loop_merge with (h := haltConf (M := projT1 pM)) (a2 := c2).
    - apply halt_comp.
    - apply HLoop1.
    - cbn [loop plus]. rewrite While_trans_repeat; auto. 2: apply (loop_fulfills HLoop1).
      cbn in *. setoid_rewrite (loop_fulfills HLoop1). now rewrite HRepeat.
  Qed.

  Lemma While_merge_term k1 (c1 c2 : mconfig sig (state WhileTM) n) (f : F) :
    loopM (projT1 pM) c1 k1 = Some c2 ->
    (projT2 pM) (cstate c2) = Some f ->
    loopM WhileTM c1 k1 = Some c2.
  Proof.
    intros HLoop HTerm. unfold loopM in *.
    eapply loop_lift with (lift := id) (f' := step (WhileTM)) (h' := haltConf (M := projT1 pM)) in HLoop; cbv [id] in *; cbn; auto; cycle 1.
    { intros. symmetry. now apply step_comp. }
    unfold loopM.
    replace k1 with (k1 + 0) by lia.
    apply loop_merge with (h := haltConf (M := projT1 pM)) (a2 := c2).
    - apply halt_comp.
    - apply HLoop.
    - cbn in *. setoid_rewrite (loop_fulfills HLoop). rewrite HTerm. cbn. reflexivity.
  Qed.
  


  (** ** Correctness of [While] *)

  Variable R : pRel sig (option F) n.

  Inductive While_Rel : pRel sig F n :=
  | While_Rel''_one :
      forall tin yout tout, R tin (Some yout, tout) -> While_Rel tin (yout, tout)
  | While_Rel''_loop :
      forall tin tmid yout tout,
        R tin (None, tmid) ->
        While_Rel tmid (yout, tout) ->
        While_Rel tin (yout, tout).

  Lemma While_Realise :
    pM ⊨ R -> While ⊨ While_Rel.
  Proof.
    intros HRel. hnf in HRel; hnf. intros t k; revert t. apply complete_induction with (x := k); clear k; intros k IH. intros tin c3 HLoop.
    apply While_split in HLoop as (k1&k2&c2&HLoop1&HLoop2&Hk).
    destruct (projT2 pM (cstate c2)) as [ f | ] eqn:E; cbn in *; [ clear IH | ].
    - apply While_split_term with (f := f) in HLoop2 as ->; auto. 2: apply (loop_fulfills HLoop1). unfold While_part. rewrite E.
      constructor 1. specialize HRel with (1 := HLoop1). now rewrite E in HRel.
    - apply While_split_repeat in HLoop2 as (k2'&->&HLoop2); auto. 2: apply (loop_fulfills HLoop1).
      specialize IH with (2 := HLoop2); spec_assert IH by lia.
      econstructor 2.
      + specialize HRel with (1 := HLoop1). rewrite E in HRel. eassumption.
      + apply IH.
  Qed.


  (** ** Termination of [While] *)
  Section While_TerminatesIn.
    Variable (T T' : Rel (tapes sig n) nat).

    Lemma While_TerminatesIn_ind :
      pM ⊨ R ->
      projT1 pM ↓ T' ->
      (forall (tin : tapes sig n) (k : nat),
          T tin k ->
          exists k1,
            T' tin k1 /\
            (forall ymid tmid, R tin (Some ymid, tmid) -> k1 <= k) /\
            (forall tmid, R tin (None, tmid) -> exists k2, T tmid k2 /\ 1 + k1 + k2 <= k)) ->
      WhileTM ↓T.
    Proof.
      intros Realise_M Term_M Hyp tin i. revert tin. apply complete_induction with (x:=i); clear i; intros i IH tin.
      intros (i1&HT1&HT2&HT3) % Hyp. (* todo: i *)
      pose proof (Term_M _ _ HT1) as (oconf&Hloop).
      specialize (Realise_M _ _ _ Hloop).
      destruct (projT2 pM (cstate oconf)) as [ ymid | ] eqn:E1.
      - specialize HT2 with (1 := Realise_M).
        exists oconf. eapply loop_monotone; eauto. eapply While_merge_term; eauto.
      - specialize HT3 with (1 := Realise_M) as (i2&HT3&Hi).
        specialize (IH i2 ltac:(lia) _ HT3) as (oconf2&Hloop2).
        exists oconf2. apply loop_monotone with (k1 := i1 + (1 + i2)). 2: lia.
        eapply While_merge_repeat; eauto.
    Qed.

  End While_TerminatesIn.

  (** Alternative for [While_TerminatesIn] using co-induction *)
  Section While_TerminatesIn_coind.
    Variable (T : Rel (tapes sig n) nat).

    CoInductive While_T : tRel sig n :=
    | While_T_intro tin k k1 :
        T tin k1 ->
        (forall tmid ymid,
            R tin (Some ymid, tmid) -> k1 <= k) ->
        (forall tmid,
            R tin (None, tmid) ->
            exists k2, While_T tmid k2 /\ 1 + k1 + k2 <= k) ->
        While_T tin k.

    Lemma While_TerminatesIn :
      pM ⊨ R ->
      projT1 pM ↓ T ->
      WhileTM ↓ While_T.
    Proof.
      intros HRel HTerm. eapply While_TerminatesIn_ind; eauto.
      intros tin k' HCoInd. destruct HCoInd as [ t k k1 H1 H2 H3 ]. eauto.
    Qed.

  End While_TerminatesIn_coind.

End While.

Arguments While : simpl never.
Arguments While {n sig F} pM {defF}.

(* Deprecated name *)
Notation WHILE := While (only parsing).


(** ** (Co-) Induction Principle for Correctness (Running Time) of [While] *)

Section WhileInduction.
  Variable (sig : finType) (n : nat) (F : finType).

  Variable R1 : pRel sig (option F) n.
  Variable R2 : pRel sig F n.

  Lemma WhileInduction :
    (forall tin yout tout (HLastStep: R1 tin (Some yout, tout)), R2 tin (yout, tout)) ->
    (forall tin tmid tout yout
       (HStar : R1 tin (None, tmid)) (HLastStep : R2 tmid (yout, tout)), R2 tin (yout, tout)) ->
    While_Rel R1 <<=2 R2.
  Proof. intros H1 H2. intros tin tout. induction 1; eauto. Qed.

End WhileInduction.


Section WhileCoInduction.
  Variable (sig : finType) (n : nat) (F : finType).

  Variable R : pRel sig (option F) n.
  Variable T T' : tRel sig n.

  Lemma WhileCoInduction :
    (forall (tin : tapes sig n) (k : nat) (HT : T tin k),
        exists k1,
          T' tin k1 /\
          forall (ymid : option F) tmid,
            R tin (ymid, tmid) ->
            match ymid with
            | Some _ => k1 <= k
            | None => exists k2, T tmid k2 /\ 1 + k1 + k2 <= k
            end) ->
    T <<=2 While_T R T'.
  Proof.
    intros. cofix IH. intros tin k HT. specialize H with (1 := HT) as (k1&H1&H2). econstructor; eauto.
    - intros tmid ymid HR. specialize (H2 (Some ymid) tmid); cbn in *. auto.
    - intros tmid HR. specialize (H2 None tmid) as (k2&H3&H4); eauto.
  Qed.

End WhileCoInduction.


(** Alternative definition of [While_Rel] *)
Section OtherWhileRel.

  Variable (sig : finType) (n : nat) (F : finType).

  Variable R : Rel (tapes sig n) (option F * tapes sig n).

  Definition While_Rel' : pRel sig F n :=
    (star (R |_ None)) ∘ ⋃_y (R |_(Some y)) ||_y.

  Goal While_Rel R =2 While_Rel'.
  Proof.
    unfold While_Rel'. split.
    {
      apply WhileInduction; intros; cbn in *.
      - eexists. split. constructor. exists yout. auto.
      - destruct HLastStep as (y&IH1&?&<-&IH2); cbn in *.
        eexists. split; eauto. econstructor; eauto.
    }
    {
      intros tin (yout, tout) H.  cbn in H. destruct H as (tmid&HStar&HLastStep).
      induction HStar as [ tin | tin tmid tmid2 HS1 HS2 IH].
      - destruct HLastStep as (?&<-&H). now constructor.
      - spec_assert IH by assumption.
        destruct HLastStep as (?&<-&H).
        econstructor 2.
        + apply HS1.
        + apply IH.
    }
  Qed.

End OtherWhileRel.
