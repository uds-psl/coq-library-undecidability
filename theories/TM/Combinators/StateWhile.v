Require Export TM.TM.
Require Import PslBase.FiniteTypes.DepPairs EqdepFacts.

Section StateWhile.

  Variable n : nat.
  Variable sig : finType.

  Variable F1 F2 : finType.
  Variable pM : F1 -> pTM sig (F1 + F2) n.

  Definition StateWhile_states : Type := { l : F1 & states (projT1 (pM l)) }.

  Definition liftState {l : F1} (q : states (projT1 (pM l))) : StateWhile_states := ltac:(eexists; apply q). (* existT _ l q *)

  Definition lift {l : F1} (c : mconfig sig (states (projT1 (pM l))) n) : mconfig sig (FinType(EqType StateWhile_states)) n :=
    {|
      cstate := liftState (cstate c);
      ctapes := ctapes c;
    |}.
  

  Definition StateWhile_trans : StateWhile_states * Vector.t (option sig) n -> StateWhile_states * Vector.t (option sig * move) n :=
    fun '(q, s) =>
      if halt (projT2 q)
      then match projT2 (pM (projT1 q)) (projT2 q) with
           | inl l1 => (liftState (start (projT1 (pM l1))), nop_action)
           | inr _ => (q, nop_action) (* terminating state, transition is irrelevant *)
           end
      else let (q', a) := trans (projT2 q, s) in (liftState q', a).


  Definition StateWhile_halt : StateWhile_states -> bool :=
    fun q => halt (projT2 q) &&
               match projT2 (pM (projT1 q)) (projT2 q) with
               | inl _ => false
               | inr l2 => true
               end.

  Definition StateWhileTM (l1 : F1) : mTM sig n :=
    {|
      start := liftState (start (projT1 (pM l1)));
      trans := StateWhile_trans;
      halt := StateWhile_halt;
    |}.

  
  Hypothesis (defF : inhabitedC F2).
  Definition StateWhile_part : StateWhile_states -> F2 :=
    fun q => match projT2 (pM (projT1 q)) (projT2 q) with
          | inl _ => default
          | inr l2 => l2
          end.

  Definition StateWhile (l1 : F1) : pTM sig F2 n :=
    (StateWhileTM l1; StateWhile_part).

  Local Arguments loopM {_ _} _ _ _.
  Local Arguments halt {_ _} _ _.
  Local Arguments step {_ _} _ _.

  
  Lemma step_comp (l : F1) (c : mconfig sig (states (projT1 (pM l))) n) :
    haltConf c = false ->
    step (StateWhileTM l) (lift c) = lift (step (projT1 (pM l)) c).
  Proof.
    intros HHalt. unfold haltConf in HHalt. unfold lift.
    destruct c as [q t]. cbn in *.
    cbv [step]. cbn. rewrite HHalt.
    destruct (trans (q, current_chars t)) as [q' a]. cbn. reflexivity.
  Qed.
  

  Lemma halt_comp (l : F1) (c : mconfig sig (states (projT1 (pM l))) n) :
    haltConf (M := projT1 (pM l)) c = false ->
    haltConf (M := StateWhileTM l) (lift c) = false.
  Proof.
    intros HHalt. cbn in *.
    destruct c as [q t]. cbn in *.
    apply andb_false_iff. cbn. now left.
  Qed.

  Lemma halt_comp' (l : F1) (c : mconfig sig (states (projT1 (pM l))) n) :
    haltConf (M := StateWhileTM l) (lift c) = haltConf (M := projT1 (pM l)) c.
  Proof.
    cbn in *. destruct c as [q t]. cbn in *. unfold StateWhile_halt, haltConf. cbn.
  Abort.

  Lemma StateWhile_trans_repeat (l l_ : F1) (c : mconfig sig (states (projT1 (pM l))) n) (l' : F1) :
    haltConf (M := projT1 (pM l)) c = true ->
    projT2 (pM l) (cstate c) = inl l' ->
    step (StateWhileTM l_) (lift c) = lift (initc (projT1 (pM l')) (ctapes c)).
  Proof.
    intros HHalt HRepeat. unfold haltConf in HHalt.
    destruct c as [q t]; cbn in *.
    unfold step. cbn -[doAct_multi] in *. rewrite HHalt, HRepeat. unfold initc, lift. cbn. f_equal. apply doAct_nop.
  Qed.



  (** The definition of [mTM] already contains the start state. The parameter of [StateWhile] somehow corresponds to the start state, but it is irrelevant when we choose a concrete starting state for [loopM]. *)
  Lemma startState_irrelevant k l l' c1 c2 :
    loopM (StateWhileTM l ) c1 k = Some c2 ->
    loopM (StateWhileTM l') c1 k = Some c2.
  Proof. auto. Qed.

  Lemma startState_irrelevant' k l l' c1 :
    loopM (StateWhileTM l) c1 k = loopM (StateWhileTM l') c1 k.
  Proof. reflexivity. Qed.

  
  Definition lifth l : mconfig sig (states (StateWhileTM l)) n -> bool.
  Proof.
    intros ((l'&q)&t).
    decide (l=l') as [_ | ].
    - eapply (halt _ q).
    - apply true.
  Defined.

  
  Lemma lifth_comp l (c : mconfig sig (states (StateWhileTM l)) n) :
    lifth c = false -> haltConf c = false.
  Proof. destruct c as ((l'&q)&t). cbn. decide (l=l') as [->| _]; intros H; auto. unfold StateWhile_halt. cbn. now rewrite H. Qed.

  
  Lemma lifth_comp' l (c : mconfig sig (states (projT1 (pM l))) n) :
    @lifth l (lift c) = haltConf c.
  Proof. unfold haltConf. destruct c as (q,t). cbn. decide (l=l); tauto. Qed.

  
  Lemma StateWhile_split_repeat k l l1 c2 c3 :
    loop (step (StateWhileTM l)) (haltConf (M:=StateWhileTM l)) (lift c2) k = Some c3 ->
    haltConf c2 = true ->
    projT2 (pM l) (cstate c2) = inl l1 ->
    exists k',
      loop (step (StateWhileTM l)) (haltConf (M:=StateWhileTM l)) (lift (initc (projT1 (pM l1)) (ctapes c2))) k' = Some c3 /\
      k = S k'.
  Proof.
    intros HLoop H E. unfold haltConf in H.
    destruct k as [ |k']; cbn in *; unfold StateWhile_halt in *; cbn in *.
    - rewrite H, E in HLoop. cbn in *. congruence.
    - rewrite H, E in HLoop. cbn in *. exists k'. repeat split; auto.
      rewrite <- HLoop. f_equal. symmetry. apply StateWhile_trans_repeat; auto.
  Qed.

  Lemma StateWhile_split_break k l l2 c2 c3 :
    loop (step (StateWhileTM l)) (haltConf (M:=StateWhileTM l)) (lift c2) k = Some c3 ->
    haltConf c2 = true ->
    projT2 (pM l) (cstate c2) = inr l2 ->
    c3 = lift c2.
  Proof. intros HLoop H E. eapply loop_eq_0 in HLoop; auto. unfold haltConf in *. cbn in *. unfold StateWhile_halt in *. cbn in *. now rewrite H, E. Qed.

  Lemma StateWhile_split k l (c1 : mconfig sig (states (projT1 (pM l))) n) (c3 : mconfig sig (FinType (EqType StateWhile_states)) n) :
    loopM (StateWhileTM l) (lift c1) k = Some c3 ->
    exists (c2 : mconfig sig (states (projT1 (pM l))) n),
      match projT2 (pM l) (cstate c2) with
      | inl l1 =>
        exists (k1 k2 : nat),
        loopM (projT1 (pM l)) c1 k1 = Some c2 /\
        loopM (StateWhileTM l) (lift (initc (projT1 (pM l1)) (ctapes c2))) k2 = Some c3 /\
        1 + k1 + k2 <= k
      | inr l2 => loopM (projT1 (pM l)) c1 k = Some c2 /\ c3 = lift c2
      end.
  Proof.
    intros HLoop. unfold loopM in *.
    apply loop_split with (h := @lifth l) in HLoop as (k1&c2&k2&HLoop1&HLoop2&Hk).
    - apply loop_unlift with (f := step (projT1 (pM l))) (h := haltConf (M := projT1 (pM l))) in HLoop1 as (c2'&HLoop1&->).
      + exists c2'. destruct (projT2 (pM l) (cstate c2')) as [l1|l2] eqn:E.
        * exists k1. eapply StateWhile_split_repeat in HLoop2 as (k2'&HLoop2&->). exists k2'. repeat split. all: eauto.
          -- omega.
          -- now apply loop_fulfills in HLoop1.
        * split. eapply loop_monotone. apply HLoop1. omega. eapply StateWhile_split_break; eauto. now apply loop_fulfills in HLoop1.
      + apply lifth_comp'.
      + apply step_comp.
    - apply lifth_comp.
  Qed.


  Lemma StateWhile_merge_repeat k1 k2 l l1 (c1 : mconfig sig (states (projT1 (pM l))) n) (c2 : mconfig sig (states (projT1 (pM l))) n) c3 :
    loopM (projT1 (pM l)) c1 k1 = Some c2 ->
    haltConf c2 = true ->
    projT2 (pM l) (cstate c2) = inl l1 ->
    loopM (StateWhileTM l) (lift (initc (projT1 (pM l1)) (ctapes c2))) k2 = Some c3 ->
    loopM (StateWhileTM l) (lift c1) (k1 + (1 + k2)) = Some c3.
  Proof.
    intros HLoop1 HHalt HL HLoop2. unfold loopM in *.
    apply loop_merge with (f := step (StateWhileTM l)) (h := @lifth l) (a2 := lift c2).
    - apply lifth_comp.
    - eapply loop_lift. 3: apply HLoop1. 2: eauto.
      + apply lifth_comp'.
      + apply step_comp.
    - cbn [plus].
      rewrite loop_step.
      + now rewrite StateWhile_trans_repeat with (l' := l1).
      + cbn; unfold StateWhile_halt; cbn. rewrite HL. apply andb_false_r.
  Qed.

  
  Lemma StateWhile_merge_break k l l2 (c1 : mconfig sig (states (projT1 (pM l))) n) (c2 : mconfig sig (states (projT1 (pM l))) n) :
    loopM (projT1 (pM l)) c1 k = Some c2 ->
    haltConf c2 = true ->
    projT2 (pM l) (cstate c2) = inr l2 ->
    loopM (StateWhileTM l) (lift c1) k = Some (lift c2).
  Proof.
    intros HLoop HHalt HL. unfold loopM in *.
    replace k with (k + 0) by omega.
    apply loop_merge with (f := step (StateWhileTM l)) (h := @lifth l) (a2 := lift c2).
    - apply lifth_comp.
    - eapply loop_lift with (lift := lift) (f' := step (StateWhileTM l)) (h' := @lifth l) in HLoop; auto.
      + apply lifth_comp'.
      + apply step_comp.
    - cbn. unfold StateWhile_halt; cbn. unfold haltConf in *. rewrite HHalt, HL. cbn. reflexivity.
  Qed.


  (** ** Correctness of [StateWhile] *)

  Variable R : F1 -> pRel sig (F1 + F2) n.

  Inductive StateWhile_Rel : F1 -> pRel sig F2 n :=
  | StateWhile_Rel_loop :
      forall l t l1 t' l' t'',
        R l t (inl l1, t') ->
        StateWhile_Rel l1 t' (l', t'') ->
        StateWhile_Rel l t (l', t'')
  | StateWhile_Rel_break :
      forall l t l2 t',
        R l t (inr l2, t') ->
        StateWhile_Rel l t (l2, t').


  Lemma lift_init l tin :
    initc (StateWhileTM l) tin = lift (initc (projT1 (pM l)) tin).
  Proof. reflexivity. Qed.
  
  Lemma StateWhile_Realise l :
    (forall l, pM l ⊨ R l) ->
    StateWhile l ⊨ StateWhile_Rel l.
  Proof.
    intros HRel. hnf in HRel; hnf. intros t k; revert t l. apply complete_induction with (x := k); clear k; intros k IH. intros tin l c3 HLoop.
    unfold loopM in HLoop. cbn in *. rewrite lift_init in HLoop. apply StateWhile_split in HLoop as (c2&HLoop).
    destruct (projT2 (pM l) (cstate c2)) as [l1|l2] eqn:E.
    - destruct HLoop as (k1&k2&HLoop1&HLoop2&Hk).
      apply HRel in HLoop1. rewrite E in HLoop1. rewrite <- lift_init in HLoop2.
      eapply startState_irrelevant in HLoop2. specialize IH with (2 := HLoop2). spec_assert IH by omega.
      econstructor 1; eauto.
    - destruct HLoop as (HLoop&->).
      apply HRel in HLoop. rewrite E in *.
      constructor 2; auto. cbn. unfold StateWhile_part. cbn. now rewrite E.
  Qed.

  
  (** ** Termination of [StateWhile] *)
  Section StateWhile_TerminatesIn.
    Variable (T T' : F1 -> tRel sig n).

    Lemma StateWhile_TerminatesIn_ind l :
      (forall l, pM l ⊨ R l) ->
      (forall l, projT1 (pM l) ↓ T' l) ->
      (forall l (tin : tapes sig n) (k : nat),
          T l tin k ->
          exists k1,
            T' l tin k1 /\
            (forall tmid l2, R l tin (inr l2, tmid) -> k1 <= k) /\
            (forall tmid l1, R l tin (inl l1, tmid) -> exists k2, T l1 tmid k2 /\ 1 + k1 + k2 <= k)) ->
      StateWhileTM l ↓ T l.
    Proof.
      intros Realise_M Term_M Hyp tin k. revert tin l. apply complete_induction with (x:=k); clear k; intros k IH tin l.
      intros (k1&HT1&HT2&HT3) % Hyp.
      pose proof (Term_M _ _ _ HT1) as (oconf&Hloop).
      specialize (Realise_M _ _ _ _ Hloop).
      destruct (projT2 (pM l) (cstate oconf)) as [ l1 | l2 ] eqn:E1.
      - specialize HT3 with (1 := Realise_M) as (k2&HT3&Hi).
        specialize (IH k2 ltac:(omega) _ _ HT3) as (oconf2&Hloop2).
        exists oconf2. apply loop_monotone with (k1 := k1 + (1 + k2)). 2: omega.
        cbn -[plus]. rewrite lift_init.
        refine (StateWhile_merge_repeat Hloop _ _ Hloop2); auto.
        unfold loopM in *; now apply loop_fulfills in Hloop.
      - specialize HT2 with (1 := Realise_M).
        exists (lift oconf). eapply loop_monotone; eauto.
        refine (StateWhile_merge_break (l2 := l2) Hloop _ _); auto.
        unfold loopM in *; now apply loop_fulfills in Hloop.
    Qed.

  End StateWhile_TerminatesIn.

  (** Alternative for [StateWhile_TerminatesIn] using co-induction *)
  Section StateWhile_TerminatesIn_coind.
    Variable (T : F1 -> tRel sig n).

    CoInductive StateWhile_T : F1 -> tRel sig n :=
    | StateWhile_T_intro l t k k1 :
        T l t k1 ->
        (forall t' l1,
            R l t (inl l1, t') ->
            exists k2, StateWhile_T l1 t' k2 /\ 1 + k1 + k2 <= k) ->
        (forall tmid l2,
            R l t (inr l2, tmid) -> k1 <= k) ->
        StateWhile_T l t k.

    Lemma StateWhile_TerminatesIn l :
      (forall l, pM l ⊨ R l) ->
      (forall l, projT1 (pM l) ↓ T l) ->
      StateWhileTM l ↓ StateWhile_T l.
    Proof.
      intros HRel HTerm. eapply StateWhile_TerminatesIn_ind; eauto.
      intros l' tin k' HCoInd. destruct HCoInd; eauto.
    Qed.

  End StateWhile_TerminatesIn_coind.



  (** It's easy to show that the start-labels are irrevant if we fix the internal state. The transition functions are definitionally equal. *)
  Lemma StartState_irrelevant (y y' : F1) (k : nat) (iconf : mconfig sig (FinType(EqType StateWhile_states)) n) :
    loopM (projT1 (StateWhile y')) iconf k = loopM (projT1 (StateWhile y )) iconf k.
  Proof. auto. Qed.


End StateWhile.

Arguments StateWhile : simpl never.
Arguments StateWhile {n sig F1 F2} pM {defF} l1.


(** ** (Co-) Induction Principle for Correctness (Running Time) of [StateWhile] *)

Section StateWhileInduction.
  Variable (sig : finType) (n : nat) (F1 F2 : finType).

  Variable R1 : F1 -> pRel sig (F1+F2) n.
  Variable R2 : F1 -> pRel sig F2 n.


  Lemma StateWhileInduction :
    (forall tin l yout tout (HLastStep: R1 l tin (inr yout, tout)), R2 l tin (yout, tout)) ->
    (forall tin l l' tmid tout yout
       (HStar : R1 l tin (inl l', tmid)) (HLastStep : R2 l' tmid (yout, tout)), R2 l tin (yout, tout)) ->
    (forall l, StateWhile_Rel R1 l <<=2 (R2 l)).
  Proof. intros H1 H2. intros tin tout. induction 1; eauto. Qed.

End StateWhileInduction.



Section WhileCoInduction.
  Variable (sig : finType) (n : nat) (F1 F2 : finType).

  Variable R : F1 -> pRel sig (F1 + F2) n.
  Variable T T' : F1 -> tRel sig n.

  Lemma StateWhileCoInduction :
    (forall l (tin : tapes sig n) (k : nat) (HT : T l tin k),
        exists k1,
          T' l tin k1 /\
          forall (ymid : F1 + F2) tmid,
            R l tin (ymid, tmid) ->
            match ymid with
            | inl l1 => exists k2, T l1 tmid k2 /\ 1 + k1 + k2 <= k
            | inr _ => k1 <= k
            end) ->
    (forall l, T l <<=2 StateWhile_T R T' l).
  Proof.
    intros. revert l. cofix IH. intros l tin k HT. specialize H with (1 := HT) as (k1&H1&H2). econstructor; eauto.
    - intros tmid ymid HR. specialize (H2 (inl ymid) tmid HR) as (k2&H2&Hk); cbn in *.
      exists k2. split. 2: omega. now apply IH.
    - intros tmid l2 HR. now specialize (H2 (inr l2) tmid HR).
  Qed.

End WhileCoInduction.
