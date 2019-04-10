Require Import ProgrammingTools.


Section CompilerOutline.

  Variable (sig F : finType).
  Variable n : nat.

  Hypothesis sigSim : finType.
  Hypothesis cTapes : codable sigSim (tapes sig n).


  Hypothesis pM : pTM sig F n.

  Hypothesis (defF : inhabitedC F).
  
  Hypothesis Step : states (projT1 pM) -> pTM (sigSim^+) (states (projT1 pM) + F) 1.

  Definition Step_Rel (q : states (projT1 pM)) : pRel (sigSim^+) (states (projT1 pM) + F) 1 :=
    fun tin '(yout, tout) =>
      forall (T : tapes sig n),
        tin[@Fin0] ≃ T ->
        let c := {| cstate := q; ctapes := T |} in
        if haltConf c
        then tout[@Fin0] ≃ T /\ yout = inr (projT2 pM q)
        else let (q', T') := step c in
             tout[@Fin0] ≃ T' /\ yout = inl q'.
  
  Hypothesis Step_Realise : forall q, Step q ⊨ Step_Rel q.


  Definition Loop q := StateWhile Step q.

  Definition Loop_Rel q : pRel (sigSim^+) F 1 :=
    fun tin '(yout, tout) =>
      forall (T : tapes sig n),
        tin[@Fin0] ≃ T ->
        let c := {| cstate := q; ctapes := T |} in
        exists c' k, loopM c k = Some c' /\
                tout[@Fin0] ≃ ctapes c' /\ yout = projT2 pM (cstate c').


  Lemma Loop_Realise q : Loop q ⊨ Loop_Rel q.
  Proof.
    eapply Realise_monotone.
    { unfold Loop. eapply StateWhile_Realise. apply Step_Realise. }
    {
      apply StateWhileInduction; intros; intros T HEncT; TMSimp.
      - modpon HLastStep. unfold haltConf in *; cbn in *. destruct (halt l) eqn:E.
        + destruct HLastStep as [HLastStep HLastStep']; inv HLastStep'.
          eexists; exists 0. cbn. unfold haltConf; cbn. rewrite E. repeat split; eauto.
        + destruct (step _). destruct HLastStep as [_ ?]; congruence.
      - modpon HStar. unfold haltConf in *; cbn in *. destruct (halt l) eqn:E.
        + destruct HStar as [HStar HStar']; inv HStar'.
        + destruct (step _) as [q' T'] eqn:E'. destruct HStar as [HStar HStar']; inv HStar'.
          modpon HLastStep. destruct HLastStep as (c'&k&HLastStep&HLastStep'&->).
          eexists. exists (S k). cbn. unfold haltConf in *; cbn in *. rewrite E, E'. repeat split; eauto.
    }
  Qed.

  Definition ToSingleTape := Loop (start (projT1 pM)).

  Definition ToSingleTape_Rel := Loop_Rel (start (projT1 pM)).

  Lemma ToSingleTape_Realise : ToSingleTape ⊨ ToSingleTape_Rel.
  Proof. exact (@Loop_Realise (start (projT1 pM))). Qed.
  

Section CompilerOutline.

