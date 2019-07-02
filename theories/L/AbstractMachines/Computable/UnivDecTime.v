From Undecidability.L.Datatypes Require Import LNat LBool.
From Undecidability.L Require Import Tactics.LTactics AbstractMachines.Computable.Unfolding Prelim.LoopSum Functions.UnboundIteration AbstractMachines.LargestVar.
From Undecidability.L.AbstractMachines Require Import AbstractHeapMachine FunctionalDefinitions Programs UnfoldHeap UnfoldTailRec. 
From Undecidability.L.AbstractMachines.Computable Require Import Shared HeapMachine Unfolding.

Definition univStep '(T,V,H) : _ + bool :=
  match heapStep (T,V,H) with
    Some s' => inl s'
  | None =>
    match T,V with
      [],[g] => match unfoldBoolean H g with
                 Some b => inr b
               | None => inr false (* don't care *)
               end
    | _,_ => inr false (* don't care *) 
    end
  end.

Instance termT_univStep : computableTime' univStep (fun x _ => 
                                                     (let '(T,V,H):=x in
                                                      heapStep_time T H +
                                                      match heapStep x with
                                                        Some _ => 0
                                                      | _ => match T,V with
                                                              [],[q] => unfoldBool_time (length H) (Init.Nat.max (largestVarH H) (largestVarC q))
                                                            | _,_ => 0 end
                                                      end + 33,tt)).
Proof.
  extract. solverec.
Qed.

Definition univDecTime :term := Eval cbn in λ s , uiter univStep (!!(extT init) s).

Definition univDecTime_time maxVar size n0 :=
  108 * size + (n0+2) * (heapStep_timeBound maxVar (n0+1) + 42) + unfoldBool_time (n0+1) maxVar +87.

Lemma step_UC : uniform_confluent step.
Proof.
  intros ? ? ? R1 R2;inv R1;inv R2. all:left;congruence.
Qed.

Lemma evalIn_mono s t n n' :
  s ⇓(<=n) t -> n <= n' -> s ⇓(<=n') t.
Proof.
  intros ? <-. easy.
Qed.

Lemma univDecTime_complete (s:term) (b:bool) k:
  closed s ->
  s ⇓(k) (enc b) ->
  univDecTime (enc s) ⇓(<= univDecTime_time (largestVar s) (size s) (k*4+1)) enc b.
Proof.
  intros cs R. apply ResourceMeasures.timeBS_evalIn in R.
  apply correctTime in R as (g&H&rep&R). 2:easy.
  unfold univDecTime, univDecTime_time.
  Lsimpl.
  eapply loopSum_sound_rel with (n:=1) (f:=univStep)in R as R'.
  2:{ intros ? ? R'. unfold univStep. cbn. repeat (let eq := fresh in destruct _ eqn:eq);inv R';try congruence. }
  cbn [loopSum univStep heapStep] in R'.
  erewrite unfoldBoolean_complete in R'. 2:eassumption.
  unshelve eapply uiter_sound in R'. 4:now exact _.
  cbn -[plus mult] in R'.
  remember (4*k+2) as n0.
  erewrite uiterTime_bound_recRel with
      (iterT := fun n _ => n* (heapStep_timeBound (largestVar s) n0 + 9 + 33) + unfoldBool_time n0 (largestVar s))
      (P:= fun i x => i <= n0 /\  pow AbstractHeapMachineDef.step i (init s) x)
      (2:=le_n _)
    in R'.
  2:{
    intros n ((T&V)&Hp) [H1 H2].
    specialize uniform_confluence_parameterized_terminal with (3:=R) (4:=H2) as (n'&R2&?).
    1:exact step_UC.
    1:now (intros ? H';inv H').
    unfold univStep. cbn [fst snd].
    specialize (subterm_property H2) as (st1&st2&st3).
    assert (largestVarH Hp <= largestVar s).
    { eapply largestVarH_bound. intros [] ? H'. cbn. eauto using subterm_lam_inv, subterm_largestVar. }
    destruct n'.
    -inversion R2. subst T V H. cbn [heapStep].
     erewrite unfoldBoolean_complete. 2:eassumption.
     rewrite heapStep_timeBound_le. 2:now eauto.
     rewrite heapStep_timeBound_mono with (k':=n0). 2:eassumption.
     rewrite unfoldBool_time_mono with (l':= n0) (n':=largestVar s).
     *now Lia.nia.
     *rewrite <- H1. eapply length_H. eauto.
     *eapply Nat.max_case. easy.
      destruct g. cbn. eauto using subterm_lam_inv, subterm_largestVar.
    -change (S n') with (1+n') in R2. replace (S n) with (n+1) by omega.
     eapply pow_add with (R:=step) in R2 as (?&R2&R2').
     eapply rcomp_1 with (R:=step) in R2. revert Heqn0. inv R2. all:intro.
     all: cbn [heapStep].
     +rewrite H0. intuition idtac.
      *Lia.lia.
      *eapply pow_add with (R:=step).
       eexists;split. eassumption. apply (rcomp_1 step). now constructor.
      *rewrite heapStep_timeBound_le. 2:now eauto.
       rewrite heapStep_timeBound_mono with (k:=n). 2:eassumption.
       Lia.nia.
     +rewrite H9. intuition idtac.
      *Lia.lia.
      *eapply pow_add with (R:=step).
       eexists;split. eassumption. apply (rcomp_1 step). now constructor.
      *rewrite heapStep_timeBound_le. 2:now eauto.
       rewrite heapStep_timeBound_mono with (k:=n). 2:eassumption.
       Lia.nia.
     +rewrite H9. intuition idtac.
      *Lia.lia.
      *eapply pow_add with (R:=step).
       eexists;split. eassumption. apply (rcomp_1 step). now constructor.
      *rewrite heapStep_timeBound_le. 2:now eauto.
       rewrite heapStep_timeBound_mono with (k:=n). 2:eassumption.
       Lia.nia.
     +intuition idtac.
      *Lia.lia.
      *eapply pow_add with (R:=step).
       eexists;split. eassumption. apply (rcomp_1 step). now constructor.
      *rewrite heapStep_timeBound_le. 2:now eauto.
       rewrite heapStep_timeBound_mono with (k:=n). 2:eassumption.
       Lia.nia.
  }
  {
    subst n0.
    eapply evalIn_mono. 1:Lsimpl. exact R'. cbn [fst snd].
    replace (k*4) with (4*k) by Lia.lia. replace (4*k +1+1) with (4*k+2) by Lia.lia. ring_simplify.
    Lia.nia.
  }
  rewrite !Nat.sub_diag. easy.
Qed.

