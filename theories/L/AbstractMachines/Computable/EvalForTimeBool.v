From Undecidability.L Require Import L Tactics.LTactics AbstractMachines.LargestVar.

From Undecidability.L Require Import AbstractHeapMachineDef UnfoldTailRec AbstractHeapMachine.
From Undecidability.L.AbstractMachines.Computable Require Import Unfolding HeapMachine Shared EvalForTime.

From Undecidability.L.Datatypes Require Import Lists LBinNums.
From Undecidability.L.Functions Require Import BinNums BinNumsCompare UnboundIteration.

Definition evalForTimeBool (checkFor:bool) (fuel : N) (s:term) := match evalForTime fuel s with
                                                   Some (g,H) => match unfoldBoolean H g with
                                                                  None => false
                                                                | Some b => if checkFor then b else negb b
                                                                end
                                                 | None => false
                                                 end.

Definition t__evalForTimeBool (largestVar size:nat) fuel := t__evalForTime largestVar size fuel+ unfoldBool_time (4*fuel+1) largestVar + 22.

Lemma evalForTimeBool_spec (checkFor :bool) (s:term) (fuel : N):
  reflect (closed s /\ s ⇓(<= N.to_nat fuel) (enc checkFor)) (evalForTimeBool checkFor fuel s).
Proof.
  unfold evalForTimeBool.
  eassert (H':=evalForTime_spec _ _).
  destruct evalForTime as [[]|] eqn:eq;rewrite eq.
  2:{ econstructor. easy. }
  destruct H' as (?&_&H').
  destruct unfoldBoolean eqn:eq'.
  -eapply iff_reflect.  destruct H' as (?&eq''&?).
   eapply unfoldBoolean_sound in eq'.
   replace x with (enc b) in *.
   2:{ eapply reprC_functional. all:easy. }
   (destruct b,checkFor;cbn).
   all:intuition. all:eapply inj_enc,eval_unique. all:eapply evalLe_eval_subrelation;easy.
  -econstructor. intros (_&H'').
   destruct H' as (?&H'&?).
   replace x with (enc checkFor) in *.
   2:{  all:eapply eval_unique. all:eapply evalLe_eval_subrelation;easy. }
   eapply unfoldBoolean_complete in H'. easy.
Qed.

Instance evalForTimeBool__comp : computableTime' evalForTimeBool (fun _ _ => (1,fun fuel _ => (1,fun s _ => (t__evalForTimeBool (largestVar s) (size s) (N.to_nat fuel),tt)))).
Proof.
  unfold evalForTimeBool. extract. solverec.
  all:unfold t__evalForTimeBool. 4:lia.
  all:eassert (H':=evalForTime_spec _ _).
  all:rewrite H in H'.
  all:destruct H' as (?&(?&?&R)&?).
  all:rewrite unfoldBool_time_mono with (l':=(4 * N.to_nat x0 + 1)) (n':=(largestVar x1));[try lia | |].
  all:try (etransitivity;[eapply AbstractHeapMachine.length_H;eassumption|lia]).
  all:rewrite largestVarH_leq with (1:=R).
  all:rewrite largestVarC_V_leq with (1:=R);[|easy].
  all:now rewrite Nat.max_id.
Qed.
