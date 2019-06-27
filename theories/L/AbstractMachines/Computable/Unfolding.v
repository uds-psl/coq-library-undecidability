From Undecidability.L Require Import L Tactics.LTactics.
From Undecidability.L.Datatypes Require Import LSum LBool LNat Lists.

From Undecidability.L.AbstractMachines Require Import FunctionalDefinitions AbstractHeapMachineDef Programs UnfoldTailRec UnfoldHeap.

Require Import Undecidability.L.AbstractMachines.LargestVar.

From Undecidability.L Require Import Prelim.LoopSum Functions.LoopSum Functions.UnboundIteration Functions.LoopSum Functions.Equality.

From Undecidability.L.AbstractMachines.Computable Require Import Shared Lookup.


Run TemplateProgram (tmGenEncode "task_enc" task).
Hint Resolve task_enc_correct : Lrewrite.

Instance termT_S : computableTime' closT (fun _ _ => (1,fun _ _ => (1,tt))).
Proof.
  extract constructor.
  solverec.
Defined.

Definition time_unfoldTailRecStep : (list task * list heapEntry * list term ) -> _ :=
  fun '(stack,H,res) => match stack with
                     | closT (var n,a) k::_ => lookupTime (length H) (n-k) + min n k * 28
                     | _ => 0
                     end + 96.

Instance term_unfoldTailRecStep : computableTime' unfoldTailRecStep (fun x _ => (time_unfoldTailRecStep x,tt)).
extract. unfold time_unfoldTailRecStep. solverec.
Qed.



Definition unfoldBool_time lengthH largestVar :=
  lookupTime lengthH largestVar * 7 + largestVar *196+ 1245.

Instance term_unfoldBool : computableTime' unfoldBoolean
                                          (fun H _ => (1,fun q _ => (unfoldBool_time (length H) (max (largestVarH H) (largestVarC q)),tt))).
Proof.
  unfold unfoldBoolean.
  unfold enc. cbn [registered_bool_enc bool_enc].
  extract.
  clear used_term.
  recRel_prettify.
  intros H _. split. reflexivity.
  intros [s a] _. split. 2:now solverec.
  unshelve eassert (H':= time_loopSum_bound_onlyByN _ _
      (f:=unfoldTailRecStep)
      (fT:=(fun (x0 : list task * list heapEntry * list term) (_ : unit) => (time_unfoldTailRecStep x0, tt)))
      (P:= fun n '(stack,H',res) =>
             H' = H
             /\ largestVarState (stack,H',res) <= max (largestVarH H) (largestVar s)
             /\ (length res <= n))
      (boundL := 96 + lookupTime (length H) (max (largestVarH H) (largestVar s)) + max (largestVarH H) (largestVar s) * 28)
      (boundR := fun n => 28*n) _).

  -intros n x. assert (H':=unfoldTailRecStep_largestVar_inv x).
   unfold unfoldTailRecStep in *.
   repeat (let eq := fresh "eq" in destruct _ eqn:eq);inv eq1;try congruence.
   all:unfold time_unfoldTailRecStep.
   
   all:intros (->&H'1&?).
   all:try rewrite H',H'1.
   all:cbn [fst].
   all:intuition (try eassumption;cbn [length];try Lia.lia;try eauto).
   

   all:repeat match goal with
                H : _ <=? _ = true |- _ => apply Nat.leb_le in H
              | H : _ <=? _ = false |- _ => apply Nat.leb_gt in H
              | H : lookup _ _ _ = Some _ |- _ => apply lookup_size in H;cbn in H
              end.
   3:now cbn in *;Lia.nia.
   1-3:assert (H'3 : n1 <= (Init.Nat.max (largestVarH H) (largestVar s))) by (cbn in *; Lia.nia).
   1-3:rewrite lookupTime_mono with (n' := Init.Nat.max (largestVarH H) (largestVar s));[|reflexivity|try omega].
   1-3:cbn - [plus mult]in *.
   1-3:Lia.lia.
  -rewrite H'. clear H'.
   2:{ cbn. intuition idtac. all:Lia.lia. } 
   ring_simplify.
   (*
   specialize @list_eqbTime_bound_r with (f:=fun x => 17 * sizeT x + 11) as H'1.
*)
   destruct loopSum as [[]|].
   cbn [size].
   repeat destruct _.
   all:unfold unfoldBool_time, largestVarC.
   all:Lia.lia.
Qed.


Lemma unfoldBool_time_mono l l' n n':
  l <= l' -> n <= n' -> unfoldBool_time l n <= unfoldBool_time l' n'.
Proof.
  unfold unfoldBool_time. intros H1 H2.
  rewrite lookupTime_mono. 2,3:eassumption. rewrite H2. reflexivity.
Qed.

Lemma unfoldBool_time_leq lengthH largestVar :
  unfoldBool_time lengthH largestVar <= (largestVar + 1) * (lengthH * 15 + 38 + 28) * 7 + 1245.
Proof.
  unfold unfoldBool_time. unfold lookupTime.
  Lia.nia.
Qed.

