From Undecidability.L Require Import L Tactics.LTactics.
From Undecidability.L.Datatypes Require Import LNat LProd Lists LOptions. 

From Undecidability.L.AbstractMachines Require Import FunctionalDefinitions AbstractHeapMachineDef Programs.

Require Import Undecidability.L.AbstractMachines.LargestVar.

From Undecidability.L Require Import Prelim.LoopSum Functions.LoopSum Functions.UnboundIteration.

Instance termT_max : computableTime' max (fun x _ => (5,fun y _ => (min x y * 15 + 8,tt))).
Proof.
  extract. fold max. solverec.
Qed.

Definition largestVarTR' '(stack,res) : (list term * nat) + nat :=
  match stack with
    [] => inr res
  | s::stack =>
    match s with
      var n => inl (stack,max n res)
    | app s t => inl (s::t::stack,res)
    | lam s => inl (s::stack,res)
    end
  end.

Fixpoint largestVarTR'_fuel (s:term) : nat :=
  match s with
    var _ => 1
  | app s t => 1 + (largestVarTR'_fuel s + largestVarTR'_fuel t)
  | lam s => 1 + largestVarTR'_fuel s
  end.


Lemma largestVarTR'_correct stack res s k:
  loopSum (largestVarTR'_fuel s + k) largestVarTR' (s::stack,res)
  = loopSum k largestVarTR' (stack,max (largestVar s) res).
Proof.
  induction s in res,stack,k |- *.
  all:cbn.
  -reflexivity.
  -rewrite <- !Nat.add_assoc. cbn.
   rewrite IHs1, IHs2. easy.
  -rewrite IHs. easy.
Qed.
                       
Lemma largestVarTR_correct s:
  loopSum (largestVarTR'_fuel s + 1) largestVarTR' ([s],0) = Some (largestVar s). 
Proof.
  rewrite largestVarTR'_correct. cbn. easy.
Qed.

Instance termT_largestVarTR' : computableTime' largestVarTR'
                                           (fun x _ => (let '(stack,res) := x in
                                                    match stack with
                                                      var n ::_ =>  n*15
                                                    | _ => 0
                                                    end + 31,tt)).
Proof.
 extract. solverec.
Qed.

Lemma largestVarTR'_fuel_leq_largestVar s : largestVarTR'_fuel s <= size s.
Proof.
  induction s;cbn [size largestVarTR'_fuel];try Lia.lia.
Qed.

Instance termT_largestVar : computableTime' largestVar (fun s _ => ((40 * size s) +46,tt)).
Proof.
  eexists.
  eapply computesTime_timeLeq.
  
  2:{ unshelve (eapply uiter_total_instanceTime with (1 := largestVarTR_correct) (preprocessT:=(fun _ _ => (5,tt)))).
      4:{ extract. solverec. }
      2:{ apply termT_largestVarTR'. }
  }
  split. 2:exact Logic.I.
  cbn [fst].
  erewrite uiterTime_bound_recRel with (iterT := fun _ '(stack,res) => ((sumn (map size stack)) * 40
                                                                   + 40))
                                       (P:= fun n x => True).
  { cbn [length map sumn]. Lia.lia. }
  {intros n [stack res] H. cbn.
   destruct stack as [|[[]| |]].
   2-5:split;[easy|].
   all:cbn [length map sumn largestVarTR'_fuel size];try Lia.lia.
  }
  all:easy.
Qed.
