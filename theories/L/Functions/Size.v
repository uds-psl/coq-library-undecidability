From Undecidability.L Require Import Tactics.LTactics Functions.Encoding Prelim.LoopSum Functions.LoopSum Functions.UnboundIteration.
Require Import Nat.
From Undecidability.L.Datatypes Require Import Lists.

(** ** Extracted size of terms *)

Instance term_size' : computable size'.
Proof.
  extract.
Abort. (*possible, but the run time of this implementation is not good enough. *)

Lemma size'_surj : surjective size'.
Proof.
  intros n. induction n.
  -exists (var 0). cbn. lia.
  -destruct IHn as [x <-].
   exists (lam x). cbn. easy. 
Qed.

Import Util.L_facts.
Definition sizeTR' '(stack,res) : (list term * nat) + nat :=
  match stack with
    [] => inr res
  | s::stack =>
    match s with
      var n => inl (stack,S (n + res))
    | app s t => inl (s::t::stack,S res)
    | lam s => inl (s::stack,S res)
    end
  end.

Fixpoint sizeTR'_fuel (s:term) : nat :=
  match s with
    var _ => 1
  | app s t => 1 + (sizeTR'_fuel s + sizeTR'_fuel t)
  | lam s => 1 + sizeTR'_fuel s
  end.


Lemma sizeTR'_correct stack res s k:
  loopSum (sizeTR'_fuel s + k) sizeTR' (s::stack,res)
  = loopSum k sizeTR' (stack,size s + res).
Proof.
  induction s in res,stack,k |- *.
  all:cbn.
  -reflexivity.
  -rewrite <- !Nat.add_assoc. cbn.
   rewrite IHs1, IHs2. easy.
  -rewrite IHs. easy.
Qed.
                       
Lemma sizeTR_correct s:
  loopSum (sizeTR'_fuel s + 1) sizeTR' ([s],0) = Some (size s). 
Proof.
  rewrite sizeTR'_correct. cbn. easy.
Qed.

Instance termT_sizeTR' : computableTime' sizeTR'
                                           (fun x _ => (let '(stack,res) := x in
                                                    match stack with
                                                      var n ::_ =>  n*11
                                                    | _ => 0
                                                    end + 28,tt)).
Proof.
 extract. solverec.
Qed.

Lemma sizeTR'_fuel_leq_size s : sizeTR'_fuel s <= size s.
Proof.
  induction s;cbn [size sizeTR'_fuel];try Lia.lia.
Qed.

Instance termT_size : computableTime' size (fun s _ => (108 * size s + 43,tt)).
Proof.
  eexists.
  eapply computesTime_timeLeq.
  
  2:{ unshelve (eapply uiter_total_instanceTime with (1 := sizeTR_correct) (preprocessT:=(fun _ _ => (5,tt)))).
      4:{ extract. solverec. }
      2:{ apply termT_sizeTR'. }
  }
  split. 2:exact Logic.I.
  cbn [fst].
  erewrite uiterTime_bound_recRel with (iterT := fun _ '(stack,res) => ((sumn (map size stack)) * 108
                                                                   + 28 + 9))
                                       (P:= fun n x => True).
  { cbn [length map sumn]. Lia.lia. }
  {intros n [stack res] H. cbn.
   destruct stack as [|[[]| |]].
   2-5:split;[easy|].
   all:cbn [length map sumn sizeTR'_fuel size];try Lia.lia.
  }
  all:easy.
Qed.
