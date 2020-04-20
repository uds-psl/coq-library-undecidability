From Undecidability.L Require Import L Tactics.LTactics.
From Undecidability.L.AbstractMachines Require Import FunctionalDefinitions.
From Undecidability.L.Datatypes Require Import LTerm LOptions LProd.

From Undecidability.L Require Import AbstractMachines.LargestVar.


From Undecidability.L.AbstractMachines Require Import AbstractHeapMachineDef AbstractHeapMachine.
From Undecidability.L.AbstractMachines.Computable Require Import Shared Lookup.

(** *** Heap Machine *)
Import GenEncode.
Run TemplateProgram (tmGenEncode "task_enc" task).
Hint Resolve task_enc_correct : Lrewrite.
Instance termT_S : computableTime' closT (fun _ _ => (1,tt)).
Proof.
  extract constructor.
  solverec.
Defined.

Instance TermT_init : computableTime' init (fun s _ => (108 * size s + 44,tt)).
Proof. extract. solverec. Qed.


(** *** Heap Machine Step *)


Definition heapStep_time (T:list task) (H: list heapEntry) :=
  match T with
    closT (var n,_)::_ => lookupTime (length H) n
  | appT::_ => length H*27 
  | _ => 0
  end + 84.


Definition heapStep_timeBound maxVar k :=
  lookupTime k maxVar + k * 27 + 84.

Lemma heapStep_timeBound_le s k T V H:
  pow step k (init s) (T,V,H) ->
  heapStep_time T H <= heapStep_timeBound (largestVar s) k.
Proof.
  intros H'.
  unfold heapStep_timeBound, heapStep_time. destruct T as [|[|[[] a]]].
  1,4,5:now Lia.lia.
  -rewrite length_H. 2:eassumption. Lia.lia.
  -rewrite lookupTime_mono with (k':=k) (n':=largestVar s).
   +Lia.lia.
   +eapply length_H;eassumption.
   +eapply subterm_property in H' as (H'&_).
    rewrite <- subterm_largestVar. 2:eapply H'. 2:eauto. easy.
Qed.

Lemma heapStep_timeBound_mono' maxVar maxVar'  k k' :
  k <= k' -> maxVar <= maxVar' ->
  heapStep_timeBound maxVar k <= heapStep_timeBound maxVar' k'.
Proof.
  intros H1 H3. 
  unfold heapStep_timeBound. rewrite Lookup.lookupTime_mono. 2,3:eassumption. Lia.nia.
Qed.

Lemma heapStep_timeBound_mono maxVar k k' :
  k <= k' -> heapStep_timeBound maxVar k <= heapStep_timeBound maxVar k'.
Proof.
  intros. 
  unfold heapStep_timeBound. rewrite lookupTime_mono. 2:eassumption. 2:reflexivity. Lia.lia.
Qed.

Instance term_heapStep : computableTime' heapStep (fun '(T,V,H) _ => (heapStep_time T H,tt)).
Proof.
  Arguments put : simpl never.
  extract.
  {unfold heapStep_time. recRel_prettify2.
   all:cbn [length].
   all:try Lia.nia.
  }
Qed.
(* with Lrewrite_new: *)
(* QED: <infomsg>Finished transaction in 58.067 secs (57.751u,0.056s) (successful)</infomsg>*)
(* Tactics: total time:     61.772s *)

(* with Lsimpl: *)
(*total time:    200.012s *)
(* Finished transaction in 27.174 secs (27.097u,0.s) (successful) *)
