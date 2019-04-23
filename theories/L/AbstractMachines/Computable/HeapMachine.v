From Undecidability.L Require Import L.
From Undecidability.L.AbstractMachines Require Import Programs FunctionalDefinitions.
From Undecidability.L.Datatypes Require Import LNat LProd Lists LOptions.
From Undecidability.L Require AbstractHeapMachine.
From Undecidability.L Require Import AbstractMachines.Computable.Shared.
From Undecidability.L.Tactics Require Import LTactics.

(** *** Heap Machine *)

Import AbstractHeapMachine.

Run TemplateProgram (tmGenEncode "heapEntry_enc" heapEntry).
Hint Resolve heapEntry_enc_correct : Lrewrite.

Instance term_heapEntryC : computableTime heapEntryC (fun _ _ => (1,fun _ _ => (1,tt))).
extract constructor. solverec.
Qed.


Instance term_get : computableTime get (fun A _ => (1,fun n _ => (min n (length A)*15+16,tt))).
extract. solverec.
Qed.


Instance put_get : computableTime put (fun A _ => (1,fun _ _ => (length A * 27 + 22,tt))).
extract. solverec.
Qed.

Instance term_lookup : computableTime lookup (fun H _ => (5,fun alpha _ => (1,fun x _ => ((1+x)*(length H*15 + 38),tt)))).
extract. solverec.
Qed.

Definition heapStep_time (T:list clos) (H: list heapEntry) :=
  match T with
    (varT n :: _,_)::_ => (n+1)*(length H*15+38)
  | (appT::_,_)::_ => length H*27 
  | (lamT::_ as P,_)::_ => length P *36 (* only because of the linear encoding of programs! *)
  | _ => 0
  end + 84.

Instance term_heapStep : computableTime heapStep (fun '(T,V,H) _ => (heapStep_time T H,tt)).
Proof.
  Arguments put : simpl never.
  extract.

  Unshelve.
  5:{inv eq8. now Intern.extractCorrectCrush_new. }
  {inv eq8. Intern.cstep. }
  {unfold heapStep_time. recRel_prettify2.
   all:cbn [length].
   all:Lia.nia.
  }
Qed.
(* with Lrewrite_new: *)
(* QED: <infomsg>Finished transaction in 58.067 secs (57.751u,0.056s) (successful)</infomsg>*)
(* Tactics: total time:     61.772s *)

(* with Lsimpl: *)
(*total time:    200.012s *)
(* Finished transaction in 27.174 secs (27.097u,0.s) (successful) *)
