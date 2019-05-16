From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import LM_heap_def.
From Undecidability Require Import HaltingProblem.



Definition test_Controll : list HClos := [(0, [lamT; varT 0; retT; lamT; varT 0; retT; appT])].
Definition test_Argument : list HClos := [].
Definition test_Heap : Heap := [ None ].


Definition steps_needed := Eval compute in Loop_steps test_Controll test_Argument test_Heap 3.

Definition min_steps_needed := 4749.

Definition res := Eval vm_compute in execTM_p Loop (initTapes (test_Controll, test_Argument, test_Heap)) min_steps_needed.


Ltac valOf x :=
  let x' := eval compute in x in
  lazymatch x' with
  | Some ?y => exact y
  end.

Definition res' := ltac:(valOf res).


Compute right ((fst res')[@Fin0]).
(* [inr (inl sigList_nil); inl STOP] *)
Check nil : list HClos.

Compute right ((fst res')[@Fin1]).
(* [inr (inl sigList_cons); inr (inl (sigList_X (sigPair_X sigNat_O))); inr (inl (sigList_X (sigPair_Y sigList_cons))); 
    inr (inl (sigList_X (sigPair_Y (sigList_X sigSum_inl)))); inr (inl (sigList_X (sigPair_Y (sigList_X (sigSum_X sigNat_O))))); inr (inl (sigList_X (sigPair_Y sigList_nil)));
    inr (inl sigList_nil); inl STOP] *)
Check [ ( 0, [ varT 0 ] ) ] : list HClos.
  

Compute right ((fst res')[@Fin2]).
(* [inr (inr sigList_cons); inr (inr (sigList_X sigOption_None)); inr (inr sigList_cons); inr (inr (sigList_X sigOption_Some));
    inr (inr (sigList_X (sigOption_X (sigPair_X (sigPair_X sigNat_O))))); inr (inr (sigList_X (sigOption_X (sigPair_X (sigPair_Y sigList_cons)))));
    inr (inr (sigList_X (sigOption_X (sigPair_X (sigPair_Y (sigList_X sigSum_inl))))));
    inr (inr (sigList_X (sigOption_X (sigPair_X (sigPair_Y (sigList_X (sigSum_X sigNat_O))))))); inr (inr (sigList_X (sigOption_X (sigPair_X (sigPair_Y sigList_nil)))));
    inr (inr (sigList_X (sigOption_X (sigPair_Y sigNat_O)))); inr (inr sigList_nil); inl STOP] *)
Check [ None; Some ((0, [varT 0]), 0) ] : Heap.


(* The same steps that the machine calculated as Heap Machine reduction *)
Goal steps_k 4 (test_Controll, test_Argument, test_Heap) (nil, [ (0, [ varT 0 ] ) ], [ None; Some ((0, [varT 0]), 0) ] ).
Proof.
  (*
  econstructor.
  { econstructor. cbn. reflexivity. }
  econstructor.
  { econstructor. cbn. reflexivity. }
  econstructor.
  { econstructor. cbv. reflexivity. }
  cbn. econstructor.
  { econstructor. cbn. reflexivity. }
  cbn. constructor.
   *)
  repeat (econstructor; [ (econstructor; cbn; reflexivity) | ]); constructor.
Qed.
