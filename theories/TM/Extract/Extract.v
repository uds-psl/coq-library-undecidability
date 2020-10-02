From Coq Require Import Extraction.
From Undecidability Require Import TM.Code.ProgrammingTools.
From Undecidability Require Import Undecidability.L.AbstractMachines.TM_LHeapInterpreter.HaltingProblem.M_LHeapInterpreter.


(* The number of symbols in the alphabet *)
(* You must change the [Retract] instances in [TM.Code.Code] to [Defined.] *)
(* Eval vm_compute in length (FinTypes.elem (finType_CS sigStep)). *)




Definition Loop_states : finType := TM.state (projT1 Loop).
Definition Loop_states_card : nat := length (FinTypes.elem Loop_states).


Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].
Extract Inductive list => "([])" [ "[]" "(:)" ].
Extract Inductive prod => "(,)" [ "(,)" ].
Extract Inductive nat => "Prelude.Int" [ "0" "Prelude.succ" ] "(\fO fS n -> if n==0 then fO () else fS (pred n))".

Recursive Extraction Loop_states_card.

(* Save the output to a "countStates.hs" file and make the following modifications: *)
(* Instead of [import qualid Prelude] -> [import Prelude hiding (seq, return, Left, Right, repeat, map, elem, concat, length, const, null, id, lookup)] *)
(* Add [main = print (loop_states_card)] to the end of the file *)
(* Compile and execute with [ghc -dynamic countStates.hs && ./countStates] *)
(* Should run in two-three minutes *)
