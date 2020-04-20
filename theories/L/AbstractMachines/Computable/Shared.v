From Undecidability.L Require Import L Tactics.LTactics.

From Undecidability.L.AbstractMachines Require Import Programs FunctionalDefinitions AbstractHeapMachineDef.
From Undecidability.L.Datatypes Require Import Lists LOptions LProd LTerm.

From Undecidability.L Require Import Tactics.GenEncode.

(** * Computability in L *)

(** *** Encoding Heaps *)
Import AbstractHeapMachineDef.

Run TemplateProgram (tmGenEncode "heapEntry_enc" heapEntry).
Hint Resolve heapEntry_enc_correct : Lrewrite.

Instance term_heapEntryC : computableTime' heapEntryC (fun _ _ => (1,fun _ _ => (1,tt))).
extract constructor. solverec.
Qed.

(** *** Primitive functions with Heaps*)

Instance term_get : computableTime' get (fun A _ => (1,fun n _ => (min n (length A)*15+16,tt))).
extract. solverec.
Qed.

Import Datatypes.
Instance put_get : computableTime' put (fun A _ => (1,fun _ _ => (length A * 27 + 22,tt))).
extract. solverec.
Qed.
