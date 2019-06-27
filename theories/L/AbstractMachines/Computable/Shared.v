From Undecidability.L Require Import L Tactics.LTactics.

From Undecidability.L.AbstractMachines Require Import Programs FunctionalDefinitions AbstractHeapMachineDef.
From Undecidability.L.Datatypes Require Import Lists LOptions.

From Undecidability.L Require Import Tactics.GenEncode.

(** * Computability in L *)
(** *** Encoding for Tokens *)

Run TemplateProgram (tmGenEncode "token_enc" Tok).
Hint Resolve token_enc_correct : Lrewrite.

Instance term_varT : computableTime' varT (fun _ _ => (1,tt)).
extract constructor. solverec.
Qed.

(* Instance term_tok_eqb : computableTime' Tok_eqb (fun t _ => (1,fun t' _ => (min (sizeT t) (sizeT t') * 17 + 10,tt))). *)
(* extract. solverec. *)
(* Qed. *)

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


Instance put_get : computableTime' put (fun A _ => (1,fun _ _ => (length A * 27 + 22,tt))).
extract. solverec.
Qed.
