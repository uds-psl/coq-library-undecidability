From Undecidability.L Require Export L.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
(** ** Encoding of booleans *)

(* Definition bool_enc (b:bool) : term:= *)
(*   Eval simpl in *)
(*     if b then .\"t", "f"; "t" else .\"t", "f"; "f". *)

Run TemplateProgram (tmGenEncode "bool_enc" bool).
(* For each encoding, Lrewrite must contain an lemma that solves goals like "encode b s t >* match ...end". The database Lrewrite also calls Lproc to discharge the other assumptions *)
Hint Resolve bool_enc_correct : Lrewrite.

(* register thefunctional constructors (not neccessary here) *)
(*
Instance true_term : computableTime' true tt.
Proof.
  extract constructor.
  solverec.
Qed.

Instance false_term : computableTime' false tt.
Proof.
  extract constructor.
  solverec.
Qed.*)

Instance term_negb : computableTime' negb (fun _ _ => (4,tt)).
Proof.
  extract.
  solverec.
Qed.

Instance term_andb : computableTime' andb (fun _ _ => (1,fun _ _ => (4,tt))).
Proof.
  extract.
  solverec.
Qed.

Instance term_orb : computableTime' orb (fun _ _ => (1,fun _ _ => (4,tt))).
Proof.
  extract.
  solverec.
Qed.

