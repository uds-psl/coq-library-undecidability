From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.

(** Minimal separation logic **)

(** Syntax **)

Definition sp_term := option nat.

Inductive msp_form :=
| mpointer : sp_term -> sp_term -> sp_term -> msp_form
| mbot : msp_form
| mimp : msp_form -> msp_form -> msp_form
| mall : msp_form -> msp_form.

(** Semantics **)

Definition val := option nat.
Definition stack := nat -> val.
Definition heap := list (nat * (val * val)).

Definition sp_eval (s : stack) (t : sp_term) : val :=
  match t with Some x => s x | None => None end.

Definition update_stack (s : stack) v :=
  fun x => match x with 0 => v | S x => s x end.

Fixpoint msp_sat (s : stack) (h : heap) (P : msp_form) :=
  match P with
  | mpointer E E1 E2 => exists l, sp_eval s E = Some l /\ (l, (sp_eval s E1, sp_eval s E2)) el h
  | mbot => False
  | mimp P1 P2 => msp_sat s h P1 -> msp_sat s h P2
  | mall P => forall v, msp_sat (update_stack s v) h P
  end.

(** Satisfiability problem **)

Definition functional (h : heap) :=
  forall l p p', (l, p) el h -> (l, p') el h -> p = p'.

Definition MSPSAT (P : msp_form) :=
  exists s h, functional h /\ msp_sat s h P. 
