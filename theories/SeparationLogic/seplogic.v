From Undecidability Require Import SeparationLogic.min_seplogic.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.

(** Separation logic **)

(** Syntax **)

Inductive sp_form :=
| pointer : sp_term -> sp_term -> sp_term -> sp_form
| equality : sp_term -> sp_term -> sp_form
| bot : sp_form
| imp : sp_form -> sp_form -> sp_form
| all : nat -> sp_form -> sp_form
| emp : sp_form
| sand : sp_form -> sp_form -> sp_form
| simp : sp_form -> sp_form -> sp_form.

(** Semantics **)

Definition disjoint (h h' : heap) :=
  ~ exists l p p', (l, p) el h /\ (l, p') el h'.

Definition equiv (h h' : heap) :=
  h <<= h' /\ h' <<= h.

Fixpoint sp_sat (s : stack) (h : heap) (P : sp_form) :=
  match P with
  | pointer E E1 E2 => exists l, sp_eval s E = Some l /\ h = [(l, (sp_eval s E1, sp_eval s E2))]
  | equality E1 E2 => sp_eval s E1 = sp_eval s E2
  | bot => False
  | imp P1 P2 => sp_sat s h P1 -> sp_sat s h P2
  | all x P => forall v, sp_sat (update_stack s x v) h P
  | emp => h = nil
  | sand P1 P2 => exists h1 h2, equiv h (h1 ++ h2) /\ sp_sat s h1 P1 /\ sp_sat s h2 P2
  | simp P1 P2 => forall h', disjoint h h' -> sp_sat s h' P1 -> sp_sat s (h ++ h') P2
  end.

(** Satisfiability problem **)

Definition SPSAT (P : sp_form) :=
  exists s h, sp_sat s h P.

(** Example **)

Goal SPSAT (sand (pointer (Some 0) (Some 10) (Some 1)) (pointer (Some 1) (Some 11) (Some 0))).
Proof.
  exists Some, [(0, (Some 10, Some 1)); (1, (Some 11, Some 0))]. cbn.
  exists [(0, (Some 10, Some 1))], [(1, (Some 11, Some 0))]. cbn.
  split. firstorder. intuition eauto.
Qed.
