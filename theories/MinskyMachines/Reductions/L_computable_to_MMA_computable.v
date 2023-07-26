(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  If a relation R is L_computable then it is MMA_computable.
*)

From Undecidability Require Import
  MinskyMachines.MMA L.L.

From Undecidability Require Import
  MinskyMachines.Reductions.L_computable_closed_to_MMA_computable
  L.Util.ClosedLAdmissible.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

Theorem L_computable_to_MMA_computable {k} (R : Vector.t nat k -> nat -> Prop) :
  L_computable R -> MMA_computable R.
Proof.
  move=> /L_computable_can_closed.
  by apply: L_computable_closed_to_MMA_computable.
Qed.
