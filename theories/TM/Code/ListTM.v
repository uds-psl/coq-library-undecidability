From Undecidability.TM.Code.List Require Export Nth Cons_constant App Length Rev Concat_Repeat.

From Undecidability Require Import HoareLogic.
Ltac hstep_ListTM :=
  match goal with
  | [ |- TripleT ?P ?k (Nth' _ _) ?Q ] => eapply Nth'_SpecT_size
  end.

Smpl Add hstep_ListTM : hstep_smpl.
