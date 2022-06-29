From Undecidability.L Require Export LTactics LTerm Functions.Encoding Tactics.Lbeta_nonrefl.
Import L_Notations.

(* * First Fixed Point Theorem *)

Theorem FirstFixedPoint (s : term) : closed s -> exists t, closed t /\ s t == t.
Proof.
  intros cls_s.
  pose (A := lam (s (#0 #0))).
  pose (t := A A).
  exists t. split;[subst t A;Lproc|].
  symmetry. cbv. now redStep.
Qed.

(* * Second Fixed Point Theorem *)

Theorem SecondFixedPoint (s : term) : closed s -> exists t, closed t /\ s (enc t) == t.
Proof.
  intros cls_s.
  pose (A := lam(s ((ext app) #0 ((ext (enc (X:= term))) #0)))).
  pose (t := A (ext A)).
  exists t. split;[subst t A;Lproc|].
  symmetry. change (enc t) with (ext t).
  unfold t. unfold A at 1.
  redSteps. now Lsimpl.
Qed.

Goal exists t, closed t /\ t == (enc t).
Proof.
  destruct (SecondFixedPoint) with ( s := I) as [t [cls_t A]]. Lproc.
  exists t.
  split. Lproc. rewrite <- A at 1. clear A. unfold I. now Lsimpl.
Qed.
