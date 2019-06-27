From Undecidability.L Require Import Tactics.LTactics.
From Undecidability.L.Datatypes Require Import Lists.

From Undecidability.L.AbstractMachines Require Import AbstractHeapMachineDef Computable.Shared.

Definition lookupTime l x := (x+1) * (l*15 + 38).

Instance term_lookup : computableTime' lookup (fun H _ => (5,fun alpha _ => (1,fun x _ => (lookupTime (length H) x ,tt)))).
extract. unfold lookupTime. solverec.
Qed.


Lemma lookupTime_mono k k' n n' :
  k <= k' -> n <= n' -> lookupTime k n <= lookupTime k' n'.
Proof.
  unfold lookupTime. now intros -> ->. 
Qed.
