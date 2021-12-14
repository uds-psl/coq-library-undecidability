Require Export Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.
From Undecidability.Synthetic Require Import
  DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
Require Import Undecidability.L.L.
Require Import Undecidability.L.Util.term_enum.

Definition undecidable {X} (p : X -> Prop) :=
  decidable p -> enumerable (complement HaltL).

Lemma undecidability_HaltL :
  undecidable (HaltL).
Proof.
  intros H%dec_compl.
  now eapply (dec_count_enum H), enumerator_enumerable, enumerator__T_term.
Qed.

(*
Require Export Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.
Require Import Undecidability.TM.TM.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts.
Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypesDef.
*)

Lemma undecidability_from_reducibility {X} {p : X -> Prop} {Y} {q : Y -> Prop} :
  undecidable p -> p ⪯ q -> undecidable q.
Proof.
  unfold undecidable, decidable, decider, reduces, reduction, reflects.
  intros H [f Hf] [d Hd]. eapply H. exists (fun x => d (f x)). intros x. rewrite Hf. eapply Hd.
Qed.

Module UndecidabilityNotations.

Tactic Notation "undec" "from" constr(H) :=
  apply (undecidability_from_reducibility H).

Tactic Notation "reduce" "with" "chain" constr(H) := 
  repeat (apply (reduces_reflexive _) || (eapply reduces_transitive; [ apply H | ])).

Tactic Notation "undec" "from" constr(U) "using" "chain" constr(C) :=
  undec from U; reduce with chain C.

End UndecidabilityNotations.
