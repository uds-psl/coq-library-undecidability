Require Export Undecidability.Synthetic.Definitions.
(* questionable Import *)
Require Export Undecidability.Synthetic.ReducibilityFacts.

Require Import Undecidability.L.L.

(* P is undecidable if decidability of P implies co-enumerability of L halting *)
Definition undecidable {X} (p : X -> Prop) :=
  decidable p -> enumerable (complement HaltL).

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
