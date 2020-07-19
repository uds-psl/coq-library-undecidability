Require Export Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.
Require Import Undecidability.TM.Halting.

Definition undecidable {X} (p : X -> Prop) :=
  decidable p -> decidable (HaltTM 1).

Lemma undecidability_HaltTM :
  undecidable (HaltTM 1).
Proof.
  intros H. exact H.
Qed.

Lemma undecidability_from_reducibility {X} {p : X -> Prop} {Y} {q : Y -> Prop} :
  undecidable p -> p ⪯ q -> undecidable q.
Proof.
  unfold undecidable, decidable, decider, reduces, reduction, reflects.
  intros H [f Hf] [d Hd]. eapply H. exists (fun x => d (f x)). intros x. rewrite Hf. eapply Hd.
Qed.
