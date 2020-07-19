Require Import Undecidability.Synthetic.DecidabilityFacts.


Lemma decidable_semi_decidable {X} {p : X -> Prop} :
  decidable p -> semi_decidable p.
Proof.
  intros [f H].
  exists (fun x n => f x). intros x.
  unfold decider, reflects in H.
  rewrite H. firstorder. econstructor.
Qed.

Lemma decidable_compl_semi_decidable {X} {p : X -> Prop} :
  decidable p -> semi_decidable (compl p).
Proof.
  intros H.
  now eapply decidable_semi_decidable, decidable_compl.
Qed.
