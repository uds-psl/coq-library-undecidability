From Undecidability.Synthetic Require Import Definitions.
Require Import Setoid.

Fact Dec_decider_nat p :
  decidable p -> exists f : nat -> nat, forall x : nat, p x <-> f x = 0.
Proof.
  intros [f Hf].
  exists (fun n => if f n then 0 else 1).
  intros x. specialize (Hf x).
  unfold reflects in *.
  destruct (f x) eqn:Hx; try tauto.
  rewrite Hf. split; congruence.
Qed.

Fact enumerable_nat p :
  enumerable p -> exists f, forall x : nat, p x <-> exists n : nat, f n = S x.
Proof. 
  intros [f Hf]. 
  exists (fun n => match f n with Some x => S x | _ => 0 end).
  unfold enumerator in *.
  intros x. rewrite Hf. split; intros [n Hn]; exists n. 
  - now rewrite Hn.
  - destruct (f n); congruence.
Qed.
