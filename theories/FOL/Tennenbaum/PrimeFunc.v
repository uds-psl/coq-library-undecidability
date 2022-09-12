
Definition div x n := exists k, n = k*x.
Definition prime p := p > 1 /\ forall a b, div p (a*b) -> div p a \/ div p b.


Definition Prime : nat -> nat. Admitted.

Lemma Prime_prime x :
  prime (Prime x).
Proof.
Admitted.

Lemma Prime_inj x y :
  Prime x = Prime y -> x = y.
Proof.
Admitted.