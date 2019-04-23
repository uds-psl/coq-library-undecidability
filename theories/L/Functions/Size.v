From Undecidability.L Require Import Tactics.LTactics Functions.Encoding.
Require Import Nat.

(** ** Extracted size of terms *)

Instance term_size : computable size'.
Proof.
  extract.
Defined.

Lemma size'_surj : surjective size'.
Proof.
  intros n. induction n.
  -exists (var 0). cbn. omega.
  -destruct IHn as [x <-].
   exists (lam x). cbn. easy. 
Qed.
