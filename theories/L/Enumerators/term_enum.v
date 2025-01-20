Require Import Undecidability.Synthetic.EnumerabilityFacts.
Require Import Undecidability.L.L.
From Stdlib Require Cantor.
From Stdlib Require Import Lia.

Fixpoint term_enum_rec (k n: nat) : term :=
  match k with
  | 0 => var 0
  | S k => 
    match Cantor.of_nat n with
    | (0, n') => var n'
    | (S (S n1), n2) => app (term_enum_rec k n1) (term_enum_rec k n2)
    | (1, n') => lam (term_enum_rec k n')
    end
  end.

Opaque Cantor.to_nat Cantor.of_nat.

Definition term_enumerator__T (n : nat) := Some (term_enum_rec (S n) n).
Lemma enumerator__T_term :
  enumerator__T term_enumerator__T term.
Proof.
  intros t. unfold term_enumerator__T.
  enough (exists n, forall m, n <= m -> term_enum_rec (S m) n = t) as [n Hn].
  { exists n. f_equal. now apply Hn. }
  induction t as [n|s [n1 IHs] t [n2 IHt]|s [n IH]].
  - exists (Cantor.to_nat (0, n)). cbn.
    now rewrite Cantor.cancel_of_to.
  - exists (Cantor.to_nat (S (S n1), n2)). cbn.
    assert (H' := Cantor.to_nat_non_decreasing (S (S n1)) n2).
    intros [|m] ?. { lia. }
    rewrite !Cantor.cancel_of_to, IHs, IHt; [easy | lia | lia].
  - exists (Cantor.to_nat (1, n)). cbn.
    assert (H' := Cantor.to_nat_non_decreasing 1 n).
    intros [|m] ?. { lia. }
    rewrite !Cantor.cancel_of_to, IH; [easy | lia ].
Qed.
