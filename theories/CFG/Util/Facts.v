Require Import List Lia.
Import ListNotations.

Fixpoint count (l : list nat) (n : nat)  :=
  match l with
  | [] => 0
  | m :: l => if Nat.eqb n m then S (count l n) else count l n
  end.

Lemma count_count_occ {l n} : count (l : list nat) (n : nat) = count_occ PeanoNat.Nat.eq_dec l n.
Proof.
  induction l as [|a l IH]; [reflexivity|].
  cbn. destruct (PeanoNat.Nat.eq_dec a n) as [->|Han%PeanoNat.Nat.eqb_neq].
  - now rewrite PeanoNat.Nat.eqb_refl, IH.
  - now rewrite PeanoNat.Nat.eqb_sym, Han.
Qed.

Lemma countSplit (A B: list nat) (x: nat) : count A x + count B x = count (A ++ B) x. 
Proof.
  now rewrite ?count_count_occ, count_occ_app.
Qed.

Lemma notInZero (x: nat) A :
  not (In x A) <-> count A x = 0.
Proof.
  rewrite ?count_count_occ. now apply count_occ_not_In.
Qed.

Lemma rev_eq {X : Type} (A B: list X):
  List.rev A = List.rev B <-> A = B.
Proof.
  split.
  - intros H%(f_equal (@rev X)). now rewrite !rev_involutive in H.
  - now intros <-.
Qed.

Lemma list_prefix_inv X (a : X) x u y v :
  ~ In a x -> ~ In a u -> x ++ a :: y = u ++ a :: v -> x = u /\ y = v.
Proof.
  intro. revert u.
  induction x; intros; destruct u; inversion H1; subst; try now firstorder.
  eapply IHx in H4; try now firstorder. intuition congruence.
Qed.

Fixpoint fresh (l : list nat) :=
  match l with
  | [] => 0
  | x :: l => S x + fresh l
  end.

Lemma fresh_spec (a : nat) (l : list nat) : In a l -> fresh l <> a.
Proof.
  intros H. enough (a < fresh l) by lia.
  revert H. induction l.
  - easy.
  - cbn; intros [ | ]; intuition lia.
Qed.
