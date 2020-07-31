Require Import Omega Lia List.
From Undecidability.HOU Require Import calculus.prelim.
Import ListNotations.

(* * H10 *)
Inductive deq :=
| Con (x: nat)
| Add (x y z: nat)
| Mul (x y z: nat).


Notation "x =ₑ 1" := (Con x) (at level 66).
Notation "x +ₑ y =ₑ z" := (Add x y z) (at level 66, y at next level).
Notation "x *ₑ y =ₑ z" := (Mul x y z) (at level 66, y at next level).
Reserved Notation "sigma ⊢ₑ e" (at level 60, e at level 99).

Inductive sol (sigma: nat -> nat) : deq -> Prop :=
| solC x: sigma x = 1 -> sigma ⊢ₑ x =ₑ 1
| solA x y z: sigma x + sigma y = sigma z -> sigma ⊢ₑ x +ₑ y =ₑ z
| solM x y z: sigma x * sigma y = sigma z -> sigma ⊢ₑ x *ₑ y =ₑ z
where "sigma ⊢ₑ e" := (sol sigma e).

Definition Sol (sigma: nat -> nat) (E: list deq) := forall e, e ∈ E -> sigma ⊢ₑ e.
Notation "sigma ⊢⁺ₑ E" := (Sol sigma E) (at level 60, E at level 99).
Definition H10 (E: list deq) := exists sigma, sigma ⊢⁺ₑ E.



Definition vars__de (e: deq) :=
  match e with
  | x =ₑ 1 => [x]
  | x +ₑ y =ₑ z => [x; y; z]
  | x *ₑ y =ₑ z => [x; y; z]
  end.

Definition Vars__de E :=
  nodup Nat.eq_dec (flat_map vars__de E).



Lemma Vars__de_in e E:
  e ∈ E -> forall y, y ∈ vars__de e -> y ∈ Vars__de E.
Proof.
  unfold Vars__de; intros; eapply nodup_In, in_flat_map.
  exists e. intuition.
Qed.
















