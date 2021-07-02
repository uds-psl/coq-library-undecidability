Require Import Undecidability.FRACTRAN.FRACTRAN.

From Coq Require Import List Vector Nat.
Import ListNotations Vector.VectorNotations.
From Undecidability Require Import Utils.prime FRACTRAN_sss Code.sss fractran_utils.

Fixpoint enc {k} p i (v : Vector.t nat k) : nat := 
  match v with
  | @nil _ => 1
  | x :: v => (p i) ^ x * enc p (S i) v
  end.

Definition FRACTRAN_computable {k} (p : nat -> nat) (R : Vector.t nat k -> nat -> Prop) := 
  exists P : list (nat * nat), fractran_regular P /\
    forall v : Vector.t nat k,
      (forall m, R v m <-> fractran_eval P (enc p 1 v) ((p 0)^m))
    /\ (forall n, fractran_eval P (enc p 1 v) n -> exists m, n = (p 0) ^ m).

Lemma FRACTRAN_computable_functional {k} (p : nat -> nat) (R : Vector.t nat k -> nat -> Prop) :
  (forall i j, p i = p j -> i = j) ->
  (forall i, prime (p i)) ->
  FRACTRAN_computable p R -> forall v m1 m2, R v m1 -> R v m2 -> m1 = m2.
Proof.
  intros Hpf Hpp (P & Hreg & HP) v m1 m2 H1 % HP H2 % HP. 
  eapply eval_iff in H1 as [H1 H1'], H2 as [H2 H2'].
  assert (p 0 ^ m1 = p 0 ^ m2).
  - eapply fractran_compute_fun; eauto.
  - assert (prime (p 0)) as ? % prime_ge_2 by eauto.
    eapply PeanoNat.Nat.pow_inj_r; try eassumption.
Qed.