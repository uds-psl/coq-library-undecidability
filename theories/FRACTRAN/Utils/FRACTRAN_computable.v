Require Import Undecidability.FRACTRAN.FRACTRAN.

From Coq Require Import List Vector Nat Arith Lia.
From Undecidability.FRACTRAN Require Import prime_seq.
Import ListNotations Vector.VectorNotations.
From Undecidability Require Import Utils.gcd Utils.prime FRACTRAN_sss Code.sss fractran_utils.

Fixpoint enc {k} i (v : Vector.t nat k) : nat := 
  match v with
  | @nil _ => 1
  | x :: v => (qs i) ^ x * enc (S i) v
  end.

Definition FRACTRAN_computable {k} (R : Vector.t nat k -> nat -> Prop) := 
  exists P : list (nat * nat), fractran_regular P /\
    forall v : Vector.t nat k,
      (forall m, R v m <-> exists j, fractran_eval P (ps 1 * enc 2 v) (j * (qs 1)^m) /\ ~ divides (qs 1) j).

Lemma FRACTRAN_computable_functional {k} (R : Vector.t nat k -> nat -> Prop) :
  FRACTRAN_computable R -> forall v m1 m2, R v m1 -> R v m2 -> m1 = m2.
Proof.
  intros (P & Hreg & HP) v m1 m2 (j1 & H1 & Hj1) % HP (j2 & H2 & Hj2) % HP. 
  eapply eval_iff in H1 as [H1 H1'], H2 as [H2 H2'].
  eapply fractran_compute_fun in H1'; eauto.
  rewrite mult_comm in H1' at 1. symmetry in H1'.
  rewrite mult_comm in H1' at 1. symmetry in H1'.
  eapply power_factor_uniq in H1'.
  - firstorder.
  - epose proof (nxtprime_spec1 (nxtprime (nxtprime 2))). cbn. lia.
  - eauto.
  - eauto.
Qed.

Lemma FRACTRAN_computable_iff {k} (R : Vector.t nat k -> nat -> Prop) : 
  (exists P : list (nat * nat), fractran_regular P /\
    forall v : Vector.t nat k,
      (forall m, R v m -> exists j, fractran_eval P (ps 1 * enc 2 v) (j * (qs 1)^m) /\ ~ divides (qs 1) j) /\
      ((exists j, fractran_eval P (ps 1 * enc 2 v) (j)) -> exists m, R v m)) -> FRACTRAN_computable R.
Proof.
  intros (P & regP & H). exists P. split. 1: eauto.
  intros v m. split. 1: eapply H.
  intros (j & H1 & Hj).
  edestruct (H v) as [_tmp [m' ]]. clear _tmp. 1: eauto.
  enough (m' = m) as -> by eauto.
  eapply H in H0 as [j' [H' Hdiv]].
  rewrite FRACTRAN_sss.eval_iff in H1, H'. destruct H1 as [H1 H1'].
  destruct H' as [H' H''].
  eapply fractran_compute_fun in H1; eauto.
  rewrite mult_comm in H1 at 1. symmetry in H1.
  rewrite mult_comm in H1 at 1. symmetry in H1.
  eapply power_factor_uniq in H1.
  - firstorder.
  - epose proof (nxtprime_spec1 (nxtprime (nxtprime 2))). cbn. lia.
  - eauto.
  - eauto.
Qed.
  
