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
  intros (P & Hreg & HP) v m1 m2 (j1 & k1 & v1 & H1) % HP (j2 & k2 & v2 & H2) % HP. 
  eapply eval_iff in H1 as [H1 H1'], H2 as [H2 H2'].
  eapply fractran_compute_fun in H1'; eauto.
  eapply power_factor_uniq with (x := ps j1 * enc 2 v1) (y := ps j2 * enc 2 v2) (p := qs 1).
  - epose proof (nxtprime_spec1 (nxtprime (nxtprime 2))). cbn. lia.
  - intros [[] % qs_ps_div | H] % prime_div_mult.
    + change (enc 1 v1) with (exp 1 v1) in H.
      eapply qs_exp_div in H; lia.
    + eapply nxtprime_spec2.
  - intros [[] % qs_ps_div | H] % prime_div_mult.
    + clear - H. induction v2.
      * eapply divides_1_inv in H. cbn in H.
        pose proof (nxtprime_spec2 (nxtprime (nxtprime 2))).
        eapply prime_ge_2 in H0. lia.
      * eapply qs_exp_div in H; lia.
    + eapply nxtprime_spec2.
  - lia.
Qed.