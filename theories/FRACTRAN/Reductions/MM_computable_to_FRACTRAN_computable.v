From Undecidability.MinskyMachines Require Import MM_computable MM_sss.
From Undecidability.FRACTRAN Require Import FRACTRAN_computable mm_fractran prime_seq.
From Undecidability.Shared.Libs.DLW Require Import gcd prime vec.

Require Import Nat Arith Lia List.

Lemma prime_qs n : prime (qs n).
Proof.
  eapply nthprime_prime.
Qed.

Opaque ps qs.

Lemma exp_const i m : exp i (Vector.const 0 m) = 1.
Proof.
  induction m in i |- *; cbn.
  - reflexivity.
  - now rewrite IHm.
Qed.

Lemma exp_app {n} (v : Vector.t nat n) i m (w : Vector.t nat m) :
  exp i (Vector.append v w) = exp i v * exp (i + n) w.
Proof.
  induction v in i, m, w |- *; cbn.
  - now rewrite !Nat.add_0_r.
  - rewrite IHv. ring_simplify. do 2 f_equal. lia.
Qed.

Theorem MM_computable_to_FRACTRAN_computable {k} (R : Vector.t nat k -> nat -> Prop) :
  MM_computable R -> FRACTRAN_computable R.
Proof.
  intros (n & P & H). 
  eapply FRACTRAN_computable_iff. setoid_rewrite eval_iff in H.
  pose proof (mm_fractran_n_strong P) as (P' & regP & HP1 & HP2).
  exists P'. setoid_rewrite H. clear H. split. 1: eapply regP.
  setoid_rewrite FRACTRAN_sss.eval_iff. fold plus.
  intros v. split.
  - intros m. fold plus in *. intros (j & v' & H).
    edestruct HP1 as [j' Hj'].
    + eexists. eapply H.
    + rewrite FRACTRAN_sss.eval_iff in Hj'.
      unfold encode_state in Hj'. cbn in *.
      rewrite !PeanoNat.Nat.add_0_r in *.
      exists (ps j' * exp 2 v').
      split.
      * replace (ps j' * exp 2 v' * PeanoNat.Nat.pow (qs 1) m)
        with (ps j' * (PeanoNat.Nat.pow (qs 1) m) * exp 2 v') by lia. 
        now rewrite exp_app, exp_const, Nat.mul_1_r, !mult_assoc in Hj'.
      * intros [Hp | Hp] % prime_div_mult. 3: eapply prime_qs.
        -- now eapply qs_ps_div in Hp.
        -- eapply qs_exp_div in Hp. 2: lia. eauto.
  - specialize (HP2 (0 ## (Vector.append v (Vector.const 0 n)))). cbn in HP2.
    rewrite Nat.add_0_r, exp_app, exp_const, Nat.mul_1_r in HP2.
    intros ((c & w) & H) % HP2. revert H.
    eapply (Vector.caseS' w). clear w. intros m w H.
    exists m, c, w. cbn. eapply H.
Qed.