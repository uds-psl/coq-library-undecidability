From Undecidability.MinskyMachines Require Import MM_computable MM_sss.
From Undecidability.FRACTRAN Require Import FRACTRAN_computable mm_fractran prime_seq.

Opaque ps qs.

Theorem MM_computable_to_FRACTRAN_computable {k} (R : Vector.t nat k -> nat -> Prop) :
  MM_computable R -> FRACTRAN_computable R.
Proof.
  intros (n & P & H). setoid_rewrite eval_iff in H.
  pose proof (mm_fractran_n_strong P) as (P' & regP & HP).
  exists P'. setoid_rewrite H. clear H. split. 1: eapply regP.
  setoid_rewrite FRACTRAN_sss.eval_iff. fold plus.
  intros v. split. 1: intros m; split.
  - fold plus in *. intros (j & v' & H).
    edestruct HP as [[j' Hj'] _].
    + eexists. eapply H.
    + rewrite FRACTRAN_sss.eval_iff in Hj'.
      exists j'. eexists. exists v'. change (@enc (k + n)) with (@exp (k + n)). 
      eexists. eexists. unfold encode_state in Hj'. cbn in *.
      rewrite !PeanoNat.Nat.add_0_r in *.
      admit. admit.
  - intros (j & k' & v' & H1 & H2). 
    admit.
  - admit.
Admitted.