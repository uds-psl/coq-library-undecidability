Require Import Undecidability.MinskyMachines.MM Undecidability.MinskyMachines.Util.MM_sss Undecidability.MinskyMachines.MM.mm_defs.

From Coq Require Import List Vector.
Import ListNotations Vector.VectorNotations.

Definition MM_computable {k} (R : Vector.t nat k -> nat -> Prop) := 
  exists n : nat, exists P : list (mm_instr (Fin.t (1 + k + n))),
    forall v : Vector.t nat k,
      (forall m, R v m <->
         exists c v', @MM.eval (1 + k + n) (1, P) (1, (0 :: v) ++ Vector.const 0 n) (c, m :: v')).

Lemma MM_computable_iff {k} (R : Vector.t nat k -> nat -> Prop) :
  (exists n : nat, exists P : list (mm_instr (Fin.t (1 + k + n))),
      (forall v m, R v m -> exists c v', @MM.eval (1 + k + n) (1, P) (1, (0 :: v) ++ Vector.const 0 n) (c, m :: v')) /\
      (forall v, sss.sss_terminates (@mm_sss _) (1, P) (1, (0 :: v) ++ Vector.const 0 n) -> exists m, R v m))
      -> MM_computable R.
Proof.
  intros (n & P & H1 & H2).
  exists n, P. intros v m. split.
  - intros H % H1. eauto.
  - intros (c & v' & H).
    pose proof (H' := H).
    edestruct H2 as [m' Hm'].
    1:{ eexists. eapply eval_iff. eauto. }
    enough (m' = m) as -> by eauto.
    eapply H1 in Hm' as (c' & v'' & H''). fold plus in *.
    eapply eval_iff in H', H''.
    destruct H' as [H1' H2']. destruct H'' as [H1'' H2''].
    eapply sss.sss_compute_fun in H1'; eauto. congruence.
    eapply mm_sss_fun.
Qed.