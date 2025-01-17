Require Import Undecidability.MinskyMachines.MMA.
Require Import Undecidability.MinskyMachines.MMA.mma_defs.
From Undecidability.Shared.Libs.DLW Require Import Code.sss.

From Stdlib Require Import Vector.
Import Vector.VectorNotations.

From Stdlib Require Import ssreflect.

#[local] Notation "P // s ~~> t" := (sss_output (@mma_sss _) P s t).

Lemma MMA_computable_iff {k} (R : Vector.t nat k -> nat -> Prop) :
  MMA_computable R <->
  (exists n : nat, exists P : list (mm_instr (Fin.t (S (k + n)))),
    (forall v m, R v m -> exists c v', (1, P) // (1, Vector.append (0 :: v) (Vector.const 0 n)) ~~> (c, m :: v')) /\
    (forall v, sss.sss_terminates (@mma_sss _) (1, P) (1, Vector.append (0 :: v) (Vector.const 0 n)) -> exists m, R v m)).
Proof.
  split.
  - move=> [n] [P] HP. exists n, P. split.
    + by move=> ?? /HP.
    + move=> v [[c' v']]. rewrite (Vector.eta v') => H'P.
      exists (Vector.hd v'). apply /HP. do 2 eexists. eassumption.
  - move=> [n] [P] [H1P H2P]. exists n, P. split.
    + apply: H1P.
    + move=> [c] [v'] Hm.
      have /H2P [m' Hm'] : sss_terminates (mma_sss (n:=S (k + n))) (1, P) (1, Vector.append (0 :: v) (Vector.const 0 n)).
      { eexists. eassumption. }
      suff : m' = m by move=> <-.
      move: Hm' Hm => /H1P [?] [?] /(sss_output_fun (@mma_sss_fun _)) /[apply].
      by move=> /pair_equal_spec [_] /Vector.cons_inj [].
Qed.
