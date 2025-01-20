(* 
  Reduction from:
    Krivine machine halting for closed terms (KrivineMclosed_HALT)
  to:
    Halting problem for a fixed, universal, single-tape, binary Turing machine (HaltUTM)
*)

From Undecidability Require Import TM.UTM TM.TM LambdaCalculus.Krivine MinskyMachines.MMA
  Shared.Libs.PSL.FiniteTypes.FinTypesDef.

From Undecidability Require 
  MinskyMachines.Reductions.KrivineMclosed_HALT_to_MMA_HALTING
  TM.Reductions.MMA_HALTING_n_to_HaltTM_n
  TM.Reductions.mTM_to_TM
  TM.Reductions.Arbitrary_to_Binary
  Shared.Libs.DLW.Vec.vec
  LambdaCalculus.Util.Krivine_facts.

Module KM_MMA := KrivineMclosed_HALT_to_MMA_HALTING.Argument.
Module MMA_TM := MMA_HALTING_n_to_HaltTM_n.Argument.
Module MTM_TM := mTM_to_TM.
Module TM_BTM := Arbitrary_to_Binary.

From Stdlib Require Import Vector ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

Lemma TM_BTM_iff {sig} {M : TM sig 1} {ts : Vector.t (tape sig) 1} :
  HaltsTM M ts <->
  HaltsTM (TM_BTM.M' M) (cons _ (hd (TM_BTM.ts' ts)) 0 (nil _)).
Proof.
  have -> (A) (v : Vector.t A 1) : cons _ (hd v) 0 (nil _) = v
    by rewrite (vec.vec_head_tail v) (vec.vec_0_nil (vec.vec_tail v)).
  by apply: TM_BTM.HaltTM_Σ_to_HaltTM_bool_correct.
Qed.

Lemma MTM_TM_iff {sig n} {M : TM sig n} {ts : Vector.t (tape sig) n} :
  HaltsTM M ts <->
  HaltsTM (MTM_TM.M' M) (MTM_TM.ts' ts).
Proof. by apply: MTM_TM.MTM_to_stM_correct. Qed.

Lemma MMA_TM_iff {n MM} {cs : Vector.t nat n}  : 
  @MMA_HALTING n (MM, cs) <->
  HaltsTM (MMA_TM.P MM) (MMA_TM.encode_counters cs).
Proof.
  split.
  - by apply: MMA_TM.simulation.
  - by move=> [p'] [ts] /MMA_TM.inverse_simulation.
Qed.

Lemma KM_MMA_iff {tm} : (forall sigma, Lambda.subst sigma tm = tm) ->
  KrivineM_HALT tm <->
  @MMA_HALTING 5 (KM_MMA.PROG 1, KM_MMA.input tm).
Proof.
  move=> /Krivine_facts.eclosed_closed ?. split.
  - by apply: KM_MMA.simulation.
  - by apply: (KM_MMA.inverse_simulation List.nil List.nil).
Qed.

#[local] Opaque TM_BTM.ts' MMA_TM.encode_counters.

Require Import Undecidability.Synthetic.Definitions.

Lemma reduction : KrivineMclosed_HALT ⪯ HaltUTM.
Proof.
  unshelve eexists.
  { intros [tm _].
    assert (cs := KM_MMA.input tm).
    assert (ts := MMA_TM.encode_counters cs).
    assert (t := MTM_TM.ts' ts).
    assert (t' := TM_BTM.ts' t).
    exact (Vector.hd t'). }
  move=> [tm Htm].
  apply: (iff_trans (KM_MMA_iff Htm)).
  apply: (iff_trans MMA_TM_iff).
  apply: (iff_trans MTM_TM_iff).
  by apply: TM_BTM_iff.
Qed.
