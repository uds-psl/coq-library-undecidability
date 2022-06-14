(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW 
  Require Import utils gcd prime pos vec subcode sss compiler_correction.

From Undecidability.MinskyMachines.MMA
  Require Import mma_defs mma_utils mma_k_mma_2_compiler godel_coding.

Set Default Goal Selector "!".

#[local] Notation "e #> x" := (vec_pos e x).

Section mma3_mma2_compiler.

  Variable n : nat.

  Let simul (v : vec nat (3+n)) (w : vec nat (2+n)) : Prop :=
        w#>pos0 = 0
     /\ w#>pos1 = gc_enc godel_coding_235 (fst (vec_split _ _ v))
     /\ forall x, v#>(pos_right _ x) = w#>(pos_right _ x).

  Theorem mma3_mma2_compiler : compiler_t (@mma_sss _) (@mma_sss _) simul.
  Proof.
    generalize (mma_k_mma_2_compiler godel_coding_235 n).
    apply compiler_t_simul_equiv.
    intros v w.
    generalize (vec_app_split _ _ v) (vec_app_split _ _ w).
    destruct (vec_split _ _ v) as (v1,v2).
    destruct (vec_split _ _ w) as (w1,w2).
    intros <- <-.
    assert (v1 = v1#>pos0##v1#>pos1##v1#>pos2##vec_nil) as E.
    1: apply vec_pos_ext; intros p; repeat invert pos p; auto.
    unfold simul; split; simpl.
    + intros (-> & ->); msplit 2; rew vec; simpl; f_equal; auto.
    + intros (H1 & H2 & H3); split.
      * apply vec_pos_ext; intros p; repeat invert pos p; auto.
        rewrite H2; f_equal; auto.
      * apply vec_pos_ext; intros p.
        generalize (H3 p); rew vec.
  Qed.

End mma3_mma2_compiler.
