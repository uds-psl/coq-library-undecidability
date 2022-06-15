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
  Require Import utils godel_coding pos vec sss compiler_correction.

From Undecidability.MinskyMachines.MMA
  Require Import mma_defs mma_k_mma_2_compiler.

Set Default Goal Selector "!".

#[local] Notation "e #> x" := (vec_pos e x).

Section mma4_mma2_compiler.

  Let simul (v : vec nat 4) (w : vec nat 2) : Prop :=
        w#>pos0 = 0
     /\ w#>pos1 = gc_enc godel_coding_2357 v.

  Theorem mma4_mma2_compiler : compiler_t (@mma_sss _) (@mma_sss _) simul.
  Proof.
    generalize (mma_k_mma_2_compiler godel_coding_2357 0); simpl.
    apply compiler_t_simul_equiv.
    intros v w.
    vec split v with x1; vec split v with x2; vec split v with x3; vec split v with x4; vec nil v; simpl.
    vec split w with y1; vec split w with y2; vec nil w; simpl; split.
    + intros (H1 & _).
      generalize (f_equal (fun v => v#>pos0) H1) (f_equal (fun v => v#>pos1) H1); simpl; intros -> ->; split; auto.
    + intros (H1 & H2); simpl in *; subst; auto.
  Qed.

End mma4_mma2_compiler.
