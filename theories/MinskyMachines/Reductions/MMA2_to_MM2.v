(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Arith Relations Lia.

Require Import Undecidability.Synthetic.Definitions.

From Undecidability.Shared.Libs.DLW Require Import utils pos vec sss subcode.
From Undecidability.MinskyMachines Require Import MM2 mma_defs.

Set Implicit Arguments.

Tactic Notation "rew" "length" := autorewrite with length_db.

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).

Section MMA2_to_MM2.

  Notation "i '/A/' r '⇢' s" := (@mma_sss 2 i r s) (at level 70, no associativity).
  Notation "P '/A/' r '→' s" := (sss_step (@mma_sss 2) P r s) (at level 70, no associativity).
  Notation "P '/A/' r '↠' s" := (sss_compute (@mma_sss 2) P r s) (at level 70, no associativity).
  Notation "P '/A/' r '~~>' s" := (sss_output (@mma_sss 2) P r s) (at level 70, no associativity).
  Notation "P '/A/' s ↓" := (sss_terminates (@mma_sss 2) P s) (at level 70, no associativity).

  Notation "i '/2/' r '⇢' s" := (mm2_atom i r s) (at level 70, no associativity).
  Notation "P '/2/' r '→' s" := (mm2_step P r s) (at level 70, no associativity).
  Notation "P '/2/' x ↠ y" := (clos_refl_trans _ (mm2_step P) x y) (at level 70, no associativity).
  Notation "P '/2/' s ↓" := (mm2_terminates P s) (at level 70, no associativity).

  Definition mma_mm2_instr : mm_instr (pos 2) -> mm2_instr.
  Proof.
    intros [ [ | p ] | [ | p ] j ].
    + exact mm2_inc_a.
    + exact mm2_inc_b.
    + exact (mm2_dec_a j).
    + exact (mm2_dec_b j).
  Defined.

  Definition mm2_mma_instr : mm2_instr -> mm_instr (pos 2).
  Proof.
    intros [ | | j | j ].
    + exact (INC pos0).
    + exact (INC pos1).
    + exact (DEC pos0 j).
    + exact (DEC pos1 j).
  Defined.

  Local Fact mm2_mma_mm2_instr ρ : mm2_mma_instr (mma_mm2_instr ρ) = ρ.
  Proof. destruct ρ as [ p | p ]; analyse pos p; trivial. Qed.

  Local Fact mma_mm2_mma_instr ρ : mma_mm2_instr (mm2_mma_instr ρ) = ρ.
  Proof. destruct ρ; trivial. Qed.

  Definition mma_mm2_state : mm_state 2 -> nat*(nat*nat).
  Proof.
    intros (i,v).
    exact (i,(vec_pos v pos0,vec_pos v pos1)).
  Defined.

  Let mm2_mma_state : nat*(nat*nat) -> mm_state 2.
  Proof.
    intros (i,(a,b)).
    exact (i,a##b##vec_nil).
  Defined.

  Let mm2_mma_mm2_state s : mm2_mma_state (mma_mm2_state s) = s.
  Proof.
    destruct s as (i,v).
    vec split v with a.
    vec split v with b.
    vec nil v.
    trivial.
  Qed.

  Let mma_mm2_mma_state s : mma_mm2_state (mm2_mma_state s) = s.
  Proof. destruct s as (i,(a,b)); auto. Qed.

  Local Fact mma_mm2_atom ρ s1 s2 : ρ /A/ s1 ⇢ s2 -> mma_mm2_instr ρ /2/ mma_mm2_state s1 ⇢ mma_mm2_state s2.
  Proof.
    induction 1 as [ i x v | i x k v H | i x k v u H ]; analyse pos x; simpl; rew vec; 
      try rewrite H; constructor.
  Qed.

  Local Fact mm2_mma_atom ρ s1 s2 : ρ /2/ s1 ⇢ s2 -> mm2_mma_instr ρ /A/ mm2_mma_state s1 ⇢ mm2_mma_state s2.
  Proof.
    induction 1 as [ i a b | i a b | i j a b | i j a b | i j b | i j a ]; simpl; try constructor; rew vec.
    + set (v := S a ## b ## vec_nil).
      change (a##b##vec_nil) with (v[a/pos0]).
      constructor 3; auto.
    + set (v := a ## S b ## vec_nil).
      change (a##b##vec_nil) with (v[b/pos1]).
      constructor 3; auto.
  Qed.

  Fact mma_mm2_atom_equiv ρ s1 s2 : ρ /A/ s1 ⇢ s2 <-> mma_mm2_instr ρ /2/ mma_mm2_state s1 ⇢ mma_mm2_state s2.
  Proof.
    split.
    + apply mma_mm2_atom.
    + intros H; apply mm2_mma_atom in H.
      rewrite mm2_mma_mm2_instr in H.
      do 2 rewrite mm2_mma_mm2_state in H.
      trivial.
  Qed.

  Local Fact mma_mm2_step P s1 s2 : (1,P) /A/ s1 → s2 -> map mma_mm2_instr P /2/ mma_mm2_state s1 → mma_mm2_state s2.
  Proof.
    intros (i & l & ρ & r & v & H1 & H2 & H3).
    subst s1; revert H3.
    vec split v with a.
    vec split v with b.
    vec nil v.
    intros H3.
    exists (mma_mm2_instr ρ); split.
    2: apply mma_mm2_atom_equiv; auto.
    simpl.
    inversion H1.
    exists (map mma_mm2_instr l), (map mma_mm2_instr r); split.
    * rewrite map_app; auto.
    * rew length; auto.
  Qed.

  Local Fact mm2_mma_step P s1 s2 : P /2/ s1 → s2 -> (1, map mm2_mma_instr P) /A/ mm2_mma_state s1 → mm2_mma_state s2.
  Proof.
    intros (ρ & (l & r & H1 & H2) & H3).
    destruct s1 as (i & a & b).
    exists 1, (map mm2_mma_instr l), (mm2_mma_instr ρ), (map mm2_mma_instr r), (a##b##vec_nil); msplit 2.
    + subst P; rewrite map_app; auto.
    + simpl in H2; subst; rew length; auto.
    + apply mm2_mma_atom; auto.
  Qed.

  Fact mma_mm2_step_equiv P s1 s2 : (1,P) /A/ s1 → s2 <-> map mma_mm2_instr P /2/ mma_mm2_state s1 → mma_mm2_state s2.
  Proof.
    split.
    + apply mma_mm2_step.
    + intros H; apply mm2_mma_step in H.
      rewrite map_map in H.
      do 2 rewrite mm2_mma_mm2_state in H.
      eq goal H; do 2 f_equal.
      rewrite <- (map_id P) at 2.
      apply map_ext, mm2_mma_mm2_instr.
  Qed.

  Local Fact mma_mm2_compute P s1 s2 : (1,P) /A/ s1 ↠ s2 -> map mma_mm2_instr P /2/ mma_mm2_state s1 ↠ mma_mm2_state s2.
  Proof.
    intros (k & Hk); revert Hk.
    induction 1 as [ | k s1 s2 s3 H1 H2 IH2 ].
    * constructor 2.
    * constructor 3 with (2 := IH2).
      constructor 1.
      apply mma_mm2_step_equiv; auto.
  Qed.

  Local Fact mm2_mma_compute P s1 s2 : P /2/ s1 ↠ s2 -> (1, map mm2_mma_instr P) /A/ mm2_mma_state s1 ↠ mm2_mma_state s2.
  Proof.
    induction 1 as [ s1 s2 | s | s1 s2 s3 H1 (k1 & IH1) H2 (k2 & IH2) ].
    + exists 1.
      apply sss_steps_1, mm2_mma_step; auto.
    + exists 0; constructor.
    + exists (k1+k2); apply sss_steps_trans with (1 := IH1) (2 := IH2).
  Qed.

  Local Fact mma_mm2_compute_equiv P s1 s2 : (1,P) /A/ s1 ↠ s2 
                                         <-> map mma_mm2_instr P /2/ mma_mm2_state s1 ↠ mma_mm2_state s2.
  Proof.
    split.
    + apply mma_mm2_compute.
    + intros H.
      apply mm2_mma_compute in H.
      rewrite map_map in H.
      do 2 rewrite mm2_mma_mm2_state in H.
      eq goal H; do 2 f_equal.
      rewrite <- (map_id P) at 2.
      apply map_ext, mm2_mma_mm2_instr.
  Qed.

  Local Fact mma_mm2_terminates_zero_equiv P s : (1,P) /A/ s ↠ (0,vec_zero) 
                                         <-> map mma_mm2_instr P /2/ mma_mm2_state s ↠ (0,(0,0)).
  Proof. apply mma_mm2_compute_equiv. Qed.

  Fact mma_mm2_terminates P s : (1,P) /A/ s ↓ -> map mma_mm2_instr P /2/ mma_mm2_state s ↓.
  Proof.
    intros (y & H1 & H2).
    exists (mma_mm2_state y); split.
    + apply mma_mm2_compute_equiv; auto.
    + intros z H.
      rewrite <- (mma_mm2_mma_state z) in H.
      rewrite <- mma_mm2_step_equiv in H.
      revert H.
      apply sss_out_step_stall with (1 := H2).
  Qed.

  Fact mm2_mma_terminates P s : P /2/ s ↓ -> (1,map mm2_mma_instr P) /A/ mm2_mma_state s ↓.
  Proof.
    intros (y & H1 & H2).
    exists (mm2_mma_state y); split.
    + apply mm2_mma_compute; auto.
    + destruct y as (i,(a,b)); simpl fst.
      red in H2.
      destruct (in_out_code_dec i (1, map mm2_mma_instr P)) as [ H3 | ] ; auto.
      destruct in_code_subcode with (1 := H3) as (rho & H4); exfalso; revert H4.
      rewrite <- (mm2_mma_mm2_instr rho).
      generalize (mma_mm2_instr rho); clear rho; intros rho.
      intros H4.
      destruct (mma_sss_total (mm2_mma_instr rho) (i,a##b##vec_nil))
        as (w & Hw).
      apply mma_mm2_atom in Hw.
      apply (H2 (mma_mm2_state w)).
      rewrite mma_mm2_mma_instr in Hw.
      exists rho; split; auto; simpl.
      destruct H4 as (l & r & H4 & H5).
      exists (map mma_mm2_instr l), (map mma_mm2_instr r); split; rew length; try lia.
      apply f_equal with (f := map mma_mm2_instr) in H4.
      rewrite map_map, map_app in H4; simpl in H4.
      rewrite mma_mm2_mma_instr in H4.
      rewrite <- H4, <- (map_id P) at 1.
      apply map_ext; intros; rewrite mma_mm2_mma_instr; auto.
  Qed.

  Theorem mma_mma2_reduction P s : (1,P) /A/ s ↓ <-> map mma_mm2_instr P /2/ mma_mm2_state s ↓.
  Proof.
    split.
    + apply mma_mm2_terminates.
    + intros H.
      apply mm2_mma_terminates in H.
      rewrite map_map, mm2_mma_mm2_state in H.
      eq goal H; do 2 f_equal.
      rewrite <- (map_id P) at 2.
      apply map_ext, mm2_mma_mm2_instr.
  Qed.

  Theorem mma_mma2_zero_reduction P s : (1,P) /A/ s ~~> (0,vec_zero) <-> map mma_mm2_instr P /2/ mma_mm2_state s ↠ (0,(0,0)).
  Proof.
    rewrite <- mma_mm2_terminates_zero_equiv; split.
    + intros []; auto.
    + intros H; split; auto; simpl; lia.
  Qed.

End MMA2_to_MM2.

Section MMA2_MM2.

  Let f : MMA2_PROBLEM -> MM2_PROBLEM.
  Proof.
    intros (P & v).
    exact (map mma_mm2_instr P, vec_pos v pos0, vec_pos v pos1).
  Defined.

  Theorem MMA2_MM2_HALTING : MMA2_HALTING ⪯ MM2_HALTING.
  Proof.
    exists f. 
    intros (P & v); simpl; unfold MMA2_HALTING.
    apply mma_mma2_reduction.
  Qed.

  Theorem MMA2_MM2_HALTS_ON_ZERO : MMA2_HALTS_ON_ZERO ⪯ MM2_HALTS_ON_ZERO.
  Proof.
    exists f. 
    intros (P & v); simpl; unfold MMA2_HALTS_ON_ZERO.
    apply mma_mma2_zero_reduction.
  Qed.

End MMA2_MM2.
