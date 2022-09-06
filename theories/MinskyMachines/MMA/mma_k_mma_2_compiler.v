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
  Require Import utils godel_coding pos vec subcode sss compiler_correction.

From Undecidability.MinskyMachines.MMA
  Require Import mma_defs mma_utils.

Set Implicit Arguments.
Set Default Goal Selector "!".

#[local] Notation "e #> x" := (vec_pos e x).
#[local] Notation "e [ v / x ]" := (vec_change e x v).

Section mma_k_mma_2_compiler.

  Variable (k : nat) (gc : godel_coding k) (n : nat).

  (* s and r are the first two registers in pos (2+n) *)

  Notation s := (pos0 : pos (2+n)).  (* spare register *)
  Notation r := (pos1 : pos (2+n)).  (* register storing ⦉a,b,c⦊ *)

  Let simul (v : vec nat (k+n)) (w : vec nat (2+n)) : Prop :=
        let (v1,v2) := vec_split _ _ v in 
        let (w1,w2) := vec_split _ _ w in 
        w1 = 0##(gc_enc gc v1)##vec_nil /\ w2 = v2.

  Infix "⋈" := simul (at level 70, no associativity).

  Notation "⟨ x ⟩" := (gc_pr gc x) (at level 1, format "⟨ x ⟩").

  Local Fact pr_not_zero x : 0 < ⟨x⟩.
  Proof. apply gc_pr_nz. Qed.

  Hint Resolve pr_not_zero : core.

  Section the_instruction_compiler.

    (* The length of compiled code does not depend on the linker *)

    Local Definition ilen : mm_instr (pos (k+n)) -> nat.
    Proof using gc.
      intros [ x | x j ]; apply pos_both in x as [ x | x ].
      + exact (8+⟨x⟩).
      + exact 1.
      + exact (16+7*⟨x⟩).
      + exact 1.
    Defined.

    (* The instruction compiler is parameterized by a linker *)

    Variable lnk : nat -> nat.

    Local Definition icomp : nat -> mm_instr (pos (k+n)) -> list (mm_instr (pos (2+n))).
    Proof using gc lnk.
      intros i [ x | x j ].
      + apply pos_both in x as [ x | x ].
        * exact (mma_mult_cst_with_zero r s ⟨x⟩ (lnk i)).
        * exact (INCₐ (pos_nxt (pos_nxt x)) :: nil).
      + apply pos_both in x as [ x | x ].
        * exact (mma_div_branch r s ⟨x⟩ (lnk i) (lnk j)).
        * exact (DECₐ (pos_nxt (pos_nxt x)) (lnk j) :: nil).
    Defined.

    Local Fact icomp_length_eq i ρ : length (icomp i ρ) = ilen ρ.
    Proof.
      unfold icomp, ilen.
      destruct ρ as [ x | x j ]; destruct (pos_both _ _ x); auto.
      + now rewrite mma_mult_cst_with_zero_length.
      + now rewrite mma_div_branch_length.
    Qed.

    Local Fact icomp_eq_1 i (x : pos k) : 
           icomp i (INCₐ (pos_left _ x)) = mma_mult_cst_with_zero r s ⟨x⟩ (lnk i).
    Proof. unfold icomp; now rewrite pos_both_left. Qed.

    Local Fact icomp_eq_2 i (x : pos n) : 
           icomp i (INCₐ (pos_right _ x)) = INCₐ (pos_nxt (pos_nxt x)) :: nil.
    Proof. unfold icomp; now rewrite pos_both_right. Qed.

    Local Fact icomp_eq_3 i (x : pos k) j : 
           icomp i (DECₐ (pos_left _ x) j) = mma_div_branch r s ⟨x⟩ (lnk i) (lnk j).
    Proof. unfold icomp; now rewrite pos_both_left. Qed.

    Local Fact icomp_eq_4 i (x : pos n) j : 
           icomp i (DECₐ (pos_right _ x) j) = DECₐ (pos_nxt (pos_nxt x)) (lnk j) :: nil.
    Proof. unfold icomp; now rewrite pos_both_right. Qed.

  End the_instruction_compiler.

  Hint Resolve subcode_refl : core.

  (* The critical lemma is the soundness of the instruction compiler: 
       every source instruction is simulated by its compiled image 
       (at list of target instructions) in at least one step of 
       computation *)

  Local Lemma icomp_sound : 
         instruction_compiler_sound icomp (@mma_sss (k+n)) (@mma_sss (2+n)) simul.
  Proof.
    intros lnk [ x | x j ] i1 v1 i2 v2 w1 H.
    + apply mma_sss_INC_inv in H as (-> & ->).
      revert w1 i1 v1. 
      pattern x; revert x; apply pos_left_right_rect; intros x w1 i v.
      * rewrite icomp_eq_1, mma_mult_cst_with_zero_length.
        intros H1 (H2 & H3).
        exists (w1[(⟨x⟩*(w1#>r))/r]); msplit 2; rew vec.
        - apply mma_mult_cst_with_zero_progress; try easy.
          2: f_equal; auto.
          apply f_equal with (f := fun v => v#>pos0) in H2; revert H2; rew vec.
        - apply vec_pos_ext; intros p; repeat invert pos p; rew vec.
          ++ apply f_equal with (f := fun v => v#>pos0) in H2; revert H2; rew vec.
          ++ apply f_equal with (f := fun v => v#>pos1) in H2; revert H2; rew vec; simpl; intros ->.
             rewrite gc_succ; f_equal.
             apply vec_pos_ext; intros p; rewrite !vec_pos_set.
             destruct (pos_eq_dec p x) as [ -> | D ]; rew vec; rewrite !vec_pos_set.
             rewrite vec_change_neq; auto.
             now contradict D; apply pos_left_inj in D.
        - apply vec_pos_ext; intros p; rew vec.
          rewrite vec_change_neq.
          2: apply pos_left_right_neq.
          generalize (f_equal (fun v => v#>p) H3); rew vec.
      * rewrite icomp_eq_2; simpl.
        intros H1 (H2 & H3).
        exists (w1[(S (w1#>(pos_right 2 x)))/pos_right 2 x]); msplit 2.
        - mma sss INC with (pos_right 2 x); simpl pos_right.
          mma sss stop.
          now f_equal; rewrite H1.
        - apply vec_pos_ext; intros p; repeat invert pos p; rew vec.
          ++ generalize (f_equal (fun v => v#>pos0) H2); rew vec.
          ++ generalize (f_equal (fun v => v#>pos1) H2); rew vec; simpl.
             intros ->; f_equal.
             apply vec_pos_ext; intros p; rew vec.
             rewrite vec_change_neq; auto. 
             intros E; symmetry in E; revert E.
             apply pos_left_right_neq.
        - apply vec_pos_ext; intros p; rew vec; rewrite vec_pos_set.
          destruct (pos_eq_dec x p) as [ -> | D ]; rew vec.
          ++ f_equal; generalize (f_equal (fun v => v#>p) H3); rew vec.
          ++ rewrite !vec_change_neq.
             2,3: now contradict D; apply pos_right_inj in D.
             generalize (f_equal (fun v => v#>p) H3); rew vec.
    + case_eq (v1#>x).
      * intros Hv1.
        apply mma_sss_DEC0_inv in H as (-> & ->); auto.
        revert v1 w1 Hv1.
        pattern x; revert x; apply pos_left_right_rect; intros x v1 w1 Hv1.
        - rewrite icomp_eq_3, mma_div_branch_length. 
          intros H1 H2.
          exists w1; split; auto.
          destruct H2 as (H2 & H3).
          apply mma_div_branch_1_progress; try easy.
          ++ generalize (f_equal (fun v => v#>pos0) H2); rew vec.
          ++ generalize (f_equal (fun v => v#>pos1) H2); rew vec; simpl.
             intros ->; apply gc_not_div; rew vec.
          ++ f_equal; auto.
        - rewrite icomp_eq_4; simpl.
          intros H1 H2.
          exists w1; split; auto.
          rewrite H1.
          destruct H2 as (H2 & H3).
          mma sss DEC zero with (pos_right 2 x) (lnk j).
          ++ now generalize (f_equal (fun v => v#>x) H3); rew vec; intros ->.
          ++ mma sss stop.
      * intros a Ha.
        apply mma_sss_DEC1_inv with (u := a) in H; auto.
        destruct H as (-> & ->).
        revert v1 w1 a Ha.
        pattern x; revert x; apply pos_left_right_rect; intros x v1 w1 a Ha.
        - rewrite icomp_eq_3, mma_div_branch_length.
          intros H1 (H2 & H3).
          set (v' := let (v,_) := vec_split _ _ v1 in v); simpl in v'.
          exists (w1[(gc_enc gc (v'[a/x]))/pos1]); msplit 2; rew vec.
          ++ apply mma_div_branch_0_progress with (gc_enc gc (v'[a/x])); try easy.
             ** generalize (f_equal (fun v => v#>pos0) H2); rew vec.
             ** generalize (f_equal (fun v => v#>pos1) H2); rew vec; simpl; intros ->. 
                rewrite Nat.mul_comm, gc_succ; f_equal; rew vec.
                unfold v'; rewrite <- Ha.
                apply vec_pos_ext; intros p; rewrite !vec_pos_set.
                destruct (pos_eq_dec p x) as [ -> | D ]; rew vec.
          ++ apply vec_pos_ext; intros p; repeat invert pos p; simpl; rew vec.
             ** generalize (f_equal (fun v => v#>pos0) H2); rew vec.
             ** f_equal; unfold v'.
                apply vec_pos_ext; intros p; rew vec; rewrite !vec_pos_set.
                destruct (pos_eq_dec p x) as [ -> | D ]; rew vec; rewrite vec_pos_set.
                rewrite vec_change_neq; auto.
                now contradict D; apply pos_left_inj in D.
          ++ apply vec_pos_ext; intros p; rew vec.
             generalize (f_equal (fun v => v#> p) H3); rew vec; rewrite ! vec_pos_set.
             simpl; intros ->; rewrite vec_change_neq; auto.
             apply pos_left_right_neq.
        - rewrite icomp_eq_4; simpl.
          intros H1 (H2 & H3).
          exists (w1[a/pos_right 2 x]); msplit 2; simpl pos_right; rew vec.
          ++ mma sss DEC S with (pos_right 2 x) (lnk j) a.
             ** now generalize (f_equal (fun v => v#>x) H3); rew vec; intros ->.
             ** mma sss stop.
          ++ apply vec_pos_ext; intros p; repeat invert pos p; rew vec.
             ** generalize (f_equal (fun v => v#>pos0) H2); rew vec.
             ** generalize (f_equal (fun v => v#>pos1) H2); rew vec; simpl; intros ->.
                f_equal; apply vec_pos_ext; intros p; rew vec.
                rewrite vec_change_neq; auto.
                intros E; symmetry in E; revert E; apply pos_left_right_neq.
          ++ apply vec_pos_ext; intros p; rewrite !vec_pos_set.
             destruct (pos_eq_dec x p) as [ -> | D ]; rew vec.
             rewrite !vec_change_neq; auto.
             2,3: contradict D.
             2: now apply pos_right_inj in D.
             2: now repeat apply pos_nxt_inj in D.
             generalize (f_equal (fun v => v#>p) H3);rew vec.
  Qed.

  (* From the soundness of the (individual) instruction compiler, using our 
     generic compiler we immediately obtain a linker/compiler for programs 
     of source instructions into programs of target instructions *)

  Theorem mma_k_mma_2_compiler : compiler_t (@mma_sss (k+n)) (@mma_sss (2+n)) simul.
  Proof.
    apply generic_compiler with icomp ilen.
    + intros; now rewrite icomp_length_eq.  (* ilen computes length icomp *) 
    + apply mma_sss_total_ni.               (* source semantics is total *)
    + apply mma_sss_fun.                    (* target semantics is functional *)
    + apply icomp_sound.                    (* compiled individual instructions is sound *)
  Qed.

End mma_k_mma_2_compiler.

Arguments mma_k_mma_2_compiler {_}.
