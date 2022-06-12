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

From Undecidability.FRACTRAN
  Require Import prime_seq.

From Undecidability.MinskyMachines.MMA
  Require Import mma_defs mma_utils.

Definition combi_235 a b c := 2^a*(3^b*5^c).

#[local] Notation "⦉ x , y , z ⦊ " := (combi_235 x y z) (at level 1, format "⦉ x , y , z ⦊ ").

Section combi_235.

  (* We use prime_bool_spec which is a crude Boolean primility test *)

  Local Fact prime_2 : prime 2.   Proof. apply prime_bool_spec; trivial. Qed.
  Local Fact prime_3 : prime 3.   Proof. apply prime_bool_spec; trivial. Qed.
  Local Fact prime_5 : prime 5.   Proof. apply prime_bool_spec; trivial. Qed.

  Hint Resolve prime_2 prime_3 prime_5 : core.

  Ltac does_not_divide_1 := 
    intros H;
    apply divides_pow in H; auto;
    now apply prime_divides in H; auto.

  Local Fact not_divides_2_3 x : ~ divides 2 (3^x).   Proof. does_not_divide_1. Qed.
  Local Fact not_divides_2_5 x : ~ divides 2 (5^x).   Proof. does_not_divide_1. Qed.
  Local Fact not_divides_3_2 x : ~ divides 3 (2^x).   Proof. does_not_divide_1. Qed.
  Local Fact not_divides_3_5 x : ~ divides 3 (5^x).   Proof. does_not_divide_1. Qed.
  Local Fact not_divides_5_2 x : ~ divides 5 (2^x).   Proof. does_not_divide_1. Qed.
  Local Fact not_divides_5_3 x : ~ divides 5 (3^x).   Proof. does_not_divide_1. Qed.

  Hint Resolve not_divides_2_3 not_divides_2_5 
               not_divides_3_2 not_divides_3_5  
               not_divides_5_2 not_divides_5_3 : core.

  Local Fact not_divides_5_1 : ~ divides 5 1.
  Proof. apply not_divides_5_3 with (x := 0). Qed.

  Ltac does_not_divide_2 :=
    intros H;
    apply prime_div_mult in H as [ H | H ]; auto;
    match type of H with ?t => revert H; change (~ t) end; auto.

  Local Fact not_divides_2_35 x y : ~ divides 2 (3^x*5^y).   Proof. does_not_divide_2. Qed.
  Local Fact not_divides_3_25 x y : ~ divides 3 (2^x*5^y).   Proof. does_not_divide_2. Qed.
  Local Fact not_divides_5_23 x y : ~ divides 5 (2^x*3^y).   Proof. does_not_divide_2. Qed.

  Hint Resolve not_divides_2_35 not_divides_3_5 not_divides_5_1 : core.

  Ltac combi_235_x_0 := unfold combi_235; rewrite Nat.pow_0_r; ring.

  Local Fact combi_235_2_0 b c : ⦉0,b,c⦊ = 3^b*5^c.   Proof. combi_235_x_0. Qed.
  Local Fact combi_235_3_0 a c : ⦉a,0,c⦊ = 2^a*5^c.   Proof. combi_235_x_0. Qed.
  Local Fact combi_235_5_0 a b : ⦉a,b,0⦊ = 2^a*3^b.   Proof. combi_235_x_0. Qed.

  Ltac combi_235_multx := unfold combi_235; rewrite Nat.pow_succ_r'; ring.

  Local Fact combi_235_mult2 a b c : 2*⦉a,b,c⦊ = ⦉S a,b,c⦊ .   Proof. combi_235_multx. Qed.
  Local Fact combi_235_mult3 a b c : 3*⦉a,b,c⦊ = ⦉a,S b,c⦊ .   Proof. combi_235_multx. Qed.
  Local Fact combi_235_mult5 a b c : 5*⦉a,b,c⦊ = ⦉a,b,S c⦊ .   Proof. combi_235_multx. Qed.

  Local Fact divides_left x k : divides x (x*k).
  Proof. apply divides_mult_r, divides_refl. Qed.

  Hint Resolve divides_left : core.

  Fact combi_235_div2 a b c : divides 2 ⦉a,b,c⦊  <-> a <> 0.
  Proof.
    destruct a; auto.
    + split; try tauto; intros H; exfalso; revert H.
      rewrite combi_235_2_0; apply not_divides_2_35.
    + split; try easy; intros _.
      now rewrite <- combi_235_mult2.
  Qed.

  Fact combi_235_div3 a b c : divides 3 ⦉a,b,c⦊  <-> b <> 0.
  Proof.
    destruct b; auto.
    + split; try tauto; intros H; exfalso; revert H.
      rewrite combi_235_3_0; apply not_divides_3_25.
    + split; try easy; intros _.
      now rewrite <- combi_235_mult3.
  Qed.

  Fact combi_235_div5 a b c : divides 5 ⦉a,b,c⦊  <-> c <> 0.
  Proof.
    destruct c; auto.
    + split; try tauto; intros H; exfalso; revert H.
      rewrite combi_235_5_0; apply not_divides_5_23.
    + split; try easy; intros _.
      now rewrite <- combi_235_mult5.
  Qed.

End combi_235.

Section mma3_mma2_compiler.

  Notation "e #> x" := (vec_pos e x).
  Notation "e [ v / x ]" := (vec_change e x v).

  Variable n : nat.

  (* a, b and c represents the indices of the first 3 registers
       either in pos 3 or pos (3+n) *)

  Notation a := pos0.
  Notation b := pos1.
  Notation c := pos2.

  (* s and r are the first two registers in pos (2+n) *)

  Notation s := (pos0 : pos (2+n)).  (* spare register *)
  Notation r := (pos1 : pos (2+n)).  (* register storing ⦉a,b,c⦊ *)

  Let simul (v : vec nat (3+n)) (w : vec nat (2+n)) : Prop :=
        w#>s = 0
     /\ w#>r = ⦉v#>a,v#>b,v#>c⦊
     /\ forall x, v#>(pos_right _ x) = w#>(pos_right _ x).

  Infix "⋈" := simul (at level 70, no associativity).

  Inductive pos3_id : pos 3 -> Type :=
    | pos3_pos0 : pos3_id pos0
    | pos3_pos1 : pos3_id pos1
    | pos3_pos2 : pos3_id pos2.

  (* This allows case analysis for p : pos 3 *)

  Local Fact pos3_split p : pos3_id p.
  Proof.
    repeat (invert pos p; [ constructor | ]).
    invert pos p.
  Defined.

  Local Definition pos3_235 : pos 3 -> nat.
  Proof.
    intros x; destruct (pos3_split x).
    + exact 2.
    + exact 3.
    + exact 5.
  Defined.

  Notation "⟨ x ⟩" := (pos3_235 x) (at level 1, format "⟨ x ⟩").

  Local Fact pos3_235_pos0 : ⟨a⟩ = 2. Proof. reflexivity. Qed.
  Local Fact pos3_235_pos1 : ⟨b⟩ = 3. Proof. reflexivity. Qed.
  Local Fact pos3_235_pos2 : ⟨c⟩ = 5. Proof. reflexivity. Qed.

  Local Fact pos3_235_gt_0 x : 0 < ⟨x⟩.
  Proof. destruct (pos3_split x); cbn; lia. Qed.

  Hint Resolve pos3_235_gt_0 : core.

  Section the_instruction_compiler.

    (* The length of compiled code does not depend on the linker *)

    Local Definition ilen : mm_instr (pos (3+n)) -> nat.
    Proof.
      intros [ x | x j ]; apply pos_both in x as [ x | x ].
      + exact (8+⟨x⟩).
      + exact 1.
      + exact (16+7*⟨x⟩).
      + exact 1.
    Defined.

    (* The instruction compiler is parameterized by a linker *)

    Variable lnk : nat -> nat.

    Local Definition icomp : nat -> mm_instr (pos (3+n)) -> list (mm_instr (pos (2+n))).
    Proof using lnk.
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

    Local Fact icomp_eq_1 i (x : pos 3) : 
           icomp i (INCₐ (pos_left _ x)) = mma_mult_cst_with_zero r s ⟨x⟩ (lnk i).
    Proof. unfold icomp; now rewrite pos_both_left. Qed.

    Local Fact icomp_eq_2 i (x : pos n) : 
           icomp i (INCₐ (pos_right _ x)) = INCₐ (pos_nxt (pos_nxt x)) :: nil.
    Proof. unfold icomp; now rewrite pos_both_right. Qed.

    Local Fact icomp_eq_3 i (x : pos 3) j : 
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
         instruction_compiler_sound icomp (@mma_sss (3+n)) (@mma_sss (2+n)) simul.
  Proof.
    intros lnk [ x | x j ] i1 v1 i2 v2 w1 H.
    + apply mma_sss_INC_inv in H as (-> & ->).
      revert w1 i1 v1. 
      pattern x; revert x; apply pos_left_right_rect; intros x w1 i v.
      * rewrite icomp_eq_1, mma_mult_cst_with_zero_length.
        intros H1 (H2 & H3 & H4).
        exists (w1[(⟨x⟩*(w1#>r))/r]); msplit 3; rew vec.
        - apply mma_mult_cst_with_zero_progress; try easy.
          f_equal; auto.
        - rewrite H3.
          destruct (pos3_split x); simpl pos_left; rew vec.
          ++ now rewrite pos3_235_pos0, combi_235_mult2.
          ++ now rewrite pos3_235_pos1, combi_235_mult3.
          ++ now rewrite pos3_235_pos2, combi_235_mult5.
        - intros p. 
          rewrite vec_change_neq.
          2: apply (@pos_left_right_neq 3).
          rewrite vec_change_neq; auto.
          change b with (@pos_left 2 n b).
          apply pos_left_right_neq.
      * rewrite icomp_eq_2; simpl.
        intros H1 (H2 & H3 & H4).
        exists (w1[(S (w1#>(pos_right 2 x)))/pos_right 2 x]); msplit 3.
        - mma sss INC with (pos_right 2 x); simpl pos_right.
          mma sss stop.
          now f_equal; rewrite H1.
        - rewrite vec_change_neq; auto.
          change a with (@pos_left 2 n a).
          intros E; symmetry in E; revert E.
          apply pos_left_right_neq.
        - rewrite vec_change_neq.
          ++ rewrite H3; f_equal; rew vec.
          ++ change b with (@pos_left 2 n b).
             intros E; symmetry in E; revert E.
             apply pos_left_right_neq.
        - intros p. 
          rewrite <- !H4.
          destruct (pos_eq_dec p x) as [ -> | H5 ]; rew vec.
          ++ simpl pos_right; rew vec.
          ++ rewrite !vec_change_neq; auto.
             ** contradict H5; symmetry; revert H5; apply pos_right_inj with (n := 2).
             ** contradict H5; symmetry; revert H5; apply pos_right_inj with (n := 3).
    + case_eq (v1#>x).
      * intros Hv1.
        apply mma_sss_DEC0_inv in H as (-> & ->); auto.
        revert v1 w1 Hv1.
        pattern x; revert x; apply pos_left_right_rect; intros x v1 w1 Hv1.
        - rewrite icomp_eq_3, mma_div_branch_length. 
          intros H1 H2.
          exists w1; split; auto.
          destruct H2 as (H2 & H3 & H4).
          apply mma_div_branch_1_progress; try easy.
          ++ rewrite H3.
             destruct (pos3_split x); cbn in Hv1 |- *; rewrite Hv1.
             ** now rewrite combi_235_div2.
             ** now rewrite combi_235_div3.
             ** now rewrite combi_235_div5.
          ++ f_equal; auto.
        - rewrite icomp_eq_4; simpl.
          intros H1 H2.
          exists w1; split; auto.
          rewrite H1.
          destruct H2 as (H2 & H3 & H4).
          mma sss DEC zero with (pos_right 2 x) (lnk j).
          ++ now rewrite <- H4, Hv1.
          ++ mma sss stop.
      * intros k Hk.
        apply mma_sss_DEC1_inv with (u := k) in H; auto.
        destruct H as (-> & ->).
        revert v1 w1 k Hk.
        pattern x; revert x; apply pos_left_right_rect; intros x v1 w1 k Hk.
        - rewrite icomp_eq_3, mma_div_branch_length.
          intros H1 (H2 & H3 & H4).
          destruct (pos3_split x); simpl pos_left in *.
          ++ exists (w1[(⦉k,v1#>pos1,v1#>pos2⦊)/pos1]); msplit 3; rew vec.
             ** apply mma_div_branch_0_progress with ⦉k,v1#>pos1,v1#>pos2⦊; try easy.
                rewrite mult_comm, pos3_235_pos0, combi_235_mult2, H3, Hk; auto.
             ** intros x; specialize (H4 x); simpl pos_right in *; rew vec.
          ++ exists (w1[(⦉v1#>pos0,k,v1#>pos2⦊)/pos1]); msplit 3; rew vec.
             ** apply mma_div_branch_0_progress with ⦉v1#>pos0,k,v1#>pos2⦊; try easy.
                rewrite mult_comm, pos3_235_pos1, combi_235_mult3, H3, Hk; auto.
             ** intros x; specialize (H4 x); simpl pos_right in *; rew vec.
          ++ exists (w1[(⦉v1#>pos0,v1#>pos1,k⦊)/pos1]); msplit 3; rew vec.
             ** apply mma_div_branch_0_progress with ⦉v1#>pos0,v1#>pos1,k⦊; try easy.
                rewrite mult_comm, pos3_235_pos2, combi_235_mult5, H3, Hk; auto.
             ** intros x; specialize (H4 x); simpl pos_right in *; rew vec.
        - rewrite icomp_eq_4; simpl.
          intros H1 (H2 & H3 & H4).
          exists (w1[k/pos_right 2 x]); msplit 3; simpl pos_right; rew vec.
          ++ mma sss DEC S with (pos_nxt (pos_nxt x)) (lnk j) k.
             ** specialize (H4 x); simpl pos_right in *.
                rewrite <- Hk, H4; auto.
             ** mma sss stop.
          ++ intros p.
             specialize (H4 p); cbn in H4.
             destruct (pos_eq_dec p x) as [ -> | H5 ]; rew vec.
             rewrite !vec_change_neq; auto.
             all: contradict H5; now repeat apply pos_nxt_inj in H5.
  Qed.

  (* From the soundness of the (individual) instruction compiler, using our 
     generic compiler we immediately obtain a linker/compiler for programs 
     of source instructions into programs of target instructions *)

  Theorem mma3_mma2_compiler : compiler_t (@mma_sss _) (@mma_sss _) simul.
  Proof.
    apply generic_compiler with icomp ilen.
    + intros; now rewrite icomp_length_eq.  (* ilen computes length icomp *) 
    + apply mma_sss_total_ni.               (* source semantics is total *)
    + apply mma_sss_fun.                    (* target semantics is functional *)
    + apply icomp_sound.                    (* compiled individual instructions is sound *)
  Qed.

End mma3_mma2_compiler.
