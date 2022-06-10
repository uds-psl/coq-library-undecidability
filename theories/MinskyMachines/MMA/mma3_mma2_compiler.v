(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Utf8.

From Undecidability.Shared.Libs.DLW 
  Require Import utils gcd prime pos vec subcode sss compiler_correction.

From Undecidability.FRACTRAN
  Require Import prime_seq.

From Undecidability.MinskyMachines.MMA
  Require Import mma_defs mma_utils.

Local Definition combi_235 a b c := 2^a*(3^b*5^c).

#[local] Notation "⦉ x , y , z ⦊ " := (combi_235 x y z) (at level 1, format "⦉ x , y , z ⦊ ").

Section combi_235.

  Local Fact prime_2 : prime 2.   Proof. apply prime_bool_spec; trivial. Qed.
  Local Fact prime_3 : prime 3.   Proof. apply prime_bool_spec; trivial. Qed.
  Local Fact prime_5 : prime 5.   Proof. apply prime_bool_spec; trivial. Qed.

  Hint Resolve prime_2 prime_3 prime_5 : core.

  Ltac does_not_divide := 
    intros H;
    apply divides_pow in H; auto;
    now apply prime_divides in H; auto.

  Local Fact not_divides_2_3 x : ~ divides 2 (3^x).   Proof. does_not_divide. Qed.
  Local Fact not_divides_2_5 x : ~ divides 2 (5^x).   Proof. does_not_divide. Qed.
  Local Fact not_divides_3_2 x : ~ divides 3 (2^x).   Proof. does_not_divide. Qed.
  Local Fact not_divides_3_5 x : ~ divides 3 (5^x).   Proof. does_not_divide. Qed.
  Local Fact not_divides_5_2 x : ~ divides 5 (2^x).   Proof. does_not_divide. Qed.
  Local Fact not_divides_5_3 x : ~ divides 5 (3^x).   Proof. does_not_divide. Qed.

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

  Fact combi_235_inj a₁ b₁ c₁ a₂ b₂ c₂ : ⦉a₁,b₁,c₁⦊ = ⦉a₂,b₂,c₂⦊ -> a₁ = a₂ /\ b₁ = b₂ /\ c₁ = c₂.
  Proof.
    intros H.
    apply power_factor_uniq in H as (<- & H); try easy; split; trivial.
    apply power_factor_uniq in H as (<- & H); try easy; split; trivial.
    replace (5^c₁) with (5^c₁*1) in H by lia. 
    replace (5^c₂) with (5^c₂*1) in H by lia.
    now apply power_factor_uniq in H as [].
  Qed.

  Fact pow_gt_0 a n : 0 < a -> 0 < a^n.
  Proof. intro; induction n; simpl; auto; apply Nat.mul_pos_pos; auto. Qed.

  Fact combi_235_gt_0 a b c : 0 < ⦉a,b,c⦊ .
  Proof. repeat apply Nat.mul_pos_pos; apply pow_gt_0; lia. Qed.

  Fact combi_235_2_0 b c : ⦉0,b,c⦊ = 3^b*5^c.
  Proof. unfold combi_235; rewrite Nat.pow_0_r; ring. Qed.

  Fact combi_235_3_0 a c : ⦉a,0,c⦊ = 2^a*5^c.
  Proof. unfold combi_235; rewrite Nat.pow_0_r; ring. Qed.

  Fact combi_235_5_0 a b : ⦉a,b,0⦊ = 2^a*3^b.
  Proof. unfold combi_235; rewrite Nat.pow_0_r; ring. Qed.

  Fact combi_235_mult2 a b c : 2*⦉a,b,c⦊ = ⦉1+a,b,c⦊ .
  Proof. unfold combi_235; rewrite Nat.pow_succ_r'; ring. Qed.

  Fact combi_235_mult3 a b c : 3*⦉a,b,c⦊ = ⦉a,1+b,c⦊ .
  Proof. unfold combi_235; rewrite Nat.pow_succ_r'; ring. Qed.

  Fact combi_235_mult5 a b c : 5*⦉a,b,c⦊ = ⦉a,b,1+c⦊ .
  Proof. unfold combi_235; rewrite Nat.pow_succ_r'; ring. Qed.

  Fact combi_235_div2 a b c : divides 2 ⦉a,b,c⦊  <-> a <> 0.
  Proof.
    destruct a; auto.
    + split; try tauto.
      rewrite combi_235_2_0.
      intros H.
      apply not_divides_2_35 in H as [].
    + split; try easy; intros _.
      change (S a) with (1+a); rewrite <- combi_235_mult2.
      apply divides_mult_r, divides_refl.
  Qed.

  Fact combi_235_div3 a b c : divides 3 ⦉a,b,c⦊  <-> b <> 0.
  Proof.
    destruct b; auto.
    + split; try tauto.
      rewrite combi_235_3_0.
      intros H.
      apply not_divides_3_25 in H as [].
    + split; try easy; intros _.
      change (S b) with (1+b); rewrite <- combi_235_mult3.
      apply divides_mult_r, divides_refl.
  Qed.

  Fact combi_235_div5 a b c : divides 5 ⦉a,b,c⦊  <-> c <> 0.
  Proof.
    destruct c; auto.
    + split; try tauto.
      rewrite combi_235_5_0.
      intros H.
      apply not_divides_5_23 in H as [].
    + split; try easy; intros _.
      change (S c) with (1+c); rewrite <- combi_235_mult5.
      apply divides_mult_r, divides_refl.
  Qed.

End combi_235.

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).

Section mma3_mma2_compiler.

  Variable n : nat.

  Let simul (v : vec nat (3+n)) (w : vec nat (2+n)) : Prop :=
        w#>pos0 = 0
     /\ w#>pos1 = ⦉v#>pos0,v#>pos1,v#>pos2⦊
     /\ forall x : pos n, v#>(pos_right _ x) = w#>(pos_right _ x).

  Infix "⋈" := simul (at level 70, no associativity).

  Inductive pos3_id : pos 3 -> Type :=
    | pos3_pos0 : pos3_id pos0
    | pos3_pos1 : pos3_id pos1
    | pos3_pos2 : pos3_id pos2.

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

  Local Fact pos3_235_pos0 : ⟨pos0⟩ = 2. Proof. trivial. Qed.
  Local Fact pos3_235_pos1 : ⟨pos1⟩ = 3. Proof. trivial. Qed.
  Local Fact pos3_235_pos2 : ⟨pos2⟩ = 5. Proof. trivial. Qed.

  Local Fact pos3_235_gt_0 x : 0 < ⟨x⟩.
  Proof. destruct (pos3_split x); cbn; lia. Qed.

  Hint Resolve pos3_235_gt_0 : core.

  Section icomp.

    Local Definition icomp_len : mm_instr (pos (3+n)) -> nat.
    Proof.
      intros [ x | x j ]; apply pos_both in x as [ x | x ].
      + exact (8+pos3_235 x).
      + exact 1.
      + exact (16+7*pos3_235 x).
      + exact 1.
    Defined.

    Variable lnk : nat -> nat.

    Local Definition icomp : nat -> mm_instr (pos (3+n)) -> list (mm_instr (pos (2+n))).
    Proof using lnk.
      intros i [ x | x j ].
      + apply pos_both in x as [ x | x ].
        * exact (mma_mult_cst_with_zero pos1 pos0 ⟨x⟩ (lnk i)).
        * exact (INCₐ (pos_nxt (pos_nxt x)) :: nil).
      + apply pos_both in x as [ x | x ].
        * exact (mma_div_branch pos1 pos0 ⟨x⟩ (lnk i) (lnk j)).
        * exact (DECₐ (pos_nxt (pos_nxt x)) (lnk j) :: nil).
    Defined.

    Local Fact icomp_length_eq i ρ : length (icomp i ρ) = icomp_len ρ.
    Proof.
      unfold icomp, icomp_len.
      destruct ρ as [ x | x j ]; destruct (pos_both _ _ x); auto.
      + now rewrite mma_mult_cst_with_zero_length.
      + now rewrite mma_div_branch_length.
    Qed.

    Local Fact icomp_eq_1 i (x : pos 3) : icomp i (INCₐ (pos_left _ x)) = mma_mult_cst_with_zero pos1 pos0 ⟨x⟩ (lnk i).
    Proof. unfold icomp; now rewrite pos_both_left. Qed.

    Local Fact icomp_eq_2 i (x : pos n) : icomp i (INCₐ (pos_right _ x)) = INCₐ (pos_nxt (pos_nxt x)) :: nil.
    Proof. unfold icomp; now rewrite pos_both_right. Qed.

    Local Fact icomp_eq_3 i (x : pos 3) j : icomp i (DECₐ (pos_left _ x) j) = mma_div_branch pos1 pos0 ⟨x⟩ (lnk i) (lnk j).
    Proof. unfold icomp; now rewrite pos_both_left. Qed.

    Local Fact icomp_eq_4 i (x : pos n) j : icomp i (DECₐ (pos_right _ x) j) = DECₐ (pos_nxt (pos_nxt x)) (lnk j) :: nil.
    Proof. unfold icomp; now rewrite pos_both_right. Qed.

  End icomp.

  Local Lemma icomp_sound : instruction_compiler_sound icomp (@mma_sss _) (@mma_sss _) simul.
  Proof.
    intros lnk [ x | x j ] i1 v1 i2 v2 w1 H.
    + apply mma_sss_INC_inv in H as (-> & ->).
      revert w1 i1 v1. 
      pattern x; revert x; apply pos_left_right_rect; intros x w1 i v.
      * rewrite icomp_eq_1, mma_mult_cst_with_zero_length.
        intros H1 (H2 & H3 & H4).
        exists (w1[(⟨x⟩*(w1#>pos1))/pos1]); msplit 3; rew vec.
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
          change pos1 with (@pos_left 2 n pos1).
          apply pos_left_right_neq.
      * rewrite icomp_eq_2; simpl.
        intros H1 (H2 & H3 & H4).
        exists (w1[(S (w1#>(pos_right 2 x)))/pos_right 2 x]); msplit 3.
        - mma sss INC with (pos_right 2 x); simpl pos_right.
          1: apply subcode_refl.
          mma sss stop.
          now f_equal; rewrite H1.
        - rewrite vec_change_neq; auto.
          change pos0 with (@pos_left 2 n pos0).
          intros E; symmetry in E; revert E.
          apply pos_left_right_neq.
        - rewrite vec_change_neq.
          ++ rewrite H3; f_equal; rew vec.
          ++ change pos1 with (@pos_left 2 n pos1).
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
          ++ apply subcode_refl.
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
             ** apply subcode_refl.
             ** specialize (H4 x); simpl pos_right in *.
                rewrite <- Hk, H4; auto.
             ** mma sss stop.
          ++ intros p.
             specialize (H4 p); cbn in H4.
             destruct (pos_eq_dec p x) as [ -> | H5 ]; rew vec.
             rewrite !vec_change_neq; auto.
             all: contradict H5; now repeat apply pos_nxt_inj in H5.
  Qed.

  Theorem mma3_mma2_compiler : compiler_t (@mma_sss _) (@mma_sss _) simul.
  Proof.
    apply generic_compiler with icomp icomp_len.
    + intros; now rewrite icomp_length_eq.
    + apply mma_sss_total_ni.
    + apply mma_sss_fun.
    + apply icomp_sound.
  Qed.

End mma3_mma2_compiler.

Check mma3_mma2_compiler.