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
  Require Import utils gcd pos vec subcode sss.

From Undecidability.MinskyMachines.MMA
  Require Import mma_defs mma_utils.

From Undecidability.FRACTRAN
  Require Import FRACTRAN fractran_utils.

Set Implicit Arguments.

Set Default Proof Using "Type".

Tactic Notation "rew" "length" := autorewrite with length_db.

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).
Local Notation ø := vec_nil.

Local Notation "P //ₐ s -+> t" := (sss_progress (@mma_sss _) P s t) (at level 70, no associativity).
Local Notation "P //ₐ s ->> t" := (sss_compute (@mma_sss _) P s t) (at level 70, no associativity).
Local Notation "P //ₐ s ~~> t" := (sss_output (@mma_sss _) P s t) (at level 70, no associativity).
Local Notation "P //ₐ s ↓" := (sss_terminates (@mma_sss _) P s) (at level 70, no associativity). 

Local Notation "Q /F/ x ≻ y" := (fractran_step Q x y) (at level 70, no associativity).
Local Notation "Q /F/ x ⊁ *" := (fractran_stop Q x) (at level 70, no associativity).

(* FRACTRAN with two counter *)

Section Fractran_with_two_counters.

  Hint Resolve subcode_refl : core.
  Hint Rewrite mma_jump_length mma_null_length mma_transfert_length mma_incs_length mma_decs_copy_length 
               mma_mult_cst_length mma_decs_length mma_mod_cst_length mma_div_cst_length : length_db.

  Notation JUMPₐ := mma_jump.
  Notation NULLₐ := mma_null.
  Notation TRANSFERTₐ := mma_transfert.
  Notation INCSₐ := mma_incs.
  Notation DECSₐ := mma_decs.
  Notation DECS_COPYₐ := mma_decs_copy.
  Notation MULT_CSTₐ := mma_mult_cst.
  Notation MOD_CSTₐ := mma_mod_cst.
  Notation DIV_CSTₐ := mma_div_cst.
  Notation LOOPₐ := mma_loop.

  Let src : pos 2 := pos0.
  Let dst : pos 2 := pos1.

  Ltac dest x y := destruct (pos_eq_dec x y) as [ | ]; [ subst x | ]; rew vec.

  Let Hsrc_dst : src <> dst.    Proof. discriminate. Qed.
  Let Hdst_src : dst <> src.    Proof. discriminate. Qed.

  Section mma_fractran_one.

    (* FRACTRAN computation, try one fraction u/v *)

    Variables (p q : nat) (j i : nat).

    Notation i0 := i.
    Notation i1 := (5+p+i0).
    Notation i2 := (6+4*q+i1).
    Notation i3 := (5+3*q+i2). 
    Notation i4 := (3+i3).
    Notation i5 := (2+i4). 
    Notation i6 := (5+3*p+i5). 

    Definition mma_fractran_one :=
           MULT_CSTₐ src dst p i0
        ++ MOD_CSTₐ dst src i2 i5 q i1
        ++ DIV_CSTₐ src dst q i2
        ++ TRANSFERTₐ dst src i3
        ++ JUMPₐ j dst
        ++ DIV_CSTₐ src dst p i5
        ++ TRANSFERTₐ dst src i6.

    Fact mma_fractran_one_length : length mma_fractran_one = 29+4*p+7*q.
    Proof. unfold mma_fractran_one; rew length; lia. Qed.

    Hypothesis (Hq : q <> 0).

    (* If the state in src is compatible with p/q then
       src becomes src*p/q and jump at j *)

    Fact mma_fractran_one_ok_progress k v :
            k*q = p*(v#>src)
         -> v#>dst = 0
         -> (i0,mma_fractran_one) //ₐ (i0,v) -+> (j,v[k/src]).
    Proof using Hq.
      intros H1 H2; unfold mma_fractran_one.
      apply sss_progress_trans with (i1,v[0/src][(k*q)/dst]).
      { apply subcode_sss_progress with (P := (i,mma_mult_cst src dst p i)); auto.
        apply mma_mult_cst_progress; auto.
        rewrite H2, <- H1; do 2 f_equal; lia. }
      apply sss_progress_trans with (i2,v[(k*q)/src][0/dst]).
      { apply subcode_sss_progress with (P := (i1,mma_mod_cst dst src i2 i5 q i1)); auto.
        apply mma_mod_cst_divides_progress with k; rew vec; try lia.
        f_equal; apply vec_pos_ext; intros y; dest y dst; try lia; dest y src. }
      apply sss_progress_trans with (i3,v[0/src][k/dst]).
      { apply subcode_sss_progress with (P := (i2,mma_div_cst src dst q i2)); auto.
        apply mma_div_cst_progress with k; auto; rew vec; try lia.
        f_equal; try lia.
        apply vec_pos_ext; intros y; dest y dst; try lia; dest y src. }
      apply sss_progress_trans with (i4,v[k/src][0/dst]).
      { apply subcode_sss_progress with (P := (i3,mma_transfert dst src i3)); auto.
        apply mma_transfert_progress; auto.
        f_equal; try lia.
        apply vec_pos_ext; intros y; dest y dst; try lia; dest y src. }
      apply sss_progress_compute_trans with (j,v[k/src][0/dst]).
      { apply subcode_sss_progress with (P := (i4,JUMPₐ j dst)); auto.
        apply mma_jump_progress; auto. }
      mma sss stop; f_equal.
      apply vec_pos_ext; intros y; dest y dst; try lia; dest y src. 
    Qed.

    (* If the state in src is not compatible with a/b then jump at the end of the code *)

    Fact mma_fractran_one_nok_progress v :
            ~ divides q (p*(v#>src))
         -> v#>dst = 0
         -> (i0,mma_fractran_one) //ₐ (i0,v) -+> (length mma_fractran_one+i0,v).
    Proof using Hq.
      rewrite mma_fractran_one_length.
      intros H1 H2; unfold mma_fractran_one.
      rewrite divides_rem_eq in H1.
      revert H1.
      generalize (div_rem_spec1 (p*(v#>src)) q)
                 (div_rem_spec2 (p*(v#>src)) Hq).
      generalize (div (p*(v#>src)) q) (rem (p*(v#>src)) q); intros x y H3 H4 H5.
      apply sss_progress_trans with (i1,v[0/src][(x*q+y)/dst]).
      { apply subcode_sss_progress with (P := (i0,mma_mult_cst src dst p i0)); auto.
        apply mma_mult_cst_progress; auto.
        rewrite H2, <- H3; do 2 f_equal; lia. }
      apply sss_progress_trans with (i5,v[(p*(v#>src))/src][0/dst]).
      { apply subcode_sss_progress with (P := (i1,mma_mod_cst dst src i2 i5 q i1)); auto.
        apply mma_mod_cst_not_divides_progress with x y; rew vec; try lia.
        f_equal; apply vec_pos_ext; intros c; dest c dst; try lia; dest c src; lia. }
      apply sss_progress_trans with (i6,v[0/src][(v#>src)/dst]).
      { apply subcode_sss_progress with (P := (i5,mma_div_cst src dst p i5)); auto.
        apply mma_div_cst_progress with (v#>src); auto; rew vec; try lia; try ring.
        f_equal; try lia.
        apply vec_pos_ext; intros c; dest c dst; try lia; dest c src. }
      apply subcode_sss_progress with (P := (i6,mma_transfert dst src i6)); auto.
      apply mma_transfert_progress; auto.
      f_equal; try lia.
      apply vec_pos_ext; intros c; dest c dst; try lia; dest c src. 
    Qed.

  End mma_fractran_one.

  Notation FRAC_ONEₐ := mma_fractran_one.

  Hint Rewrite mma_fractran_one_length : length_db.

  Section mma_fractran_step.

    (* One step of Fractran computation *)

    Variable (j : nat).

    Fixpoint mma_fractran_step Q i { struct Q } :=
      match Q with
        | nil      => nil
        | (p,q)::Q => let P := FRAC_ONEₐ p q j i
                      in  P ++ mma_fractran_step Q (length P+i)
      end.

    Notation FRAC_STEPₐ := mma_fractran_step.

    Fact mma_fractran_step_success_progress Q i x y : 
            fractran_regular Q
         -> Q /F/ x ≻ y
         -> (i,mma_fractran_step Q i) //ₐ (i,x##0##ø) -+> (j,y##0##ø).
    Proof.
      unfold fractran_regular.
      intros H1 H2; revert H2 i H1.
      induction 1 as [ p q ll x y H1 | p q ll x y H1 H2 IH2 ];
        intros i H3; rewrite Forall_cons_inv in H3; destruct H3 as (H3 & H4); simpl in H3, H4;
        unfold mma_fractran_step; fold mma_fractran_step.
      + apply subcode_sss_progress with (P := (i,mma_fractran_one p q j i)); auto.
        apply mma_fractran_one_ok_progress with (v := _##_##ø); auto.
        simpl; rewrite <- H1; ring.
      + apply sss_progress_trans with (length (mma_fractran_one p q j i)+i,x##0##ø).
        { apply subcode_sss_progress with (P := (i,mma_fractran_one p q j i)); auto.
          apply mma_fractran_one_nok_progress; auto. }
        { apply subcode_sss_progress 
            with (P := (length (mma_fractran_one p q j i)+i,
                        mma_fractran_step ll (length (mma_fractran_one p q j i)+i))); auto. }
    Qed.

    Fact mma_fractran_step_failure_compute Q i x : 
            fractran_regular Q
         -> Q /F/ x ⊁ *
         -> (i,mma_fractran_step Q i) //ₐ (i,x##0##ø) ->> (length (mma_fractran_step Q i)+i,x##0##ø).
    Proof.
      unfold fractran_regular.
      intros H1 H2; revert H1 i H2.
      induction 1 as [ | (p,q) ll Hq Hll IH ]; intros i H4.
      + mma sss stop.
      + apply fractan_stop_cons_inv in H4; destruct H4 as (H4 & H5).
        unfold mma_fractran_step; fold mma_fractran_step.
        set (P := mma_fractran_one p q j i); rew length.
        apply sss_compute_trans with (length P+i,x##0##ø).
        { apply subcode_sss_compute with (P := (i,P)); auto.
          apply sss_progress_compute, mma_fractran_one_nok_progress; auto. }
        { apply subcode_sss_compute with (P := (length P+i,mma_fractran_step ll (length P + i))); auto.
          replace (length P+length (mma_fractran_step ll (length P + i))+i)
          with    (length (mma_fractran_step ll (length P + i)) + (length P+i)) by lia; auto. }
    Qed.

  End mma_fractran_step.

  Section fractran_mma.

    Variables (Q : list (nat*nat)) (HQ : fractran_regular Q).

    Definition fractran_mma := mma_fractran_step 1 Q 1.

    Lemma fractran_mma_sound x y : 
               fractran_compute Q x y
            -> Q /F/ y ⊁ *
            -> (1,fractran_mma) //ₐ (1,x##0##ø) ->> (length fractran_mma+1,y##0##ø).
    Proof using HQ.
      intros (u & H2) H3.
      revert x y H2 H3.
      induction u as [ | u IHu ]; simpl; intros x y H2 H3.
      + rewrite H2; apply mma_fractran_step_failure_compute; auto.
      + destruct H2 as (z & H2 & H4).
        apply mma_fractran_step_success_progress 
          with (1 := HQ) (j := 1) (i := 1) in H2; auto.
        apply IHu with (x := z) in H3; auto; rew vec.
        apply sss_compute_trans with (2 := H3).
        apply sss_progress_compute; auto.
    Qed.

    Lemma fractran_mma_complete x : 
               (1,fractran_mma) //ₐ (1,x##0##ø) ↓
            -> Q /F/ x ↓.
    Proof using HQ.
      intros ((j,w) & (k & H2) & H3); simpl fst in H3.
      revert x H2.
      induction on k as IHu with measure k; intros x H2.
      destruct (fractran_step_dec Q x) as [ (y & Hy) | H4 ].
      2: { exists x; split; auto; exists 0; simpl; auto. }
      generalize Hy; intros H4.
      apply mma_fractran_step_success_progress 
        with (1 := HQ) (j := 1) (i := 1) 
        in H4; auto.
      fold fractran_mma in H4.
      destruct subcode_sss_progress_inv with (4 := H4) (5 := H2)
        as (r & H5 & H6); auto.
      1: apply mma_sss_fun.
      apply IHu in H6; auto; rew vec.
      destruct H6 as (z & (u & Hk) & Hz2).
      exists z; split; auto; exists (S u), y; split; auto.
    Qed.
   
    Theorem fractran_mma_reduction x : 
        Q /F/ x ↓ <-> (1,fractran_mma) //ₐ (1,x##0##ø) ↓.
    Proof using HQ.
      split; auto.
      + intros (y & H2 & H3).
        exists (length fractran_mma+1,y##0##vec_nil); split; simpl; auto; try lia.
        apply fractran_mma_sound; auto.
      + apply fractran_mma_complete; auto.
    Qed.

  End fractran_mma.

  Section fractran_mma0.

    Variables (Q : list (nat*nat)) (HQ : fractran_regular Q).

    Let P := fractran_mma Q.

    Definition fractran_mma0 := P ++ NULLₐ src (length P + 1) ++ JUMPₐ 0 src.

    Notation FRAC_MMAₐ := fractran_mma0.

    Let fmma0_1 x : (1,FRAC_MMAₐ) //ₐ (length P+1,x##0##ø) -+> (0,0##0##ø).
    Proof.
      unfold fractran_mma0.
      apply subcode_sss_progress with (P := (length P+1, NULLₐ src (length P + 1) ++ JUMPₐ 0 src)); auto.
      apply sss_progress_trans with (length (NULLₐ src (length P + 1)) + length P+1,0##0##ø).
      + apply subcode_sss_progress with (P := (length P+1,NULLₐ src (length P+1))); auto.
        apply mma_null_progress; auto.
      + apply subcode_sss_progress with (2 := mma_jump_progress _ src _ eq_refl); auto.
    Qed.

    Lemma fractran_mma0_sound x y : 
               fractran_compute Q x y
            -> fractran_stop Q y 
            -> (1,FRAC_MMAₐ) //ₐ (1,x##0##ø) ->> (0,0##0##ø).
    Proof using HQ.
      intros H2 H3.
      unfold fractran_mma0.
      apply sss_compute_trans with (length P+1,y##0##ø).
      + apply subcode_sss_compute with (P := (1,P)); auto.
        apply fractran_mma_sound with (2 := H2); auto.
      + apply sss_progress_compute, fmma0_1; auto.
    Qed.

    Variable x : nat.

    Let Term1 := Q /F/ x ↓.
    Let Term2 := (1,FRAC_MMAₐ) //ₐ (1,x##0##ø) ~~> (0,0##0##ø).
    Let Term3 := (1,FRAC_MMAₐ) //ₐ (1,x##0##ø) ↓.

    Theorem fractran_mma0_reduction : 
         (Term1 -> Term2) /\ (Term2 -> Term3) /\ (Term3 -> Term1).
    Proof using HQ.
      msplit 2; unfold Term1, Term2, Term3.
      + intros (y & H1 & H2); split; simpl; auto.
        apply fractran_mma0_sound with (1 := H1); auto.
      + now exists (0,0##0##ø).
      + intros H1; apply fractran_mma_reduction; auto.
        revert H1; apply subcode_sss_terminates.
        unfold fractran_mma0, P; auto.
    Qed.

  End fractran_mma0.

End Fractran_with_two_counters.

Theorem fractran_reg_mma0_reductions Q : 
             fractran_regular Q 
          -> (forall x, Q /F/ x ↓ <-> (1,fractran_mma0 Q) //ₐ (1,x##0##ø) ↓)
          /\ (forall x, Q /F/ x ↓ <-> (1,fractran_mma0 Q) //ₐ (1,x##0##ø) ~~> (0,(0##0##ø))).
Proof.
  do 2 (split; intros); repeat (apply fractran_mma0_reduction; auto).
Qed.

