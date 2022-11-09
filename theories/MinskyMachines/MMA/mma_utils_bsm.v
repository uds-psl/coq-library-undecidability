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
  Require Import utils list_bool pos vec subcode sss.

From Undecidability.MinskyMachines.MMA
  Require Import mma_defs mma_utils.

Set Implicit Arguments.
Set Default Goal Selector "!".

Tactic Notation "rew" "length" := autorewrite with length_db.

#[local] Notation "e #> x" := (vec_pos e x).
#[local] Notation "e [ v / x ]" := (vec_change e x v).

#[local] Notation "P // s -+> t" := (sss_progress (@mma_sss _) P s t).
#[local] Notation "P // s ->> t" := (sss_compute (@mma_sss _) P s t).

(* Utils for Binary Stack Machines simulation *)

Section Minsky_Machine_alt_utils_BSM.

  Variable (n : nat).

  Ltac dest x y := destruct (pos_eq_dec x y) as [ | ]; [ subst x | ]; rew vec.

  Hint Resolve subcode_refl : core.

  Notation JUMPₐ := mma_jump.
  Notation TRANSFERTₐ := mma_transfert.
  Notation MULT_CSTₐ := mma_mult_cst.

  Hint Rewrite mma_jump_length 
               mma_transfert_length 
               mma_mult_cst_length : length_db.

  Section mma_div2_branch.

    Variable (x q : pos n) (Hxq : x <> q) (i j0 j1 : nat).

    Definition mma_div2_branch :=
           DECₐ x (3+i)
        :: JUMPₐ j0 x
        ++ DECₐ x (6+i)
        :: JUMPₐ j1 x
        ++ INCₐ q
        :: JUMPₐ i x.

    Fact mma_div2_branch_length : length mma_div2_branch = 9.
    Proof. unfold mma_div2_branch; rew length; auto. Qed.

    Local Fact mma_div2_branch_2k k v st :
            v#>x = 2*k
         -> st = (j0,v[0/x][(k+(v#>q))/q])
         -> (i,mma_div2_branch) // (i,v) -+> st.
    Proof using Hxq.
      revert v st; induction k as [ | k IHk ]; intros v st H1 ->; unfold mma_div2_branch.
      + mma sss DEC zero with x (3+i).
        apply subcode_sss_compute with (P := (1+i,JUMPₐ j0 x)); auto.
        simpl in H1; rewrite <- H1 at 3; simpl; rewrite !vec_change_same.
        apply mma_jump_spec.
      + replace (2*S k) with (S (S (2*k))) in H1 by lia.
        mma sss DEC S with x (3+i) (S (2*k)).
        mma sss DEC S with x (6+i) (2*k); rew vec.
        mma sss INC with q; rew vec.
        apply subcode_sss_compute_trans with (P := (7+i,JUMPₐ i  x)) (st2 := (i,v[(2*k)/x][(S (v#>q))/q])); auto.
        * apply sss_progress_compute, mma_jump_progress; auto.
        * apply sss_progress_compute, IHk; rew vec.
          f_equal; apply vec_pos_ext; intros p; dest p x; dest p q; lia.
    Qed.

    Local Fact mma_div2_branch_2k1 k v st :
           v#>x = 2*k+1
         -> st = (j1,v[0/x][(k+(v#>q))/q])
         -> (i,mma_div2_branch) // (i,v) -+> st.
    Proof using Hxq.
      revert v st; induction k as [ | k IHk ]; intros v st H1 ->; unfold mma_div2_branch.
      + mma sss DEC S with x (3+i) 0.
        mma sss DEC zero with x (6+i); rew vec.
        apply subcode_sss_compute with (P := (4+i,JUMPₐ j1 x)); auto.
        simpl plus.
        apply sss_progress_compute, mma_jump_progress; auto.
        apply vec_pos_ext; intros p; dest p x; dest p q; lia.
      + replace (2*S k+1) with (S (S (2*k+1))) in H1 by lia.
        mma sss DEC S with x (3+i) (S (2*k+1)).
        mma sss DEC S with x (6+i) (2*k+1); rew vec.
        mma sss INC with q; rew vec.
        apply subcode_sss_compute_trans with (P := (7+i,JUMPₐ i  x)) (st2 := (i,v[(2*k+1)/x][(S (v#>q))/q])); auto.
        * apply sss_progress_compute, mma_jump_progress; auto.
        * apply sss_progress_compute, IHk; rew vec.
          f_equal. 
          apply vec_pos_ext; intros p; dest p x; dest p q; lia.
    Qed.

    (** mma_div2_branch performs an Euclidean division of v#>x
        by 2, adding the quotient to v#>q and jumping to j[r]
        where r is the remainder *)

    Fact mma_div2_branch_progress v st :
          let (k,b) := div2 (v#>x) in 
          st = (if b then j1 else j0,v[0/x][(k+(v#>q))/q])
       -> (i,mma_div2_branch) // (i,v) -+> st.
    Proof using Hxq.
      generalize (div2_spec (v#>x)).
      destruct (div2 (v#>x)) as (k,[]); intros Hv ->.
      + apply mma_div2_branch_2k1 with k; auto.
      + apply mma_div2_branch_2k with k; auto.
    Qed.

  End mma_div2_branch.

  Notation DIV2ₐ := mma_div2_branch.

  Hint Rewrite mma_div2_branch_length : length_db.

  Fixpoint stack_enc (s : list bool) : nat :=
    match s with 
      | nil     => 1
      | One::s  => 1+2*stack_enc s
      | Zero::s =>   2*stack_enc s
    end.

  Fact stack_enc_S s : { k | stack_enc s = S k }.
  Proof.
    induction s as [ | [] s (k & Hk) ].
    + exists 0; auto.
    + exists (2*stack_enc s); auto.
    + exists (S (2*k)); simpl; lia.
  Qed.

  Section mma_push.

    Variables (src zero : pos n) 
              (Hsz : src <> zero) 
              (i : nat).

    Definition mma_push_Zero := 
    (*    i *)  TRANSFERTₐ src zero i ++ 
    (*  3+i *)  MULT_CSTₐ zero src 2 (3+i).
 
    Fact mma_push_Zero_length : length mma_push_Zero = 10.
    Proof. reflexivity. Qed.

    Fact mma_push_Zero_progress s v :
         v#>zero = 0
      -> v#>src  = stack_enc s
      -> (i,mma_push_Zero) // (i,v) -+> (10+i,v[(stack_enc (Zero::s))/src]).
    Proof using Hsz.
      intros H1 H2.
      unfold mma_push_Zero.
      apply sss_progress_trans with (st2 := (3+i,v[0/src][(v#>src)/zero])).
      + apply subcode_sss_progress with (P := (i,TRANSFERTₐ src zero i)); auto.
        apply mma_transfert_progress; auto.
        do 2 f_equal; lia.
      + apply subcode_sss_progress with (P := (3+i,MULT_CSTₐ zero src 2 (3+i))); auto.
        apply mma_mult_cst_progress; auto.
        f_equal; rew vec.
        apply vec_pos_ext; intros p.
        dest p src; simpl; try lia. 
        dest p zero.
    Qed.

    Definition mma_push_One := mma_push_Zero ++ INCₐ src :: nil.

    Fact mma_push_One_length : length mma_push_One = 11.
    Proof. reflexivity. Qed.

    Hint Rewrite mma_push_Zero_length : length_db.

    Fact mma_push_One_progress s v :
         v#>zero = 0
      -> v#>src  = stack_enc s
      -> (i,mma_push_One) // (i,v) -+> (11+i,v[(stack_enc (One::s))/src]).
    Proof using Hsz.
      intros H1 H2.
      unfold mma_push_One.
      apply sss_progress_trans with (10+i,v[(stack_enc (Zero::s))/src]).
      + apply subcode_sss_progress with (P := (i,mma_push_Zero)); auto.
        apply mma_push_Zero_progress; auto.
      + mma sss INC with src.
        mma sss stop; f_equal; rew vec.
    Qed.

  End mma_push.

  Section mma_pop.

    Variables (src zero : pos n) (Hsz : src <> zero) (i j0 j1 je : nat).

    Local Fact Hzs : zero <> src.
    Proof using Hsz. auto. Qed.

    Hint Resolve Hzs : core.

    Let src' := src.
 
    Definition mma_pop :=
    (*     i *)  TRANSFERTₐ src zero i ++
    (*   3+i *)  DIV2ₐ zero src (3+i) j0 (12+i) ++
    (*  12+i *)  DECₐ src (16+i) ::
    (*  13+i *)  INCₐ src ::
    (*  14+i *)  JUMPₐ je src ++
    (*  16+i *)  INCₐ src' ::
    (*  17+i *)  JUMPₐ j1 src.

    Fact mma_pop_length : length mma_pop = 19.
    Proof. reflexivity. Qed.

    Fact mma_pop_void_progress v :
         v#>zero = 0
      -> v#>src  = stack_enc nil 
      -> (i,mma_pop) // (i,v) -+> (je,v).
    Proof using Hsz.
      intros H1 H2; unfold mma_pop.
      apply sss_progress_trans with (st2 := (3+i,v[0/src][(v#>src)/zero])).
      1:{ apply subcode_sss_progress with (P := (i,TRANSFERTₐ src zero i)); auto.
          apply mma_transfert_progress; auto.
          do 2 f_equal; lia. }
      apply sss_progress_trans with (st2 := (12+i,v[0/src][0/zero])).
      1:{ apply subcode_sss_progress with (P := (3+i,DIV2ₐ zero src (3+i) j0 (12 + i))); auto.
          simpl in H2. 
          generalize (mma_div2_branch_progress Hzs (3+i) j0 (12+i) (v[0/src][1/zero])); rew vec; intros H3.
          simpl div2 in H3.
          rewrite H2; apply H3; f_equal; simpl; rew vec.
          apply vec_pos_ext; intros p; dest p src. }
      mma sss DEC zero with src (16+i); rew vec.
      mma sss INC with src; rew vec.
      apply subcode_sss_compute with (P := (14+i,JUMPₐ je src)); auto.
      apply sss_progress_compute, mma_jump_progress.
      apply vec_pos_ext; intros p; dest p src; dest p zero.
    Qed.

    Fact mma_pop_One_progress v s:
         v#>zero = 0
      -> v#>src  = stack_enc (One::s) 
      -> (i,mma_pop) // (i,v) -+> (j1,v[(stack_enc s)/src]).
    Proof using Hsz.
      intros H1 H2; unfold mma_pop.
      apply sss_progress_trans with (st2 := (3+i,v[0/src][(v#>src)/zero])).
      1:{ apply subcode_sss_progress with (P := (i,TRANSFERTₐ src zero i)); auto.
          apply mma_transfert_progress; auto.
          do 2 f_equal; lia. }
      apply sss_progress_trans with (st2 := (12+i,v[(stack_enc s)/src][0/zero])).
      1:{ apply subcode_sss_progress with (P := (3+i,DIV2ₐ zero src (3+i) j0 (12 + i))); auto. 
          match goal with |- _ // _ -+> ?st => 
            generalize (mma_div2_branch_progress Hzs (3+i) j0 (12+i) (v[0/src][(2*stack_enc s+1)/zero]) st)
          end. 
          rew vec; intros H3. 
          rewrite div2_2p1 in H3.
          rewrite (Nat.add_comm _ 1) in H3.
          rewrite H2.
          apply H3; f_equal; simpl; rew vec.
          apply vec_pos_ext; intros p; dest p src; dest p zero. }
      destruct (stack_enc_S s) as (k & Hk).
      mma sss DEC S with src (16+i) k; rew vec.
      mma sss INC with src'; rew vec.
      apply subcode_sss_compute with (P := (17+i,JUMPₐ j1 src)); auto.
      apply sss_progress_compute, mma_jump_progress.
      unfold src'; apply vec_pos_ext; intros p; dest p src; dest p zero.
    Qed.

    Fact mma_pop_Zero_progress v s:
         v#>zero = 0 
      -> v#>src  = stack_enc (Zero::s) 
      -> (i,mma_pop) // (i,v) -+> (j0,v[(stack_enc s)/src]).
    Proof using Hsz.
      intros H1 H2; unfold mma_pop.
      apply sss_progress_trans with (st2 := (3+i,v[0/src][(v#>src)/zero])).
      1:{ apply subcode_sss_progress with (P := (i,TRANSFERTₐ src zero i)); auto.
          apply mma_transfert_progress; auto.
          do 2 f_equal; lia. }
      apply subcode_sss_progress with (P := (3+i,DIV2ₐ zero src (3+i) j0 (12 + i))); auto.
      match goal with |- _ // _ -+> ?st => 
        generalize (mma_div2_branch_progress Hzs (3+i) j0 (12+i) (v[0/src][(2*stack_enc s)/zero]) st)
      end.
      rew vec; intros H3. 
      rewrite div2_2p0 in H3.
      rewrite (Nat.add_comm _ 0) in H3.
      rewrite H2.
      apply H3; f_equal.
      apply vec_pos_ext; intros p; dest p src; dest p zero.
    Qed.

  End mma_pop.

End Minsky_Machine_alt_utils_BSM.





