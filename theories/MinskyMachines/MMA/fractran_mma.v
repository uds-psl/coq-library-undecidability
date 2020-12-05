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

Local Notation "P /MM2/ s -+> t" := (sss_progress (@mma_sss _) P s t) (at level 70, no associativity).
Local Notation "P /MM2/ s ->> t" := (sss_compute (@mma_sss _) P s t) (at level 70, no associativity).
Local Notation "P /MM2/ s ↓" := (sss_terminates (@mma_sss _) P s) (at level 70, no associativity). 

Local Notation "l /F/ x → y" := (fractran_step l x y) (at level 70, no associativity).

(* FRACTRAN with two counter *)

Section Fractran_with_two_counters.

  Hint Resolve subcode_refl : core.
  Hint Rewrite mma_null_length mma_transfert_length mma_incs_length mma_decs_copy_length 
               mma_mult_cst_length mma_decs_length mma_mod_cst_length mma_div_cst_length : length_db.

  Let src : pos 2 := pos0.
  Let dst : pos 2 := pos1.

  Ltac dest x y := destruct (pos_eq_dec x y) as [ | ]; [ subst x | ]; rew vec.

  Let Hsrc_dst : src <> dst.    Proof. discriminate. Qed.
  Let Hdst_src : dst <> src.    Proof. discriminate. Qed.

  Section mma_loop.

    Definition mma_loop := INC src :: DEC src 1 :: nil.

    Fact mma_loop_loop v : (1,mma_loop) /MM2/ (1,v) -+> (1,v).
    Proof.
      unfold mma_loop.
      mma sss INC with src.
      mma sss DEC S with src 1 (v#>src); rew vec.
      mma sss stop.
    Qed.

    Theorem mma_loop_spec v : ~ (1,mma_loop) /MM2/ (1,v) ↓.
    Proof.
      intros (w & (k & Hk) & H2); revert w Hk H2.
      induction on k as IHk with measure k; intros w Hk Hw.
      destruct subcode_sss_progress_inv with (4 := mma_loop_loop v) (5 := Hk)
        as (q & H1 & H2); auto.
      { apply mma_sss_fun. }
      apply IHk with (1 := H1) (2 := H2); auto.
    Qed.
  
  End mma_loop.

  Section mma_fractran_one.

    (* FRACTRAN computation, try one fraction a/b *)

    Variables (a b : nat) (p i : nat).

    Definition mma_fractran_one :=
           mma_mult_cst src dst a i
        ++ mma_mod_cst dst src (11+a+4*b+i) (21+a+7*b+i) b (5+a+i)
        ++ mma_div_cst src dst b (11+a+4*b+i)
        ++ mma_transfert dst src (16+a+7*b+i)
        ++ INC dst :: DEC dst p
        :: mma_div_cst src dst a (21+a+7*b+i)
        ++ mma_transfert dst src (26+4*a+7*b+i).

    Fact mma_fractran_one_length : length mma_fractran_one = 29+4*a+7*b.
    Proof. unfold mma_fractran_one; rew length; lia. Qed.

    Hypothesis (Ha : a <> 0) (Hb : b <> 0).

    (* If the state in src is compatible with a/b then
       src becomes src*a/b and jump at p *)

    Fact mma_fractran_one_ok_progress k v :
            k*b = a*(v#>src)
         -> v#>dst = 0
         -> (i,mma_fractran_one) /MM2/ (i,v) -+> (p,v[k/src]).
    Proof using Ha Hb.
      intros H1 H2; unfold mma_fractran_one.
      apply sss_progress_trans with (5+a+i,v[0/src][(k*b)/dst]).
      { apply subcode_sss_progress with (P := (i,mma_mult_cst src dst a i)); auto.
        apply mma_mult_cst_progress; auto.
        rewrite H2, <- H1; do 2 f_equal; lia. }
      apply sss_progress_trans with (11+a+4*b+i,v[(k*b)/src][0/dst]).
      { apply subcode_sss_progress with (P := (5+a+i,mma_mod_cst dst src (11+a+4*b+i) (21+a+7*b+i) b (5+a+i))); auto.
        apply mma_mod_cst_divides_progress with k; rew vec; try lia.
        f_equal; apply vec_pos_ext; intros y; dest y dst; try lia; dest y src. }
      apply sss_progress_trans with (16+a+7*b+i,v[0/src][k/dst]).
      { apply subcode_sss_progress with (P := (11+a+4*b+i,mma_div_cst src dst b (11+a+4*b+i))); auto.
        apply mma_div_cst_progress with k; auto; rew vec; try lia.
        f_equal; try lia.
        apply vec_pos_ext; intros y; dest y dst; try lia; dest y src. }
      apply sss_progress_trans with (19+a+7*b+i,v[k/src][0/dst]).
      { apply subcode_sss_progress with (P := (16+a+7*b+i,mma_transfert dst src (16+a+7*b+i))); auto.
        apply mma_transfert_progress; auto.
        f_equal; try lia.
        apply vec_pos_ext; intros y; dest y dst; try lia; dest y src. }
      mma sss INC with dst.
      mma sss DEC S with dst p 0; rew vec.
      mma sss stop; f_equal.
      apply vec_pos_ext; intros y; dest y dst; try lia; dest y src. 
    Qed.

    (* If the state in src is not compatible with a/b then jump at the end of the code *)

    Fact mma_fractran_one_nok_progress v :
            ~ divides b (a*(v#>src))
         -> v#>dst = 0
         -> (i,mma_fractran_one) /MM2/ (i,v) -+> (length mma_fractran_one+i,v).
    Proof using Ha Hb.
      rewrite mma_fractran_one_length.
      intros H1 H2; unfold mma_fractran_one.
      rewrite divides_rem_eq in H1.
      revert H1.
      generalize (div_rem_spec1 (a*(v#>src)) b)
                 (div_rem_spec2 (a*(v#>src)) Hb).
      generalize (div (a*(v#>src)) b) (rem (a*(v#>src)) b); intros x y H3 H4 H5.
      apply sss_progress_trans with (5+a+i,v[0/src][(x*b+y)/dst]).
      { apply subcode_sss_progress with (P := (i,mma_mult_cst src dst a i)); auto.
        apply mma_mult_cst_progress; auto.
        rewrite H2, <- H3; do 2 f_equal; lia. }
      apply sss_progress_trans with (21+a+7*b+i,v[(a*(v#>src))/src][0/dst]).
      { apply subcode_sss_progress with (P := (5+a+i,mma_mod_cst dst src (11+a+4*b+i) (21+a+7*b+i) b (5+a+i))); auto.
        apply mma_mod_cst_not_divides_progress with x y; rew vec; try lia.
        f_equal; apply vec_pos_ext; intros c; dest c dst; try lia; dest c src; lia. }
      apply sss_progress_trans with (26+4*a+7*b+i,v[0/src][(v#>src)/dst]).
      { apply subcode_sss_progress with (P := (21+a+7*b+i,mma_div_cst src dst a (21+a+7*b+i))); auto.
        apply mma_div_cst_progress with (v#>src); auto; rew vec; try lia; try ring.
        f_equal; try lia.
        apply vec_pos_ext; intros c; dest c dst; try lia; dest c src. }
      apply subcode_sss_progress with (P := (26+4*a+7*b+i,mma_transfert dst src (26+4*a+7*b+i))); auto.
      apply mma_transfert_progress; auto.
      f_equal; try lia.
      apply vec_pos_ext; intros c; dest c dst; try lia; dest c src. 
    Qed.

  End mma_fractran_one.

  Hint Rewrite mma_fractran_one_length : length_db.

  Section mma_fractran_step.

    (* One step of Fractran computation *)

    Variable (p : nat).

    Fixpoint mma_fractran_step ll i { struct ll } :=
      match ll with
        | nil       => nil
        | (a,b)::ll => let P := mma_fractran_one a b p i
                       in  P ++ mma_fractran_step ll (length P+i)
      end.

    Fact mma_fractran_step_success_progress ll i x y v : 
            Forall (fun c => fst c <> 0 /\ snd c <> 0) ll
         -> ll /F/ x → y
         -> v#>src = x
         -> v#>dst = 0
         -> (i,mma_fractran_step ll i) /MM2/ (i,v) -+> (p,v[y/src]).
    Proof.
      intros H1 H2; revert H2 i v H1.
      induction 1 as [ a b ll x y H1 | a b ll x y H1 H2 IH2 ];
        intros i v H3 H6 H7; rewrite Forall_cons_inv in H3; destruct H3 as ((H3 & H4) & H5); simpl in H3, H4;
        unfold mma_fractran_step; fold mma_fractran_step.
      + apply subcode_sss_progress with (P := (i,mma_fractran_one a b p i)); auto.
        apply mma_fractran_one_ok_progress; auto; rewrite H6, <- H1; ring.
      + apply sss_progress_trans with (length (mma_fractran_one a b p i)+i,v).
        { apply subcode_sss_progress with (P := (i,mma_fractran_one a b p i)); auto.
          apply mma_fractran_one_nok_progress; auto; rewrite H6; auto. }
        { apply subcode_sss_progress with (P := (length (mma_fractran_one a b p i)+i,
                                                 mma_fractran_step ll (length (mma_fractran_one a b p i)+i))); auto.
          apply subcode_right; lia. }
    Qed.

    Fact mma_fractran_step_failure_compute ll i v : 
            Forall (fun c => fst c <> 0 /\ snd c <> 0) ll
         -> fractran_stop ll (v#>src)
         -> v#>dst = 0
         -> (i,mma_fractran_step ll i) /MM2/ (i,v) ->> (length (mma_fractran_step ll i)+i,v).
    Proof.
      intros H1 H2 H3; revert H1 i H2.
      induction 1 as [ | (a,b) ll (Ha & Hb) Hll IH ]; intros i H4.
      + mma sss stop.
      + apply fractan_stop_cons_inv in H4; destruct H4 as (H4 & H5).
        unfold mma_fractran_step; fold mma_fractran_step.
        set (P := mma_fractran_one a b p i); rew length.
        apply sss_compute_trans with (length P+i,v).
        { apply subcode_sss_compute with (P := (i,P)); auto.
          apply sss_progress_compute, mma_fractran_one_nok_progress; auto. }
        { apply subcode_sss_compute with (P := (length P+i,mma_fractran_step ll (length P + i))); auto.
          { apply subcode_right; lia. }
            replace (length P+length (mma_fractran_step ll (length P + i))+i)
            with    (length (mma_fractran_step ll (length P + i)) + (length P+i)) by lia.
            auto. }
    Qed.

  End mma_fractran_step.

  Section fractran_mma.

    Variables (ll : list (nat*nat)) (Hll : Forall (fun c => fst c <> 0 /\ snd c <> 0) ll).

    Let i := 1.

    Definition fractran_mma := mma_fractran_step i ll i.

    Lemma fractran_mma_sound v x w : 
               v#>dst = 0 
            -> fractran_compute ll (v#>src) x
            -> fractran_stop ll x 
            -> w = v[x/src]
            -> (i,fractran_mma) /MM2/ (i,v) ->> (length fractran_mma+i,w).
    Proof using Hll.
      intros H1 (u & H2) H3 ?; subst w.
      revert v x H1 H2 H3.
      induction u as [ | u IHu ]; simpl; intros v y H1 H2 H3.
      + rewrite <- H2; rew vec.
        apply mma_fractran_step_failure_compute; auto.
        rewrite H2; auto.
      + destruct H2 as (z & H2 & H4).
        apply mma_fractran_step_success_progress 
          with (1 := Hll) (p := i) (i := i) (v := v) in H2; auto.
        apply IHu with (v := v[z/src]) in H3; auto; rew vec.
        revert H3; rew vec; intros H3.
        apply sss_compute_trans with (2 := H3).
        apply sss_progress_compute; auto.
    Qed.

    Lemma fractran_mma_complete v : 
               v#>dst = 0 
            -> (i,fractran_mma) /MM2/ (i,v) ↓
            -> ll /F/ (v#>src) ↓.
    Proof using Hll.
      intros H1 ((j,w) & (u & H2) & H3); simpl fst in H3.
      revert v H1 H2.
      induction on u as IHu with measure u; intros v H1 H2.
      destruct (fractran_step_dec ll (v#>src)) as [ (y & Hy) | H4 ].
      2: { exists (v#>src); split; auto; exists 0; simpl; auto. }
      generalize Hy; intros H4.
      apply mma_fractran_step_success_progress 
        with (1 := Hll) (p := i) (i := i) (v := v) 
        in H4; auto.
      fold fractran_mma in H4.
      destruct subcode_sss_progress_inv with (4 := H4) (5 := H2)
        as (p & H5 & H6); auto.
      1: apply mma_sss_fun.
      apply IHu in H6; auto; rew vec.
      destruct H6 as (z & (k & Hk) & Hz2).
      exists z; split; auto; exists (S k), y; split; auto.
      revert Hk; rew vec.
    Qed.
   
    Theorem fractran_mma_reduction x : 
        ll /F/ x ↓ <-> (i,fractran_mma) /MM2/ (i,x##0##vec_nil) ↓.
    Proof using Hll.
      split; auto.
      + intros (y & H2 & H3).
        exists (length fractran_mma+i,y##0##vec_nil); split; simpl; auto; try lia.
        apply fractran_mma_sound with (x := y); auto.
      + apply fractran_mma_complete; auto.
    Qed.

  End fractran_mma.

End Fractran_with_two_counters.

Section fractran_mma_reg_reduction.

  Variables (ll : list (nat*nat)).

  Let reduction : { P | Forall (fun c => snd c <> 0) ll -> forall x, ll /F/ x ↓ <-> (1,P) /MM2/ (1,x##0##vec_nil) ↓ }.
  Proof.
    destruct (Forall_Exists_dec (fun c : nat * nat => fst c <> 0)) with (l := ll) as [ H | H ].
    + intros (x,?); simpl; destruct (eq_nat_dec x 0); subst; auto. 
    + exists (fractran_mma ll); intros Hll x.
      apply fractran_mma_reduction.
      revert H Hll; repeat rewrite Forall_forall; firstorder.
    + rewrite Exists_exists in H.
      exists mma_loop; intros Hll.
      destruct H as ((x,y) & H1 & H2); simpl in H2.
      replace x with 0 in H1 by lia; clear H2.
      intros n; split.
      * intros H; exfalso.
        revert H; apply FRACTRAN_HALTING_zero_num.
        apply Exists_exists; exists (0,y); auto.
      * intros H; exfalso; revert H; apply mma_loop_spec.
  Qed.
  
  Definition fractran_reg_mma := proj1_sig reduction.

  Theorem fractran_reg_mma_reduction : 
                       Forall (fun c => snd c <> 0) ll 
          -> forall x, ll /F/ x ↓ 
                   <-> (1,fractran_reg_mma) /MM2/ (1,x##0##vec_nil) ↓.
  Proof. apply (proj2_sig reduction). Qed.

End fractran_mma_reg_reduction.
