(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

From Undecidability.Shared.Libs.DLW
  Require Import Utils.utils Vec.pos Vec.vec Code.subcode Code.sss.

From Undecidability.MinskyMachines.MMenv 
  Require Import env mme_defs. 

Set Implicit Arguments.

Tactic Notation "rew" "length" := autorewrite with length_db.

Local Notation "P // s ->> t" := (sss_compute (mm_sss_env eq_nat_dec) P s t).
Local Notation "P // s -+> t" := (sss_progress (mm_sss_env eq_nat_dec) P s t).
Local Notation "P // s -[ k ]-> t" := (sss_steps (mm_sss_env eq_nat_dec) P k s t).
Local Notation "P // s ↓" := (sss_terminates (mm_sss_env eq_nat_dec ) P s). 

Local Notation " e ⇢ x " := (@get_env _ _ e x).
Local Notation " e ⦃  x ⇠ v ⦄ " := (@set_env _ _ eq_nat_dec e x v).
Local Notation "x '⋈' y" := (forall i : nat, x⇢i = y⇢i :> nat) (at level 70, no associativity).

Section mm_env_utils.

  Ltac dest x y := destruct (eq_nat_dec x y) as [ | ]; [ subst x | ]; rew env.

  Section mm_transfert.

    Variables (src dst zero : nat).

    Hypothesis (Hsd : src <> dst) (Hsz : src <> zero) (Hdz : dst <> zero).

    Definition mm_transfert i := DEC src (3+i) :: INC dst :: DEC zero i :: nil.

    Fact mm_transfert_length i : length (mm_transfert i) = 3.
    Proof. reflexivity. Qed.

    Let mm_transfert_spec i e k x :  
           e⇢src = k
        -> e⇢dst = x
        -> e⇢zero = 0
        -> exists e', e' ⋈  e⦃src⇠0⦄⦃dst⇠k+x⦄
                   /\ (i,mm_transfert i) // (i,e) -+> (3+i,e').
    Proof.
      unfold mm_transfert.
      revert e x.
      induction k as [ | k IHk ]; intros e x H1 H2 H3.
      + exists e; split.
        * intros j; dest j src; dest j dst.
        * mm env DEC 0 with src (3+i).
          mm env stop; f_equal; auto.
      + destruct IHk with (e := e⦃src⇠k⦄⦃dst⇠1+x⦄) (x := 1+x)
          as (e' & H4 & H5); rew env.
        exists e'; split.
        * intros j; rewrite H4.
          dest j dst; try omega.
          dest j src.
        * mm env DEC S with src (3+i) k.
          mm env INC with dst.
          mm env DEC 0 with zero i; rew env.
          rewrite H2.
          apply sss_progress_compute; auto.
    Qed.

    Fact mm_transfert_progress i e : 
           e⇢dst = 0
        -> e⇢zero = 0
        -> exists e', e' ⋈  e⦃src⇠0⦄⦃dst⇠(e⇢src)⦄
                  /\ (i,mm_transfert i) // (i,e) -+> (3+i,e').
    Proof.
      intros H1 H2.
      destruct mm_transfert_spec with (e := e) (x := 0) (i := i) (k := e⇢src)
        as (e' & H3 & H4); auto.
      exists e'; split; auto.
      intros j; rewrite H3, plus_comm; auto.
    Qed.

  End mm_transfert.

  Hint Rewrite mm_transfert_length : length_db.

  Section mm_erase.

    Variables (dst zero : nat).

    Hypothesis (Hdz : dst <> zero).

    Definition mm_erase i := DEC dst (2+i) :: DEC zero i :: nil.

    Fact mm_erase_length i : length (mm_erase i) = 2.
    Proof. reflexivity. Qed.

    Let mm_erase_spec i e x :
           e⇢dst = x
        -> e⇢zero = 0
        -> exists e', e' ⋈  e⦃dst⇠0⦄
                   /\ (i,mm_erase i) // (i,e) -+> (2+i,e').
    Proof.
      unfold mm_erase.
      revert e.
      induction x as [ | x IHx ]; intros e H1 H2.
      + exists e; split.
        * intros j; dest j dst.
        * mm env DEC 0 with dst (2+i).
          mm env stop; f_equal; auto.
      + destruct IHx with (e := e⦃dst⇠x⦄)
          as (e' & H4 & H5); rew env.
        exists e'; split.
        * intros j; rewrite H4; dest j dst.
        * mm env DEC S with dst (2+i) x.
          mm env DEC 0 with zero i; rew env.
          apply sss_progress_compute; auto.
    Qed.

    Fact mm_erase_progress i e : 
           e⇢zero = 0
        -> exists e', e' ⋈  e⦃dst⇠0⦄
                  /\ (i,mm_erase i) // (i,e) -+> (2+i,e').
    Proof.
      intros H1.
      destruct mm_erase_spec with (e := e) (i := i) (x := e⇢dst)
        as (e' & H3 & H4); auto.
      exists e'; split; auto.
    Qed.

  End mm_erase.

  Hint Rewrite mm_erase_length : length_db.

  Opaque mm_erase.

  Section mm_list_erase.

    Variable (zero : nat).

    Fixpoint mm_list_erase ll i := 
      match ll with
        | nil     => nil
        | dst::ll => mm_erase dst zero i ++ mm_list_erase ll (2+i)
      end.

    Fact mm_list_erase_length ll i : length (mm_list_erase ll i) = 2*length ll.
    Proof.
      revert i; induction ll as [ | dst ll IH ]; simpl; intros i; rew length; auto.
      rewrite IH; ring.
    Qed.

    Fact mm_list_erase_compute ll i e : 
            Forall (fun x => x <> zero) ll 
         -> e⇢zero = 0
         -> exists e', (forall x,   In x ll -> e'⇢x = 0)
                    /\ (forall x, ~ In x ll -> e'⇢x = e⇢x)
                    /\ (i,mm_list_erase ll i) // (i,e) ->> (2*length ll+i,e').
    Proof.
      intros H; revert H i e.
      induction 1 as [ | dst ll H1 H2 IH2 ]; intros i e H3.
      + simpl; exists e; repeat split; try tauto; mm env stop.
      + destruct mm_erase_progress with (dst := dst) (zero := zero) (i := i) (e := e)
          as (e1 & H4 & H5); auto.
        destruct IH2 with (i := 2+i) (e := e1) as (e2 & H6 & H7 & H8).
        { rewrite H4; rew env. }
        exists e2; split; [ | split ].
        * intros x [ H | H ]; subst; auto.
          destruct in_dec with (1 := eq_nat_dec) (a := x) (l := ll) as [ H9 | H9 ]; auto.
          rewrite H7; auto; rewrite H4; rew env.
        * simpl; intros x Hx.
          rewrite H7, H4; try tauto.
          dest x dst; destruct Hx; auto.
        * apply sss_compute_trans with (2+i,e1).
          - apply sss_progress_compute.
            simpl; revert H5; apply subcode_sss_progress; auto.
          - replace (2*length (dst::ll)+i) with (2*length ll+(2+i)) by (rew length; omega).
            revert H8; simpl; apply subcode_sss_compute; auto.
            subcode_tac; rewrite <- app_nil_end; auto.
    Qed.

  End mm_list_erase.

  Hint Rewrite mm_list_erase_length : length_db.

  Section mm_multi_erase.

    Variables (dst zero k : nat).

    Definition mm_multi_erase := mm_list_erase zero (list_an dst k).

    Fact mm_multi_erase_length i : length (mm_multi_erase i) = 2*k.
    Proof. unfold mm_multi_erase; rew length; auto. Qed.

    Hypothesis (Hdz : dst+k <= zero).

    Fact mm_multi_erase_compute i e :
                    e⇢zero = 0
      -> exists e', (forall j, dst <= j < k+dst -> e'⇢j = 0)
                 /\ (forall j, ~ dst <= j < k+dst -> e'⇢j = e⇢j)
                 /\ (i,mm_multi_erase i) // (i,e) ->> (2*k+i,e').
    Proof.
      intros H; unfold mm_multi_erase.
      destruct mm_list_erase_compute 
        with (zero := zero) (ll := list_an dst k) (i := i) (e := e)
        as (e' & H1 & H2 & H3); auto.
      * rewrite Forall_forall; intros j; rewrite list_an_spec; intros; omega.
      * rew length in H3; exists e'; msplit 2; auto. 
        + intros; apply H1, list_an_spec; omega.
        + intros; apply H2; rewrite list_an_spec; omega.
    Qed.

  End mm_multi_erase.

  Hint Rewrite mm_multi_erase_length : length_db.

  Section mm_dup.

    Variables (src dst tmp zero : nat).

    Hypothesis (Hsd : src <> dst) (Hst : src <> tmp) (Hsz : src <> zero) 
               (Hdt : dst <> tmp) (Hdz : dst <> zero)
               (Htz : tmp <> zero).

    Definition mm_dup i := DEC src (4+i) :: INC dst :: INC tmp :: DEC zero i :: nil.

    Fact mm_dup_length i : length (mm_dup i) = 4.
    Proof. reflexivity. Qed.

    Let mm_dup_spec i e k x y :  
           e⇢src = k
        -> e⇢dst = x
        -> e⇢tmp = y
        -> e⇢zero = 0
        -> exists e', e' ⋈  e⦃src⇠0⦄⦃dst⇠k+x⦄⦃tmp⇠k+y⦄
                   /\ (i,mm_dup i) // (i,e) -+> (4+i,e').
    Proof.
      unfold mm_dup.
      revert e x y.
      induction k as [ | k IHk ]; intros e x y H1 H2 H3 H4.
      + exists e; split.
        * intros j; dest j src; dest j dst; dest j tmp.
        * mm env DEC 0 with src (4+i).
          mm env stop; f_equal; auto.
      + destruct IHk with (e := e⦃src⇠k⦄⦃dst⇠1+x⦄⦃tmp⇠1+y⦄) (x := 1+x) (y := 1+y)
          as (e' & H5 & H6); rew env.
        exists e'; split.
        * intros j; rewrite H5.
          dest j tmp; try omega.
          dest j dst; try omega.
          dest j src.
        * mm env DEC S with src (4+i) k.
          mm env INC with dst.
          mm env INC with tmp.
          mm env DEC 0 with zero i; rew env.
          rewrite H2, H3.
          apply sss_progress_compute; auto.
    Qed.

    Fact mm_dup_progress i e : 
           e⇢dst = 0
        -> e⇢tmp = 0
        -> e⇢zero = 0
        -> exists e', e' ⋈  e⦃src⇠0⦄⦃dst⇠(e⇢src)⦄⦃tmp⇠(e⇢src)⦄
                  /\ (i,mm_dup i) // (i,e) -+> (4+i,e').
    Proof.
      intros H1 H2 H3.
      destruct mm_dup_spec with (e := e) (x := 0) (y := 0) (i := i) (k := e⇢src)
        as (e' & H4 & H5); auto.
      exists e'; split; auto.
      intros j; rewrite H4, plus_comm; auto.
    Qed.

  End mm_dup.

  Hint Rewrite mm_dup_length : length_db.

  Section mm_copy.

    Variables (src dst tmp zero : nat).

    Hypothesis (Hsd : src <> dst) (Hst : src <> tmp) (Hsz : src <> zero) 
               (Hdt : dst <> tmp) (Hdz : dst <> zero)
               (Htz : tmp <> zero).

    Definition mm_copy i := mm_erase dst zero i
                         ++ mm_transfert src tmp zero (2+i) 
                         ++ mm_dup tmp src dst zero (5+i).

    Fact mm_copy_length i : length (mm_copy i) = 9.
    Proof. reflexivity. Qed.

    Fact mm_copy_progress i e : 
           e⇢tmp = 0
        -> e⇢zero = 0
        -> exists e', e' ⋈  e⦃dst⇠(e⇢src)⦄
                  /\ (i,mm_copy i) // (i,e) -+> (9+i,e').
    Proof.
      intros H0 H1.
      unfold mm_copy.
      destruct mm_erase_progress with (1 := Hdz) (i := i) (e := e)
        as (e0 & H2 & H3); auto.
      destruct mm_transfert_progress 
        with (src := src) (dst := tmp) (zero := zero) (i := 2+i) (e := e0)
        as (e1 & H4 & H5); auto.
      1,2: rewrite H2; rew env.
      destruct mm_dup_progress 
        with (src := tmp) (dst := src) (tmp := dst) (zero := zero) (i := 5+i) (e := e1)
        as (e2 & H6 & H7); auto.
      1,2,3: rewrite H4; rew env; rewrite H2; rew env.
      exists e2; split.
      * intros j. 
        rewrite H6; dest j dst.
        - rewrite H4; rew env.
          rewrite H2; rew env. 
        - dest j src.
          + rewrite H4; rew env.
            rewrite H2; rew env.
          + dest j tmp. 
            rewrite H4; rew env.
            rewrite H2; rew env.
      * apply sss_progress_trans with (2+i,e0).
        { revert H3; apply subcode_sss_progress; auto. }
        apply sss_progress_trans with (5+i,e1).
        { revert H5; apply subcode_sss_progress; auto. }
        { revert H7; apply subcode_sss_progress; auto. }
    Qed.

  End mm_copy.

  Hint Rewrite mm_copy_length : length_db.

  Section mm_multi_copy.

    Variables (tmp zero : nat).

    Fixpoint mm_multi_copy k src dst i :=
      match k with 
        | 0   => nil
        | S k => mm_copy src dst tmp zero i ++ mm_multi_copy k (S src) (S dst) (9+i)
      end.

    Fact mm_multi_copy_length k src dst i : length (mm_multi_copy k src dst i) = 9*k.
    Proof.
      revert src dst i; induction k as [ | k IHk ]; intros src dst i; simpl; auto.
      rew length; rewrite IHk; omega.
    Qed.

    Fact mm_multi_copy_compute k src dst i e :
            k+src <= dst
         -> k+dst <= tmp
         -> k+dst <= zero 
         -> tmp <> zero
         -> e⇢tmp = 0
         -> e⇢zero = 0
         -> exists e', (forall j, j < k -> e'⇢(j+dst) = e⇢(j+src))
                    /\ (forall j, ~ dst <= j < k+dst -> e'⇢j = e⇢j)
                    /\ (i,mm_multi_copy k src dst i) // (i,e) ->> (9*k+i,e').
    Proof.
      revert src dst i e; induction k as [ | k IHk ]; intros src dst i e; intros H1 H2 H3 H4 H5 H6.
      + exists e; split; [ | split ]; try (intros; omega).
        mm env stop.
      + destruct (@mm_copy_progress src dst tmp zero) with (i := i) (e := e)
          as (e1 & G1 & G2); try omega.
        destruct (IHk (S src) (S dst) (9+i)) with (e := e1) 
          as (e2 & G3 & G4 & G5); try omega.
        { rewrite G1; assert (dst <> tmp); try omega; rew env. }
        { rewrite G1; assert (dst <> zero); try omega; rew env. }
        exists e2; split; [ | split ].
        * intros [ | j ] Hj.
          - rewrite G4; try omega; simpl; rewrite G1; rew env.
          - replace (S j + dst) with (j+S dst) by omega.
            replace (S j + src) with (j+S src) by omega.
            rewrite G3; try omega.
            rewrite G1.
            assert (dst <> j+S src) by omega; rew env.
        * intros j Hj.
          rewrite G4; try omega.
          rewrite G1.
          assert (j <> dst) by omega; rew env.
        * unfold mm_multi_copy; fold mm_multi_copy. 
          apply sss_compute_trans with (9+i,e1).
          - apply sss_progress_compute.
            revert G2; apply subcode_sss_progress; auto.
          - replace (9*S k+i) with (9*k+(9+i)) by omega.
            revert G5; apply subcode_sss_compute.
            subcode_tac; rewrite <- app_nil_end; auto.
    Qed.

  End mm_multi_copy.

  Hint Rewrite mm_multi_copy_length : length_db.

  Section mm_set.

    Variables (dst zero : nat) (Hdz : dst <> zero).

    Let mm_incs : nat -> list (mm_instr nat) :=
      fix loop n := match n with
        | 0   => nil
        | S n => INC dst :: loop n
      end.

    Let mm_incs_length n : length (mm_incs n) = n.
    Proof. induction n; simpl; f_equal; auto. Qed.

    Let mm_incs_spec i e n :
      exists e', e' ⋈  e⦃dst⇠(n+(e⇢dst))⦄
              /\ (i,mm_incs n) // (i,e) ->> (n+i,e').
    Proof.
      revert i e; induction n as [ | n IHn ]; intros i e; simpl.
      + exists e; split.
        * intros j; dest j dst.
        * mm env stop.
      + destruct (IHn (1+i) (e⦃dst⇠1+(e⇢dst)⦄)) as (e' & H1 & H2).
        exists e'; split.
        * intros j; rewrite H1; dest j dst.
        * mm env INC with dst.
          replace (S (n+i)) with (n+(1+i)) by omega.
          revert H2; apply subcode_sss_compute.
          subcode_tac; simpl; rewrite <- app_nil_end; auto.
    Qed.

    Definition mm_set n i := mm_erase dst zero i ++ mm_incs n.

    Fact mm_set_length n i : length (mm_set n i) = 2+n.
    Proof.
      unfold mm_set; rew length; rewrite mm_incs_length; auto.
    Qed.

    Fact mm_set_progress n i e :
            e⇢zero = 0
         -> exists e', e' ⋈  e⦃dst⇠n⦄
                   /\ (i,mm_set n i) // (i,e) -+> (2+n+i,e').
    Proof.
      intros H; unfold mm_set.
      destruct (@mm_erase_progress _ _ Hdz i _ H) as (e1 & H1 & H2).
      destruct (mm_incs_spec (2+i) e1 n) as (e2 & H3 & H4).
      exists e2; split.
      + intros j; rewrite H3, H1.
        dest j dst; rewrite H1; rew env.
      + apply sss_progress_compute_trans with (2+i,e1).
        * revert H2; apply subcode_sss_progress; auto.
        * replace (2+n+i) with (n+(2+i)) by omega.
          revert H4; apply subcode_sss_compute; auto.
          subcode_tac; rewrite <- app_nil_end; auto.
    Qed.

  End mm_set.

End mm_env_utils.

Hint Rewrite mm_set_length mm_transfert_length mm_erase_length
             mm_list_erase_length mm_multi_erase_length
             mm_dup_length mm_copy_length mm_multi_copy_length
             mm_set_length : length_db.
