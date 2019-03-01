(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

Require Import utils pos vec gcd.
Require Import subcode sss mm2_defs.

Set Implicit Arguments.

Tactic Notation "rew" "length" := autorewrite with length_db.

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).

Local Notation "P // s -[ k ]-> t" := (sss_steps (@mm2_sss _) P k s t).
Local Notation "P // s -+> t" := (sss_progress (@mm2_sss _) P s t).
Local Notation "P // s ->> t" := (sss_compute (@mm2_sss _) P s t).
Local Notation "P // s ↓" := (sss_terminates (@mm2_sss _) P s). 

(** Utils for FRACTRAN with two counter *)

Section Minsky_Machine_alt_utils.

  Variable (n : nat).
  
  Ltac dest x y := destruct (pos_eq_dec x y) as [ | ]; [ subst x | ]; rew vec.

  Hint Resolve subcode_refl.

  Section mm2_null.

    (* Empty oone register/counter *)

    Variable (dst : pos n).

    Definition mm2_null i := DEC dst i :: nil.

    Fact mm2_null_length i : length (mm2_null i) = 1.
    Proof. auto. Qed.
    
    Let mm2_null_spec i k v w : v#>dst = k 
                             -> w = v[0/dst]
                             -> (i,mm2_null i) // (i,v) -+> (1+i,w).
    Proof.
      unfold mm2_null.
      revert v w.
      induction k as [ | k IHk ]; intros v w H1 H2; subst w.
      + mm2 sss DEC 0 with dst i.
        mm2 sss stop; f_equal.
        apply vec_pos_ext; intros z; dest z dst.
      + mm2 sss DEC S with dst i k.
        apply sss_progress_compute.
        apply IHk; rew vec.
    Qed.

    Fact mm2_null_progress i v st : 
             st = (1+i,v[0/dst])
          -> (i,mm2_null i) // (i,v) -+> st.
    Proof.
      intros; subst.
      apply mm2_null_spec with (1 := eq_refl); auto.
    Qed.

  End mm2_null.

  Hint Rewrite mm2_null_length : length_db.

  Section mm2_transfert.

    (* Added the content of src to dst while emptying src *)

    Variables (src dst : pos n) (Hsd : src <> dst).

    Definition mm2_transfert i := INC dst :: DEC src i :: DEC dst (3+i) :: nil.

    Fact mm2_transfert_length i : length (mm2_transfert i) = 3.
    Proof. reflexivity. Qed.

    Let mm2_transfert_spec i v w k x :  v#>src = k
                                     -> v#>dst = x
                                     -> w = v[0/src][(1+k+x)/dst]
                                     -> (i,mm2_transfert i) // (i,v) -+> (2+i,w).
    Proof.
      unfold mm2_transfert.
      revert v w x.
      induction k as [ | k IHk ]; intros v w x H1 H2 H3; subst w.
      + mm2 sss INC with dst.
        mm2 sss DEC 0 with src i; rew vec.
        mm2 sss stop; f_equal; auto.
        apply vec_pos_ext; intros z; dest z dst; dest z src.
      + mm2 sss INC with dst.
        mm2 sss DEC S with src i k; rew vec.
        apply sss_progress_compute, IHk with (x := 1+x); rew vec.
        apply vec_pos_ext; intros p.
        dest p dst; try omega; dest p src.
    Qed.

    Fact mm2_transfert_progress i v st : 
           st = (3+i,v[0/src][((v#>src)+(v#>dst))/dst])
        -> (i,mm2_transfert i) // (i,v) -+> st.
    Proof.
      intros ?; subst.
      apply sss_progress_trans with (2+i, v[0/src][(1+(v#>src)+(v#>dst))/dst]).
      + apply mm2_transfert_spec with (1 := eq_refl) (2 := eq_refl); auto.
      + unfold mm2_transfert.
        mm2 sss DEC S with dst (3+i) ((v#>src)+(v#>dst)); rew vec.
        mm2 sss stop.
    Qed.

  End mm2_transfert.

  Hint Rewrite mm2_transfert_length : length_db.

  Section mm2_incs.

    (* Add a constant value k to dst *)

    Variable (dst : pos n).

    Fixpoint mm2_incs k := 
      match k with 
        | 0   => nil
        | S k => INC dst :: mm2_incs k
      end.

    Fact mm2_incs_length k : length (mm2_incs k) = k.
    Proof. induction k; simpl; f_equal; auto. Qed.

    Fact mm2_incs_compute k i v st :
             st = (k+i,v[(k+(v#>dst))/dst])
          -> (i,mm2_incs k) // (i,v) ->> st.
    Proof.
      revert i v st; induction k as [ | k IHk ]; intros i v st ?; subst.
      + mm2 sss stop; f_equal; auto.
        apply vec_pos_ext; intros p; dest p dst.
      + simpl; mm2 sss INC with dst.
        apply subcode_sss_compute with (P := (1+i,mm2_incs k)); auto.
        { subcode_tac; rewrite <- app_nil_end; auto. }
        apply IHk; f_equal; try omega.
        apply vec_pos_ext; intros p; dest p dst.
    Qed.

  End mm2_incs.

  Section mm2_decs.

    (* "mm2_dec dst p q k" at i 

        removes constant k to dst:

        if dst < k, dst ends up empty and jump to q
        if k <= dst, dst is decremented by k and jump to p 

      *)

    Variable (dst : pos n) (p q : nat).

    Fixpoint mm2_decs k i := 
      match k with 
        | 0   => INC dst :: DEC dst p :: nil
        | S k => DEC dst (3+i) :: INC dst :: DEC dst q :: mm2_decs k (3+i)
      end.

    Fact mm2_decs_length k i : length (mm2_decs k i) = 2+3*k.
    Proof.
      revert i; induction k as [ | ? IHk ]; intros i; simpl; auto.
      rewrite IHk; omega.
    Qed.

    Let mm2_decs_spec_lt k i v w : 
            v#>dst < k 
         -> w = v[0/dst]
         -> (i,mm2_decs k i) // (i,v) -+> (q,w).
    Proof.
      revert i v w; induction k as [ | k IHk ]; intros i v w H1 ?; subst w.
      + omega.
      + unfold mm2_decs; fold mm2_decs.
        case_eq (v#>dst).
        * intros H2.
          mm2 sss DEC 0 with dst (3+i).
          mm2 sss INC with dst.
          mm2 sss DEC S with dst q (v#>dst); rew vec.
          mm2 sss stop; f_equal.
          apply vec_pos_ext; intros x; dest x dst.
        * intros d Hd.
          mm2 sss DEC S with dst (3+i) d.
          apply subcode_sss_compute with (P := (3+i,mm2_decs k (3+i))); auto.
          { subcode_tac; rewrite <- app_nil_end; auto. }
          apply sss_progress_compute, IHk; rew vec; try omega.
    Qed.

    Let mm2_decs_spec_le k i v w : 
            k <= v#>dst 
         -> w = v[((v#>dst)-k)/dst]
         -> (i,mm2_decs k i) // (i,v) -+> (p,w).
    Proof.
      revert i v w; induction k as [ | k IHk ]; intros i v w H1 ?; subst w.
      + simpl.
        mm2 sss INC with dst.
        mm2 sss DEC S with dst p (v#>dst); rew vec.
        mm2 sss stop; f_equal.
        apply vec_pos_ext; intros x; dest x dst; try omega.
      + unfold mm2_decs; fold mm2_decs.
        mm2 sss DEC S with dst (3+i) ((v#>dst) - 1); try omega.
        apply subcode_sss_compute with (P := (3+i,mm2_decs k (3+i))); auto.
        { subcode_tac; rewrite <- app_nil_end; auto. }
        apply sss_progress_compute, IHk; rew vec; try omega.
        apply vec_pos_ext; intros x; dest x dst; omega.
    Qed.

    Fact mm2_decs_lt_progress k i v st :
             v#>dst < k 
          -> st = (q,v[0/dst])
          -> (i,mm2_decs k i) // (i,v) -+> st.
    Proof.
      intros H1 ?; subst st.
      apply mm2_decs_spec_lt; auto.
    Qed.

    Fact mm2_decs_le_progress k i v st :
             k <= v#>dst 
          -> st = (p,v[((v#>dst)-k)/dst])
          -> (i,mm2_decs k i) // (i,v) -+> st.
    Proof.
      intros H1 ?; subst st.
      apply mm2_decs_spec_le; auto.
    Qed.

  End mm2_decs.

  Section mm2_decs_copy.

    (* Same as mm2_decs except that the quantity
       removed from dst is transfered into tmp *)

    Variable (dst tmp : pos n) (Hdt : dst <> tmp) (p q : nat).

    Fixpoint mm2_decs_copy k i := 
      match k with 
        | 0   => INC dst :: DEC dst p :: nil
        | S k => DEC dst (3+i) :: INC dst :: DEC dst q :: INC tmp :: mm2_decs_copy k (4+i)
      end.

    Fact mm2_decs_copy_length k i : length (mm2_decs_copy k i) = 2+4*k.
    Proof.
      revert i; induction k as [ | ? IHk ]; intros i; simpl; auto.
      rewrite IHk; omega.
    Qed.

    Let mm2_decs_copy_spec_lt k i v w : 
            v#>dst < k 
         -> w = v[0/dst][((v#>dst)+(v#>tmp))/tmp]
         -> (i,mm2_decs_copy k i) // (i,v) -+> (q,w).
    Proof.
      revert i v w; induction k as [ | k IHk ]; intros i v w H1 ?; subst w.
      + omega.
      + unfold mm2_decs_copy; fold mm2_decs_copy.
        case_eq (v#>dst).
        * intros H2.
          mm2 sss DEC 0 with dst (3+i).
          mm2 sss INC with dst.
          mm2 sss DEC S with dst q (v#>dst); rew vec.
          mm2 sss stop; f_equal.
          apply vec_pos_ext; intros x; dest x tmp; dest x dst.
        * intros d Hd.
          mm2 sss DEC S with dst (3+i) d.
          mm2 sss INC with tmp.
          apply subcode_sss_compute with (P := (4+i,mm2_decs_copy k (4+i))); auto.
          { subcode_tac; rewrite <- app_nil_end; auto. }
          apply sss_progress_compute; rewrite plus_assoc.
          apply IHk; rew vec; try omega.
          apply vec_pos_ext; intros x; dest x tmp; try omega; dest x dst.
    Qed.

    Let mm2_decs_copy_spec_le k i v w : 
            k <= v#>dst 
         -> w = v[((v#>dst)-k)/dst][(k+(v#>tmp))/tmp]
         -> (i,mm2_decs_copy k i) // (i,v) -+> (p,w).
    Proof.
      revert i v w; induction k as [ | k IHk ]; intros i v w H1 ?; subst w.
      + simpl.
        mm2 sss INC with dst.
        mm2 sss DEC S with dst p (v#>dst); rew vec.
        mm2 sss stop; f_equal.
        apply vec_pos_ext; intros x; dest x dst; try omega; dest x tmp.
      + unfold mm2_decs_copy; fold mm2_decs_copy.
        mm2 sss DEC S with dst (3+i) ((v#>dst) - 1); try omega.
        mm2 sss INC with tmp.
        apply subcode_sss_compute with (P := (4+i,mm2_decs_copy k (4+i))); auto.
        { subcode_tac; rewrite <- app_nil_end; auto. }
        apply sss_progress_compute, IHk; rew vec; try omega.
        apply vec_pos_ext; intros x; dest x tmp; try omega; dest x dst; omega.
    Qed.

    Fact mm2_decs_copy_lt_progress k i v st :
             v#>dst < k 
          -> st = (q,v[0/dst][((v#>dst)+(v#>tmp))/tmp])
          -> (i,mm2_decs_copy k i) // (i,v) -+> st.
    Proof.
      intros H1 ?; subst st.
      apply mm2_decs_copy_spec_lt; auto.
    Qed.

    Fact mm2_decs_copy_le_progress k i v st :
             k <= v#>dst 
          -> st = (p,v[((v#>dst)-k)/dst][(k+(v#>tmp))/tmp])
          -> (i,mm2_decs_copy k i) // (i,v) -+> st.
    Proof.
      intros H1 ?; subst st.
      apply mm2_decs_copy_spec_le; auto.
    Qed.

  End mm2_decs_copy.

  Hint Rewrite mm2_incs_length mm2_decs_copy_length : length_db.
 
  Section mm2_mult_cst.

    (* dst <- k*src+dst *)

    Variable (src dst : pos n) (Hsd : src <> dst) (k i : nat).

    Definition mm2_mult_cst :=
           DEC src (3+i) :: INC src :: DEC src (5+k+i) 
        :: mm2_incs dst (S k) ++ DEC dst i :: nil. 

    Fact mm2_mult_cst_length : length mm2_mult_cst = 5+k.
    Proof. unfold mm2_mult_cst; rew length; omega. Qed.

    Let mm2_mult_cst_spec x v st :
             v#>src = x
          -> st = (5+k+i,v[0/src][(x*k+(v#>dst))/dst])
          -> (i,mm2_mult_cst) // (i,v) -+> st.
    Proof.
      unfold mm2_mult_cst.
      revert v st; induction x as [ | x IHx ]; intros v st Hv ?; subst.
      + mm2 sss DEC 0 with src (3+i).
        mm2 sss INC with src.
        mm2 sss DEC S with src (5+k+i) 0; rew vec.
        mm2 sss stop; f_equal.
        apply vec_pos_ext; intros y; dest y dst; omega.
      + mm2 sss DEC S with src (3+i) x.
        apply sss_compute_trans with (4+k+i,v[x/src][(S k+(v#>dst))/dst]).
        * apply subcode_sss_compute with (P := (3+i,mm2_incs dst (S k))); auto.
          apply mm2_incs_compute; f_equal; try omega.
          apply vec_pos_ext; intros y; dest y dst; omega.
        * mm2 sss DEC S with dst i (k+(v#>dst)); rew vec.
          apply sss_progress_compute, IHx; rew vec; f_equal.
          apply vec_pos_ext; intros y; dest y dst; try ring.
          dest y src.
    Qed.

    Fact mm2_mult_cst_progress v st :
             st = (5+k+i,v[0/src][(k*(v#>src)+(v#>dst))/dst])
          -> (i,mm2_mult_cst) // (i,v) -+> st.
    Proof.
      intros ?; subst.
      apply mm2_mult_cst_spec with (1 := eq_refl); do 2 f_equal.
      ring.
    Qed.

  End mm2_mult_cst.

  Hint Rewrite mm2_mult_cst_length : length_db.
  
  Section mm2_mod_cst.

    (* test whether k divides src and transfer of src into dst *)

    Variable (src dst : pos n) (Hsd : src <> dst) (p q k i : nat).

    Definition mm2_mod_cst :=
            DEC src (3+i)
         :: INC dst
         :: DEC dst p
         :: INC src
         :: mm2_decs_copy src dst i q k (4+i).

    Fact mm2_mod_cst_length : length mm2_mod_cst = 6+4*k.
    Proof. unfold mm2_mod_cst; rew length; omega. Qed.

    (* This is of no use when k = 0 *)

    Hypothesis (Hk : 0 < k).

    Let mm2_mod_cst_spec_0 v :
           v#>src = 0
        -> (i,mm2_mod_cst) // (i,v) -+> (p,v).
    Proof.
      intros H; unfold mm2_mod_cst.
      mm2 sss DEC 0 with src (3+i).
      mm2 sss INC with dst.
      mm2 sss DEC S with dst p (v#>dst); rew vec.
      mm2 sss stop.
    Qed.

    Let mm2_mod_cst_spec_1 a b v w :
           v#>src = a*k+b
        -> w = v[b/src][(a*k+(v#>dst))/dst]
        -> (i,mm2_mod_cst) // (i,v) ->> (i,w).
    Proof.
      revert v w; induction a as [ | a IHa ]; intros v w H1 H2; subst w.
      + mm2 sss stop; f_equal.
        simpl in H1; rewrite <- H1; simpl; rew vec.
      + unfold mm2_mod_cst.
        mm2 sss DEC S with src (3+i) (S a*k+b-1).
        { rewrite H1; simpl; generalize (a*k); intro; omega. }
        mm2 sss INC with src.
        apply sss_compute_trans with (i, v[(a*k+b)/src][(k+(v#>dst))/dst]).
        * apply subcode_sss_compute with (P := (4+i,mm2_decs_copy src dst i q k (4+i))); auto.
          { subcode_tac; rewrite <- app_nil_end; auto. }
          apply sss_progress_compute, mm2_decs_copy_le_progress; auto; rew vec.
          { simpl; generalize (a*k); intro; omega. }
          do 3 f_equal; simpl mult; generalize (a*k); intro; omega.
        * apply IHa; rew vec.
          apply vec_pos_ext; intros y; dest y dst; try ring; dest y src.
    Qed.

    Let mm2_mod_cst_spec_2 v w :
           0 < v#>src < k
        -> w = v[0/src][((v#>src)+(v#>dst))/dst]
        -> (i,mm2_mod_cst) // (i,v) -+> (q,w).
    Proof.
      intros H ?; subst; unfold mm2_mod_cst.
      case_eq (v#>src).
      { intros; try omega. }
      intros x Hx.
      mm2 sss DEC S with src (3+i) x.
      mm2 sss INC with src.
      apply subcode_sss_compute with (P := (4+i,mm2_decs_copy src dst i q k (4+i))); auto.
      { subcode_tac; rewrite <- app_nil_end; auto. }
       apply sss_progress_compute, mm2_decs_copy_lt_progress; auto; rew vec; omega.
    Qed.
 
    Fact mm2_mod_cst_divides_progress v a st :
            v#>src = a*k
         -> st = (p,v[0/src][((v#>src)+(v#>dst))/dst])
         -> (i,mm2_mod_cst) // (i,v) -+> st.
    Proof.
      intros H1 ?; subst st.
      apply sss_compute_progress_trans with (i,v[0/src][((v#>src)+(v#>dst))/dst]).
      + apply mm2_mod_cst_spec_1 with (a := a) (b := 0); try omega.
        rewrite <- H1; auto.
      + apply mm2_mod_cst_spec_0; rew vec.
    Qed.

    Fact mm2_mod_cst_not_divides_progress v a b st :
            v#>src = a*k+b
         -> 0 < b < k
         -> st = (q,v[0/src][((v#>src)+(v#>dst))/dst])
         -> (i,mm2_mod_cst) // (i,v) -+> st.
    Proof.
      intros H1 H2 ?; subst st.
      apply sss_compute_progress_trans with (i,v[b/src][(a*k+(v#>dst))/dst]).
      + apply mm2_mod_cst_spec_1 with (a := a) (b := b); try omega; auto.
      + apply mm2_mod_cst_spec_2; rew vec.
        apply vec_pos_ext; intros y; dest y dst; try omega; dest y src.
    Qed.
  
  End mm2_mod_cst.

  Hint Rewrite mm2_decs_length mm2_mod_cst_length : length_db.

  Section mm2_div_cst.

    (* Division by a constant *)

    Variable (src dst : pos n) (Hsd : src <> dst) (k i : nat).

    Let p := (2+3*k+i).
    Let q := (5+3*k+i).

    Definition mm2_div_cst := 
         mm2_decs src p q k i ++ INC dst :: INC src :: DEC src i :: nil.

    Fact mm2_div_cst_length : length mm2_div_cst = 5+3*k.
    Proof. unfold mm2_div_cst; rew length; omega. Qed.

    Hypothesis (Hk : 0 < k).

    Let mm2_div_cst_spec a v w :
           v#>src = a*k
        -> w = v[0/src][(a+(v#>dst))/dst]
        -> (i, mm2_div_cst) // (i,v) -+> (q,w).
    Proof.
      unfold mm2_div_cst; revert v w; induction a as [ | a IHa ]; intros v w H1 ?; subst w.
      + apply subcode_sss_progress with (P := (i,mm2_decs src p q k i)); auto.
        apply mm2_decs_lt_progress; try omega.
        f_equal; simpl.
        apply vec_pos_ext; intros y; dest y dst.
      + apply sss_progress_trans with (p,v[(a*k)/src]).
        * apply subcode_sss_progress with (P := (i,mm2_decs src p q k i)); auto.
          apply mm2_decs_le_progress.
          - rewrite H1; simpl; generalize (a*k); intro; omega.
          - f_equal.
            apply vec_pos_ext; intros y; dest y dst; dest y src.
            rewrite H1; simpl; generalize (a*k); intro; omega.
        * unfold p.
          mm2 sss INC with dst.
          mm2 sss INC with src.
          mm2 sss DEC S with src i (a*k); rew vec.
          apply sss_progress_compute, IHa; rew vec.
          apply vec_pos_ext; intros y; dest y dst; try omega; dest y src.
    Qed.

    Fact mm2_div_cst_progress a v st :
            v#>src = a*k
         -> st = (q,v[0/src][(a+(v#>dst))/dst])
         -> (i, mm2_div_cst) // (i,v) -+> st.
    Proof.
      intros H1 H2; subst st; apply mm2_div_cst_spec with (1 := H1); auto.
    Qed.

  End mm2_div_cst.

  Hint Rewrite mm2_div_cst_length : length_db.

 
End Minsky_Machine_alt_utils.
