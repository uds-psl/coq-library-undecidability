(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Bool.

From Undecidability.Shared.Libs.DLW 
  Require Import utils list_bool pos vec subcode sss compiler_correction.

Check gen_compiler_correction.

From Undecidability.StackMachines.BSM 
  Require Import bsm_defs.

From Undecidability.TM
  Require Import SBTM pctm_defs.

Import PCTMNotations SBTMNotations.

Set Implicit Arguments.

Set Default Proof Using "Type".

Tactic Notation "rew" "length" := autorewrite with length_db.

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).

Local Notation "P // s -[ k ]-> t" := (sss_steps (@bsm_sss _) P k s t).
Local Notation "P // s ->> t" := (sss_compute (@bsm_sss _) P s t).
Local Notation "P // s -+> t" := (sss_progress (@bsm_sss _) P s t) (at level 70, no associativity).

Section PCTM_BSM2_compiler.

  Let x : pos 2 := pos0.
  Let y : pos 2 := pos1.

  Let Hxy : x <> y. Proof. easy. Qed.

  Section jump.

   Variable (i j : nat).

   Definition jump := PUSH x Zero :: POP x j j :: nil.

   Fact jump_length : length jump = 2.
   Proof. reflexivity. Qed.

   Fact jump_spec v w : v = w -> (i,jump) // (i,v) -+> (j,w).
   Proof.
     unfold jump; intros <-.
     bsm sss PUSH with x Zero.
     bsm sss POP zero with x j j (v#>x); rew vec.
     bsm sss stop.
   Qed.

   Fact jump_spec' v w : v = w -> (i,jump) // (i,v) ->> (j,w).
   Proof. intros; apply sss_progress_compute, jump_spec; auto. Qed.

  End jump.

  Hint Rewrite jump_length : length_db.
  Hint Resolve jump_spec jump_spec' : core.

  Section read_head.

    Variable (i : nat) (j : nat).
    
    (* Code for reading the head *)

    Definition read_head := 
      POP y (4+i) j :: 
      PUSH y One :: 
      jump (7+i) ++
      PUSH y Zero ::
      jump j.

    Fact read_head_length : length read_head = 7.
    Proof. reflexivity. Qed.

    Fact read_head_Zero v l :
           v#>y = Zero::l -> (i,read_head) // (i,v) -+> (j,v).
    Proof.
      unfold read_head; intros H.
      bsm sss POP zero with y (4+i) j l.
      bsm sss PUSH with y Zero.
      apply subcode_sss_compute_trans with (P := (5+i,jump j))
                                           (st2 := (j,v)); auto.
      2: bsm sss stop.
      apply jump_spec'.
      rew vec; rewrite <- H; rew vec.
    Qed.

    Fact read_head_One v l :
           v#>y = One::l -> (i,read_head) // (i,v) -+> (7+i,v).
    Proof.
      unfold read_head; intros H.
      bsm sss POP one with y (4+i) j l.
      bsm sss PUSH with y One.
      apply subcode_sss_compute_trans with (P := (2+i,jump (7+i)))
                                           (st2 := (7+i,v)); auto.
      2: bsm sss stop.
      apply jump_spec'.
      rew vec; rewrite <- H; rew vec.
    Qed.

    Fact read_head_spec v (b : bool) l w k :
           v = w 
        -> v#>y = b::l 
        -> k = (if b then 7+i else j)
        -> (i,read_head) // (i,v) -+> (k,w).
    Proof.
      intros <- H ->.
      destruct b.
      + eapply read_head_One; eauto.
      + eapply read_head_Zero; eauto.
    Qed.

  End read_head.

  Hint Rewrite read_head_length : length_db.
  Hint Resolve read_head_spec : core.

  Section ovwrite_head.

    Variable (b : bool) (i j : nat).
    
    (* Code for overwriting the head *)

    Definition ovwrite_head := POP y (1+i) (1+i) :: PUSH y b :: jump j.

    Fact ovwrite_head_length : length ovwrite_head = 4.
    Proof. reflexivity. Qed.

    Fact ovwrite_head_1 c l v :
         v#>y = c::l 
      -> (i,ovwrite_head) // (i,v) -+> (1+i,v[l/y]).
    Proof.
      intros H; unfold ovwrite_head; destruct c.
      + bsm sss POP one with y (1+i) (1+i) l; bsm sss stop.
      + bsm sss POP zero with y (1+i) (1+i) l; bsm sss stop.
    Qed.

    Fact ovwrite_head_spec c l v w :
         v#>y = c::l 
      -> w = v[(b::l)/y]
      -> (i,ovwrite_head) // (i,v) -+> (j,w).
    Proof.
      intros H ->.
      apply sss_progress_trans with (1 := ovwrite_head_1 _ H).
      unfold ovwrite_head.
      bsm sss PUSH with y b.
      apply subcode_sss_compute_trans with (P := (2+i,jump j))
                                           (st2 := (j,v[(b::l)/y])); auto.
      2: bsm sss stop.
      apply jump_spec'; rew vec.
    Qed.

  End ovwrite_head.

  Hint Rewrite ovwrite_head_length : length_db.
  Hint Resolve ovwrite_head_spec : core.

  Section to_default.

    Variable (i j : nat).

    Let j' := j.

    Definition to_default :=
      POP y (4+i) (4+i) ::
      PUSH y One ::
      jump j ++
      PUSH y Zero ::
      jump j'.

    Fact to_default_length : length to_default = 7.
    Proof. reflexivity. Qed.

    Definition default_stack (l : list bool) :=
      match l with nil => Zero::nil | _ => l end.

    Fact to_default_spec v w :
           w = v[(default_stack (v#>y))/y]
        -> (i,to_default) // (i,v) ->> (j,w).
    Proof.
      intros ->; unfold to_default.
      case_eq (v#>y); [ intros H | intros [] l H ].
      + bsm sss POP empty with y (4+i) (4+i).
        bsm sss PUSH with y Zero.
        rewrite H.
        apply subcode_sss_compute_trans with (P := (5+i,jump j'))
                                             (st2 := (j,v[(Zero::nil)/y])); auto.
        bsm sss stop.
      + bsm sss POP one with y (4+i) (4+i) l.
        bsm sss PUSH with y One.
        rew vec; simpl default_stack. 
        apply subcode_sss_compute_trans with (P := (2+i,jump j))
                                             (st2 := (j,v[(One::l)/y])); auto.
        bsm sss stop.
      + bsm sss POP zero with y (4+i) (4+i) l.
        bsm sss PUSH with y Zero.
        rew vec; simpl default_stack.
        apply subcode_sss_compute_trans with (P := (5+i,jump j'))
                                             (st2 := (j,v[(Zero::l)/y])); auto.
        bsm sss stop.
    Qed.

  End to_default.

  Hint Rewrite to_default_length : length_db.

  Definition tape_eq_stacks (t : tape) (lft : list bool) (rt : list bool) :=
     match t with (l,b,r) => l = lft /\ b::r = rt end.

  Section move_tape.

    Variable (i j : nat).

    Notation "t '~r' v" := (tape_eq_stacks t (v#>x) (v#>y)) (at level 70).

    (* Code for reading the head *)

    Let j' := j.

    Local Definition mv_left := 
      POP x (11+i) (11+i) :: 
      PUSH y One :: 
      jump j ++
      to_default i i ++ (* dead code to match the size with mv_right *)
      PUSH y Zero ::
      jump j'
      .

    Local Definition mv_right := 
      POP y (4+i) (4+i) :: 
      PUSH x One :: 
      jump (5+i) ++
      PUSH x Zero ::
      to_default (5+i) j ++
      jump j           (* dead code to match the size with mv_left *)
      .

    Fact mv_left_spec t v w : 
          t ~r v
       -> mv go_left t ~r w
       -> (i,mv_left) // (i,v) -+> (j,w).
    Proof using Hxy.
      destruct t as ((l,b),r).
      intros (H1 & H2) H3.
      unfold mv_left.
      destruct l as [ | [] l ].
      + bsm sss POP empty with x (11+i) (11+i).
        bsm sss PUSH with y Zero.
        apply subcode_sss_compute_trans with (P := (12+i,jump j'))
                                           (st2 := (j,w)); auto.
        2: bsm sss stop.
        unfold j'; apply jump_spec'.
        simpl in H3.
        destruct H3 as (H3 & H5).
        apply vec_pos_ext; intros z.
        repeat invert pos z; rew vec.
        * rewrite <- H1; auto.
        * unfold y in *; rew vec; rewrite <- H2; auto.
      + bsm sss POP one with x (11+i) (11+i) l.
        bsm sss PUSH with y One.
        apply subcode_sss_compute_trans with (P := (2+i,jump j))
                                           (st2 := (j,w)); auto.
        2: bsm sss stop.
        apply jump_spec'.
        simpl in H3.
        destruct H3 as (H3 & H5).
        apply vec_pos_ext; intros z.
        unfold x, y in *; repeat invert pos z; rew vec.
        rewrite <- H2; auto.
      + bsm sss POP zero with x (11+i) (11+i) l.
        bsm sss PUSH with y Zero.
        apply subcode_sss_compute_trans with (P := (12+i,jump j'))
                                           (st2 := (j,w)); auto.
        2: bsm sss stop.
        apply jump_spec'.
        simpl in H3.
        destruct H3 as (H3 & H5).
        apply vec_pos_ext; intros z.
        unfold x, y in *; repeat invert pos z; rew vec.
        rewrite <- H2; auto.
    Qed.

    Fact mv_right_spec t v w : 
          t ~r v
       -> mv go_right t ~r w
       -> (i,mv_right) // (i,v) -+> (j,w).
    Proof using Hxy.
      destruct t as ((l,b),r).
      intros (H1 & H2) H3.
      unfold mv_right.
      destruct b.
      + bsm sss POP one with y (4+i) (4+i) r.
        bsm sss PUSH with x One.
        rew vec; rewrite <- H1.
        apply subcode_sss_compute_trans with (P := (2+i,jump (5+i)))
                                           (st2 := (5+i,v[r/y][(One::l)/x])); auto.
        apply subcode_sss_compute with (P := (5+i,to_default (5+i) j)); auto.
        apply to_default_spec.
        rew vec.
        symmetry.
        apply vec_pos_ext; intros z.
        unfold x, y in *; repeat invert pos z; rew vec.
        all: destruct r; simpl in *; destruct H3; auto.
      + bsm sss POP zero with y (4+i) (4+i) r.
        bsm sss PUSH with x Zero.
        rew vec; rewrite <- H1.
        apply subcode_sss_compute with (P := (5+i,to_default (5+i) j)); auto.
        apply to_default_spec.
        rew vec.
        symmetry.
        apply vec_pos_ext; intros z.
        unfold x, y in *; repeat invert pos z; rew vec.
        all: destruct r; simpl in *; destruct H3; auto.
    Qed.

    Definition move_tape d :=
      match d with
        | go_left  => mv_left
        | go_right => mv_right
      end.

    Fact move_tape_length d : length (move_tape d) = 14.
    Proof. destruct d; reflexivity. Qed.

    Fact move_tape_spec d t v w : 
          t ~r v
       -> mv d t ~r w
       -> (i,move_tape d) // (i,v) -+> (j,w).
    Proof using Hxy.
      destruct d; simpl move_tape.
      + apply mv_left_spec.
      + apply mv_right_spec.
    Qed.

  End move_tape.

  Hint Rewrite move_tape_length : length_db.

  Section compiler.

    Let icomp (lnk : nat -> nat) (i : nat) : pctm_instr -> list (bsm_instr 2).
    Proof.
      intros [ d | b | j | j ].
      + exact (move_tape (lnk i) (lnk (1+i)) d).
      + exact (ovwrite_head b (lnk i) (lnk (1+i))).
      + exact (read_head (lnk i) (lnk j)).
      + exact (jump (lnk j)).
    Defined.

    Let ilen : pctm_instr -> nat.
    Proof.
      intros [].
      + exact 14.
      + exact 4.
      + exact 7.
      + exact 2.
    Defined.

    Definition pctm_bsm2_compiler : compiler_t (pctm_sss) (@bsm_sss 2) (fun t v => tape_eq_stacks t (v#>x) (v#>y)).
    Proof.
      apply generic_compiler with icomp ilen.
      + intros ? ? []; simpl icomp; rew length; auto.
      + apply pctm_sss_total'.
      + apply bsm_sss_fun.
      + intros lnk [ d | b | j | j ] i1 v1 i2 v2 w1 H1 H2 H3; simpl icomp.
        * case_eq (mv d v1); intros (l,b) r E.
          exists (l##(b::r)##vec_nil); split.
          - assert (i2 = 1+i1) as -> by (inversion H1; auto).
            apply move_tape_spec with (1 := H3); simpl.
            rewrite E; split; auto.
          - simpl.
            inversion H1; subst; rewrite E; split; auto.
        * case_eq v1; intros (l,c) r E.
          exists (l##(b::r)##vec_nil); split.
          - assert (i2 = 1+i1) as -> by (inversion H1; auto).
            rewrite E in H3; destruct H3 as [ H3 H4 ].
            apply ovwrite_head_spec with c r; auto.
            apply vec_pos_ext; intros z; repeat invert pos z;unfold x, y; rew vec.
          - inversion H1; subst; split; rew vec.
        * case_eq v1; intros (l,c) r E.
          rewrite E in H3; destruct H3 as [ H3 H4 ]. 
          exists w1; split.
          - inversion H1; subst i2 v2.
            apply read_head_spec with (rd v1) r; auto.
            ++ subst; rewrite <- H4; auto.
            ++ destruct (rd v1); auto.
          - inversion H1; subst; split; auto.
        * exists w1; split.
          - inversion H1; subst.
            apply jump_spec; auto.
          - inversion H1; subst; auto.
    Qed.

  End compiler.

End PCTM_BSM2_compiler.

From Undecidability.Synthetic
  Require Import Undecidability ReducibilityFacts.

Theorem PCTM_BSM_reduction : PCTM_HALT ⪯ BSM_HALTING.
Proof.
  generalize (compiler_t_correct_term pctm_bsm2_compiler).
  destruct pctm_bsm2_compiler as [ link code init out sound complete ]; simpl; intros correct.
  apply reduces_dependent; exists.
  intros (P,((l,b),r)).
  set (Q := code (1,P) 1).
  set (w1 := l##(b::r)##vec_nil).
  exists (existT _ 2 (existT _ 1 (existT _ Q w1))); simpl.
  apply correct.
  unfold w1; simpl; auto.
Qed.

Check PCTM_BSM_reduction.