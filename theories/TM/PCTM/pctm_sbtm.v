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
  Require Import utils pos subcode sss.

From Undecidability.Synthetic
  Require Import Undecidability ReducibilityFacts.

From Undecidability.TM 
  Require Import SBTM pctm_defs.

Import ListNotations SBTMNotations PCTMNotations.

Set Implicit Arguments.

Set Default Proof Using "Type".

#[local] Notation "i // s -1> t" := (pctm_sss i s t).
#[local] Notation "P // s -[ k ]-> t" := (sss_steps pctm_sss P k s t).
#[local] Notation "P // s ->> t" := (sss_compute pctm_sss P s t).
#[local] Notation "P // s -+> t" := (sss_progress pctm_sss P s t).
#[local] Notation "P // s ↓" := (sss_terminates pctm_sss P s).

Section helpers.

  (* This is a bit stronger than pos_list_prop *)

  Fact pos_list_split n p : exists l r, pos_list n = l++p::r /\ length l = pos2nat p.
  Proof. 
    induction p as [ n | n p (l & r & H1 & H2) ].
    + exists nil, (map pos_nxt (pos_list n)); auto.
    + exists (pos0::map pos_nxt l), (map pos_nxt r); split; simpl.
      * rewrite H1, map_app; simpl; auto.
      * rewrite map_length, H2; auto.
  Qed.

  Fact Natiter_add a b X (f : X -> X) x : Nat.iter (a+b) f x = Nat.iter a f (Nat.iter b f x).
  Proof. induction a; simpl; f_equal; auto. Qed.

  Fact Natiter_S n X (f : X -> X) x : Nat.iter (S n) f x = Nat.iter n f (f x).
  Proof. 
    replace (S n) with (n+1) by lia.
    rewrite Natiter_add; auto.
  Qed.

  Fact Natiter_fixpoint n X (f : X -> X) x : f x = x -> Nat.iter n f x = x.
  Proof.
    intros H.
    induction n as [ | n IHn ]; simpl; auto.
    rewrite IHn; auto.
  Qed.

End helpers.

Section SBTM_PCTM.

  Section sbtm_op.

    (* if head reads true, write b1, mv d1 and jump j1
       if head reads false, write b0, mv d0 and jump j0 *)

    Variable (i : nat)
       (o0 o1 : bool) (b0 b1 : bool) (d0 d1 : direction) (j0 j1 k : nat).

    Definition sbtm_op :=
      (* 0+i *) JZ (5+i) ::
      (* 1+i *) JMP (if o1 then 2+i else k) ::
      (* 2+i *) WR b1 ::
      (* 3+i *) MV d1 ::
      (* 4+i *) JMP j1 ::
      (* 5+i *) JMP (if o0 then 6+i else k) ::
      (* 6+i *) WR b0 ::
      (* 7+i *) MV d0 ::
      (* 8+i *) JMP j0 ::
      (* 9+i *) nil.

    Fact sbtm_op_length : length sbtm_op = 9.
    Proof. reflexivity. Qed.

    Fact sbtm_op_spec t t' :
       let o := if rd t then o1 else o0 in
       let d := if rd t then d1 else d0 in
       let b := if rd t then b1 else b0 in
       let j := if rd t then j1 else j0 
       in  t' = mv d (wr t b)
        -> (i,sbtm_op) // (i,t) -+> if o then (j,t') else (k,t).
    Proof.
      intros o d b j ->.
      unfold sbtm_op.
      destruct t as ((l,[]),r); simpl in * |-; unfold d, b, j, o in *; clear d b j o.
      + pctm sss JZ with (5+i); simpl rd.
        pctm sss JMP with (if o1 then 2+i else k).
        destruct o1.
        * pctm sss WR with b1.
          pctm sss MV with d1.
          pctm sss JMP with j1.
          pctm sss stop.
        * pctm sss stop.
      + pctm sss JZ with (5+i); simpl rd.
        pctm sss JMP with (if o0 then 6+i else k).
        destruct o0.
        * pctm sss WR with b0.
          pctm sss MV with d0.
          pctm sss JMP with j0.
          pctm sss stop.
        * pctm sss stop.
    Qed.

  End sbtm_op.

  Section sbtm.

    Variable (M : SBTM).

    Let f (k : option (state M * bool * direction)) :=
      match k with
        | None         => (false, false, go_left, 0)
        | Some (s,b,d) => (true,  b,     d,       pos2nat s)
      end.

    Let g s := 
      let '(o1,b1,d1,j1) := f (trans' M (s,true)) in
      let '(o0,b0,d0,j0) := f (trans' M (s,false))
      in sbtm_op (2+9*pos2nat s) o0 o1 b0 b1 d0 d1 (2+9*j0) (2+9*j1) 0.

    Let length_g s : length (g s) = 9.
    Proof.
      unfold g.
      destruct (f (trans' M (s,true))) as (((?,?),?),?).
      destruct (f (trans' M (s,false))) as (((?,?),?),?).
      apply sbtm_op_length.
    Qed.

    Let fm_length l : length (flat_map g l) = 9*length l.
    Proof.
      induction l as [ | s l IHl ]; auto.
      simpl flat_map; rewrite app_length, IHl, length_g; simpl; lia.
    Qed.

    Let gs_sc l s r : (2+9*length l,g s) <sc (2,flat_map g (l++s::r)).
    Proof.
      exists (flat_map g l), (flat_map g r); split.
      + rewrite flat_map_app; auto.
      + f_equal; clear s r.
        induction l as [ | s l IHl ]; simpl flat_map; auto.
        rewrite app_length, <- IHl, length_g; simpl; lia.
    Qed.

    Let Q := flat_map g (pos_list _).
 
    Fact Q_length : length Q = 9*num_states M.
    Proof. 
      unfold Q.
      now rewrite fm_length, pos_list_length.
    Qed.

    Let Q_sc i : (2+9*pos2nat i, g i) <sc (2,Q).
    Proof.
      unfold Q.
      destruct (pos_list_split i) as (l & r & -> & <-).
      apply gs_sc.
    Qed.

    Let Q_step_None i t : 
          step M (i,t) = None 
       -> (2,Q) // (2+9*pos2nat i,t) -+> (0,t).
    Proof.
      intros H.
      apply subcode_sss_progress with (1 := Q_sc i).
      destruct t as ((l,[]),r); unfold step in H.
      + revert H; case_eq (trans' M (i,true)). 
        1: now intros ((?,?),?).
        unfold g; intros -> _.
        unfold f at 1.
        destruct (f (trans' M (i, false))) as (((o0,b0),d0),j0).
        apply (sbtm_op_spec (2+9*pos2nat i) o0 false b0 false d0 go_left (2+9*j0) (2+9*0) 0 (l,true,r) eq_refl).
      + revert H; case_eq (trans' M (i,false)). 
        1: now intros ((?,?),?).
        unfold g; intros -> _.
        unfold f at 2.
        destruct (f (trans' M (i, true))) as (((o1,b1),d1),j1).
        apply (sbtm_op_spec (2+9*pos2nat i) false o1 false b1 go_left d1 (2+9*0) (2+9*j1) 0 (l,false,r) eq_refl).
    Qed.

    Let Q_step_Some i t j t' : 
          step M (i,t) = Some (j,t') 
       -> (2,Q) // (2+9*pos2nat i,t) -+> (2+9*pos2nat j,t').
    Proof.
      intros H.
      apply subcode_sss_progress with (1 := Q_sc i).
      destruct t as ((l,[]),r); unfold step in H.
      + revert H; case_eq (trans' M (i,true)). 
        2: easy.
        unfold g; intros ((j1,b1),d1) -> H1.
        inversion H1; subst j t'; clear H1.
        unfold f at 1.
        destruct (f (trans' M (i, false))) as (((o0,b0),d0),j0).
        apply (sbtm_op_spec (2+9*pos2nat i) o0 true b0 b1 d0 d1 (2+9*j0) (2+9*pos2nat j1) 0 (l,true,r) eq_refl).
      + revert H; case_eq (trans' M (i,false)). 
        2: easy.
        unfold g; intros ((j0,b0),d0) -> H1.
        inversion H1; subst j t'; clear H1.
        unfold f at 2.
        destruct (f (trans' M (i, true))) as (((o1,b1),d1),j1).
        apply (sbtm_op_spec (2+9*pos2nat i) true o1 b0 b1 d0 d1 (2+9*pos2nat j0) (2+9*j1) 0 (l,false,r) eq_refl).
    Qed.

    Let steps_Q k i t : 
      match steps M k (i,t) with
        | None => exists t', (2,Q) // (2+9*pos2nat i,t) ->> (0,t') 
        | Some (j,t') =>     (2,Q) // (2+9*pos2nat i,t) ->> (2+9*pos2nat j,t')
      end.
    Proof.
      induction k as [ | k IHk ]; simpl steps.
      + pctm sss stop.
      + unfold SBTM.obind.
        case_eq (steps M k (i,t)).
        * intros (j1,t1) E1; rewrite E1 in IHk.
          case_eq (step M (j1,t1)).
          - intros (j2,t2) E2. 
            apply sss_compute_trans with (1 := IHk).
            now apply sss_progress_compute, Q_step_Some.
          - intros E2.
            exists t1.
            apply sss_compute_trans with (1 := IHk).
            now apply sss_progress_compute, Q_step_None.
        * intros E1; rewrite E1 in IHk; auto.
    Qed.

    Let Q_steps i t :
           (2,Q) // (2+9*pos2nat i,t) ↓
        -> exists k, steps M k (i,t) = None.
    Proof.
      intros ((j,t') & (k & H1) & H2); unfold fst in H2; exists k.
      revert i j t t' H1 H2.
      induction on k as IH with measure k.
      intros i j t t' H1 H2.
      destruct k as [ | k ].
      + apply sss_steps_0_inv in H1. 
        apply f_equal with (f := fst) in H1; unfold fst in H1.
        rewrite <- H1 in H2.
        red in H2.
        unfold code_start, code_end, fst, snd in H2.
        rewrite Q_length in H2.
        generalize (pos2nat_prop i); lia.
      + unfold steps.
        rewrite Natiter_S; simpl.
        case_eq (step M (i,t)).
        2:{ intros _; apply Natiter_fixpoint; auto. }
        intros (j1,t1) H3.
        apply Q_step_Some in H3.
        destruct subcode_sss_progress_inv 
          with (1 := pctm_sss_fun)
               (4 := H3)
               (5 := H1)
          as (r & H4 & H5).
        * simpl; auto.
        * apply subcode_refl.
        * apply IH in H5; auto.
          unfold steps in H5.
          replace k with (k-r+r) by lia.
        rewrite Natiter_add, H5.
        apply Natiter_fixpoint; auto.
    Qed.

    Variable (i : pos (num_states M)).

    Definition sbtm2pctm := (JMP (2+9*pos2nat i)::Q).

    Lemma sbtm2pctm_sound k t : steps M k (i,t) = None -> exists t', (1,sbtm2pctm) // (1,t) ->> (0,t').
    Proof.
      intros H.
      generalize (steps_Q k i t); rewrite H.
      intros (t' & H1); exists t'.
      unfold sbtm2pctm.
      pctm sss JMP with (2 + 9 * pos2nat i).
      revert H1; apply subcode_sss_compute; auto.
    Qed.

    Lemma sbtm2pctm_complete t : (1,sbtm2pctm) // (1,t) ↓ -> exists k, steps M k (i,t) = None.
    Proof.
      unfold sbtm2pctm.
      intros H.
      apply Q_steps.
      apply subcode_sss_terminates_inv 
        with (1 := pctm_sss_fun)
             (P := (1,[JMP (2 + 9 * pos2nat i)]))
             (st1 := (2+9*pos2nat i,t)) in H; auto.
      * revert H; apply subcode_sss_terminates; auto.
      * split; [ | simpl; lia ].
        pctm sss JMP with (2+9*pos2nat i).
        - apply subcode_refl.
        - pctm sss stop.
    Qed.

  End sbtm.

End SBTM_PCTM.

Theorem SBTM_PCTM_reduction : SBTM_HALT ⪯ PCTM_HALT.
Proof.
  apply reduces_dependent; exists.
  intros (M,(i,t)).
  exists (sbtm2pctm M i,t); split.
  + intros (k & Hk).
    apply sbtm2pctm_sound in Hk as (t' & Ht').
    exists (0,t'); split; auto; simpl; lia.
  + apply sbtm2pctm_complete.
Qed.

