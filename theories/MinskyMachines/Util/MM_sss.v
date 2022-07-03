(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* Certified Undecidability of Intuitionistic Linear Logic via Binary Stack Machines and Minsky Machines. Yannick Forster and Dominique Larchey-Wendling. CPP '19. http://uds-psl.github.io/ill-undecidability/ *)

From Coq Require Import List Lia.

From Undecidability.Shared.Libs.DLW
  Require Import Vec.pos Vec.vec Code.sss.

Require Import Undecidability.MinskyMachines.MM.

Set Implicit Arguments.

(** * Halting problem for Minsky machines MM_HALTING  *)

(* * Minsky Machines (MM)

    A Minsky machine has n registers and there are just two instructions
 
    1/ INC x   : increment register x by 1
    2/ DEC x k : decrement register x by 1 if x > 0
                 or jump to k if x = 0

  *)

(* * Alternate Minsky Machines (MMA) such that two counters are enough for undec

    Minsky machine has n registers and there are just two instructions
 
    1/ INC x   : increment register x by 1
    2/ DEC x k : if x > 0 then decrement register x by 1 and jump to k

    If no jump occurs, then implicitly, the jump is to the next instruction

    We show that they simulated FRACTRAN
  *)
(* 
Inductive mm_instr (X : Set) : Set :=
  | mm_inc : X -> mm_instr X
  | mm_dec : X -> nat -> mm_instr X
  .
 *)
Notation INC := mm_inc.
Notation DEC := mm_dec.

(* ** Semantics for MM, restricted to X = pos n for some n *)

Section Minsky_Machine.

  Variable (n : nat).

  Definition mm_state := (nat*vec nat n)%type.

  Local Notation "e #> x" := (vec_pos e x).
  Local Notation "e [ v / x ]" := (vec_change e x v).

  (* Minsky machine small step semantics *)

  Inductive mm_sss : mm_instr (pos n) -> mm_state -> mm_state -> Prop :=
    | in_mm_sss_inc   : forall i x v,                   INC x   // (i,v) -1> (1+i,v[(S (v#>x))/x])
    | in_mm_sss_dec_0 : forall i x k v,   v#>x = O   -> DEC x k // (i,v) -1> (k,v)
    | in_mm_sss_dec_1 : forall i x k v u, v#>x = S u -> DEC x k // (i,v) -1> (1+i,v[u/x])
  where "i // s -1> t" := (mm_sss i s t).

End Minsky_Machine.

Lemma eval_to_sss_compute n i (P : list (mm_instr (pos n))) c (v : vec nat n) c' v' :
  eval (i, P) (c, v) (c', v') -> sss_compute (@mm_sss _) (i,P) (c, v) (c', v').
Proof.
  generalize (i, P) as iP.
  generalize (c, v) as cv.
  generalize (c', v') as c'v'. clear.
  induction 1 as [ i P c v
                 | i P c v j c' v' H1 H2 H [k IH]
                 | i P c v j c1 c' v' l H1 H2 H3 H [k IH]
                 | i P c v j c1 c' v' H1 H2 H3 H [k IH] ].
  - exists 0. econstructor.
  - exists (1 + k).
    eapply nth_error_split in H2 as (l1 & l2 & -> & Hl).
    repeat econstructor.
    + f_equal. lia.
    + replace (1 + c) with (c + 1) by lia.
      now replace (S (vec_pos v j)) with (vec_pos v j + 1) by lia.
  - exists (1 + k).
    eapply nth_error_split in H2 as (l1 & l2 & -> & Hl).
    econstructor; [ | eauto]. 
    repeat econstructor.
    + f_equal. lia.
    + replace (c + 1) with (1 + c) by lia. econstructor. eauto.
  - exists (1 + k).
    eapply nth_error_split in H2 as (l1 & l2 & -> & Hl).
    econstructor; [ | eauto].
    repeat econstructor.
    * f_equal. lia.
    * eauto.
Qed.

Lemma eval_to_sss_out_code n i (P : list (mm_instr (pos n))) c (v : vec nat n) c' v' :
  eval (i, P) (c, v) (c', v') -> subcode.out_code (fst (c', v')) (i, P).
Proof.
  generalize (i, P) as iP.
  generalize (c, v) as cv.
  generalize (c', v') as c'v'. clear.
  induction 1 as [ i P c v
                 | i P c v j b c' v' H1 H2 H IH
                 | i P c v j c1 c2 c' v' l H1 H2 H3 H IH
                 | i P c v j c1 c2 c' v' H1 H2 H3 H IH]; cbn in *.
  all: lia.
Qed.

Lemma sss_output_to_eval n i (P : list (mm_instr (pos n))) c (v : vec nat n) c' v' :
  sss_output (@mm_sss _) (i,P) (c, v) (c', v') -> eval (i, P) (c, v) (c', v').
Proof.
  generalize (i, P) as iP.
  generalize (c, v) as cv.
  generalize (c', v') as c'v'. clear.
  intros ? ? ? [[k H1] H2].
  induction H1 as [cv | n0 st1 st2 (c', v') (k & l & i & r & d & -> & -> & HH) H IH] in * |- *.
  - destruct iP as (i, P), cv as (c, v);
      try destruct c'v' as (c', v').
    econstructor. cbn in *. lia.
  - revert IH H H2.
    inversion_clear HH as [ | | ]; subst; intros IH' HHH IH % IH'; clear IH'.
    + eapply eval_mm_inc; [ lia | | ].
      * rewrite nth_error_app2; [ | lia].
        now replace (k + length l - k - length l) with 0 by lia.
      * replace (k + length l + 1) with (1 + (k + length l)) by lia.
        now replace (vec_pos d x + 1) with (S (vec_pos d x)) by lia.
    + eapply eval_mm_dec_empty; [ lia | | eauto ..].
      rewrite nth_error_app2; [ | lia].
      now replace (k + length l - k - length l) with 0 by lia.
    + eapply eval_mm_dec_S; [ lia | | eauto ..].
      * rewrite nth_error_app2; [ | lia].
        now replace (k + length l - k - length l) with 0 by lia.
      * now replace (k + length l + 1) with (1 + (k + length l)) by lia.
Qed.

Theorem eval_iff n i (P : list (mm_instr (pos n))) c (v : vec nat n) c' v' :
  eval (i, P) (c, v) (c', v') <-> sss_output (@mm_sss _) (i,P) (c, v) (c', v').
Proof.
  split.
  - intros H. split.
    + now eapply eval_to_sss_compute.
    + eapply eval_to_sss_out_code. eassumption.
  - intros H. now eapply sss_output_to_eval.
Qed.

Section MM_problems.

  Notation "P // s ~~> t" := (sss_output (@mm_sss _) P s t).
  Notation "P // s ↓" := (sss_terminates (@mm_sss _) P s). 

  Definition MM_PROBLEM := { n : nat & { P : list (mm_instr (pos n)) & vec nat n } }.

  Definition MM_HALTS_ON_ZERO (P : MM_PROBLEM) := 
    match P with existT _ n (existT _ P v) => (1,P) // (1,v) ~~> (0,vec_zero) end.

  Definition MM_HALTING (P : MM_PROBLEM) :=
    match P with existT _ n (existT _ P v) => (1, P) // (1, v) ↓ end.

  Definition Halt_MM (P : MM_PROBLEM) :=
    match P with existT _ n (existT _ P v) => exists c v', eval (1, P) (1, v) (c, v') end.

  Definition MM_2_PROBLEM := { P : list (mm_instr (pos 2)) & vec nat 2 }.

  Definition MM_2_HALTING (P : MM_2_PROBLEM) :=
    match P with existT _ P v => (1, P) // (1, v) ↓ end.

End MM_problems.

Lemma Halt_MM_iff P :
  Halt_MM P <-> MM_HALTING P.
Proof.
  destruct P as (n & P & v); cbn.
  split.
  - intros (c' & v' & H % eval_iff). eexists. eauto.
  - intros [(c', v') H % eval_iff]. eauto.
Qed.
