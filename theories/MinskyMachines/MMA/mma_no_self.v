(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* * Minsky machines to FRACTRAN programs *)
(* ** Removal of self-loops in MMAs *)

Require Import List Arith Lia.

Import ListNotations.

From Undecidability.Shared.Libs.DLW
  Require Import utils pos vec subcode sss compiler.

From Undecidability.MinskyMachines.MMA
  Require Import mma_defs.

Set Implicit Arguments.

Tactic Notation "rew" "length" := autorewrite with length_db.

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).

Local Notation "I // s -1> t" := (mma_sss I s t).
Local Notation "P // s -[ k ]-> t" := (sss_steps (@mma_sss _) P k s t).
Local Notation "P // s -+> t" := (sss_progress (@mma_sss _) P s t).
Local Notation "P // s ->> t" := (sss_compute (@mma_sss _) P s t).
Local Notation "P // s '~~>' t" := (sss_output (@mma_sss _) P s t).
Local Notation "P // s ↓" := (sss_terminates (@mma_sss _) P s). 

Section no_self_loops.

  Variables (n : nat).

  Definition mma_no_self_loops (Q : nat * list (mm_instr (pos n))) := 
    forall i x, ~ (i,[DEC x i]) <sc Q.

  Implicit Types (P Q : list (mm_instr (pos n))).

  Fact mma_no_self_loops_app i P Q : mma_no_self_loops (i,P) 
                                  -> mma_no_self_loops (length P+i,Q)
                                  -> mma_no_self_loops (i,P++Q).
  Proof.
    intros H1 H2 j x H.
    apply subcode_app_invert_right in H.
    destruct H as [ H | H ]; revert H.
    + apply H1.
    + apply H2.
  Qed.

End no_self_loops.

Section remove_self_loops.

  Variable (n : nat).

  Implicit Type ρ : mm_instr (pos n).

  Local Definition il ρ :=
    match ρ with
      | INCₐ x   => 1
      | DECₐ x j => 5
    end.

  Section instr_compiler.

    Variable (lnk : nat -> nat).

    Local Definition ic i ρ :=
      match ρ with
        | INCₐ x   => [ INCₐ x ]
        | DECₐ x j => [ DECₐ x (2+lnk i) ;
                        INCₐ x ;
                        DECₐ x (5+lnk i) ;
                        INCₐ x ;
                        DECₐ x (lnk j) ]
      end.

    Local Fact il_ic_length i ρ : length (ic i ρ) = il ρ.
    Proof. now destruct ρ. Qed.

  End instr_compiler.

  Variable lnk : nat -> nat.

  (* One would here want to use the instruction compiler but this
     poses a problem because we do not have much syntactic information
     available from the linker/compiler ATM, hence showing that
     lnk j above cannot be 4+lnk i is problematic
     this should eg follow from 
        if   j <= i  then                lnk j <= lnk i
     or if 1+i <= j  then  5+lnk i = lnk (1+i) <= lnk j
     which are both compatible with lnk j = 4+lnk i *)

  Local Fact mma_no_self_loops_ic i ρ : mma_no_self_loops (lnk i,ic i ρ).
  Proof.
    destruct ρ as [ x | x j ]; simpl; intros k µ H.
    + apply subcode_cons_invert_right in H as [ (? & ?) | H ]; try easy.
      now apply subcode_nil_invert in H.
    + repeat apply subcode_cons_invert_right in H as [ (E1 & E2) | H ].
      * inversion E2; lia.
      * easy.
      * inversion E2; lia.
      * easy.
      * inversion E2; subst k x.
        destruct (le_lt_dec i j) as [ 
      apply subcode_cons_invert_right in H as [ (E1 & E2) | H ].
      1: easy.
