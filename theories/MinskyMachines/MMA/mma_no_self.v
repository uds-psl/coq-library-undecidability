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

    Local Fact il_le ρ : 1 <= il ρ.
    Proof. destruct ρ; simpl; lia. Qed.

  End instr_compiler.

  Section no_self_loops. 

    Let gc := generic_syntactic_compiler _ _ il_le il_ic_length.

    Fact gc_no_self_loops P i : mma_no_self_loops (i,cs_code gc P i).
    Proof.
      generalize (cs_exclude gc).
      destruct gc as [ lnk code H0 H1 H2 H3 H4 H5 H6 ]; simpl; clear gc; intro H7.
      intros j x H.
      apply H6 in H as (k & [ x' | x' j' ] & G1 & G2); simpl ic in G2.
      + apply subcode_cons_invert_right in G2 as [ (_ & ?) | G2 ]; try easy.
        now apply subcode_nil_invert in G2.
      + repeat apply subcode_cons_invert_right in G2 as [ (E1 & E2) | G2 ].
        * inversion E2; lia.
        * easy.
        * inversion E2; lia.
        * easy.
        * inversion E2; clear E2.
          generalize G1; intros G.
          apply subcode_in_code with (i := k) in G.
          2: simpl; lia.
          apply H7 with (i := i) (j := j') in G.
          apply H2 with (i := i) in G1; simpl in G1; lia.
        * now apply subcode_nil_invert in G2.
      Qed.

  End no_self_loops.

End remove_self_loops.