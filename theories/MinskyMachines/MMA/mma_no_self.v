(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* * Minsky machines to FRACTRAN programs *)
(* ** Removal of self-loops in MMAs using syntactic and semantic
      properties of the generic compiler *)

Require Import List Arith Lia.

Import ListNotations.

From Undecidability.Shared.Libs.DLW
  Require Import utils pos vec subcode sss compiler compiler_correction.

From Undecidability.MinskyMachines.MMA
  Require Import mma_defs.

Set Implicit Arguments.

Tactic Notation "rew" "length" := autorewrite with length_db.

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v). (* clashes with ListNotations below *)

Local Notation "I // s -1> t" := (mma_sss I s t).
Local Notation "P // s -+> t" := (sss_progress (@mma_sss _) P s t).
Local Notation "P // s ->> t" := (sss_compute (@mma_sss _) P s t).
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

  Fact mma_no_self_loops_cons_inv i ρ P :
         mma_no_self_loops (i,ρ::P)
      -> mma_no_self_loops (1+i,P).
  Proof.
    intros H j x Hj.
    now apply (H j x), subcode_cons.
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
        | DECₐ x j => [ DECₐ x (3+lnk i) ;
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

  Hint Resolve subcode_refl : core.

  Local Fact ic_correct : instruction_compiler_sound ic (@mma_sss _) (@mma_sss _) eq.
  Proof.
    intros lnk I i1 v1 i2 v2 w1.
    change i1 with (fst (i1,v1)) at 2 3 4 5 6 7.
    change i2 with (fst (i2,v2)) at 2.
    change v1 with (snd (i1,v1)) at 5.
    change v2 with (snd (i2,v2)) at 3.
    generalize (i1,v1) (i2,v2); intros st1 st2; clear i1 v1 i2 v2.
    induction 1 as [ i x v | i x k v H | i x k v u H ]; simpl.
    + intros -> <-. 
      exists (vec_change v x (S (v#>x))); split; auto.
      mma sss INC with x.
      mma sss stop.
    + intros -> <-.
      exists v; split; auto.
      mma sss DEC zero with x (S (S (S (lnk i)))).
      mma sss INC with x.
      mma sss DEC S with x (S (S (S (S (S (lnk i)))))) (v#>x); rew vec.
      mma sss stop.
    + intros _ <-.
      exists (vec_change v x u); split; auto.
      mma sss DEC S with x (S (S (S (lnk i)))) u.
      mma sss INC with x.
      1: do 2 apply subcode_cons; subcode_tac.
      mma sss DEC S with x (lnk k) u; rew vec.
      mma sss stop.
  Qed.

  Section no_self_loops. 

    Let gc := generic_syntactic_compiler _ _ il_le il_ic_length.

    Variables (P : list (mm_instr (pos n))).

    Let Q := cs_code gc (1,P) 1.

    Local Fact gc_no_self_loops : mma_no_self_loops (1,Q).
    Proof.
      generalize (cs_not_between gc).
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
          specialize (H7 (1,P) 1 j' k).
          apply H2 with (i := 1) in G1; simpl in G1; lia.
        * now apply subcode_nil_invert in G2.
    Qed.

    Local Fact gc_bounded i x j : (i,DEC x j::nil) <sc (1,Q) -> j <= 1+length Q.
    Proof.
      generalize (cs_between gc (1,P) 1); fold Q; intros H10.
      destruct gc as [ lnk code H0 H1 H2 H3 H4 H5 H6 ]; clear gc.
      simpl in Q, H10.
      intros H.
      apply H6 in H as (k' & [ x' | x' j' ] & G1 & G2); simpl ic in G2.
      + apply subcode_cons_invert_right in G2 as [ (_ & ?) | G2 ]; try easy.
        now apply subcode_nil_invert in G2.
      + generalize G1; intros G0.
        apply H5 with (i := i) in G0; fold Q in G0; apply subcode_length' in G0; simpl in G0.
        apply (H2 _ 1) in G1; simpl in G1.
        repeat apply subcode_cons_invert_right in G2 as [ (G3 & G4) | G2 ]; try easy.
        * specialize (H10 (S k')); inversion G4; lia.
        * specialize (H10 (S k')); inversion G4; lia.
        * specialize (H10 j'); inversion G4; lia.
        * now apply subcode_nil_invert in G2.
    Qed.

    Hint Resolve il_ic_length ic_correct mma_sss_total_ni : core.

    Let lnk := cs_link gc (1,P) 1.

    Theorem mma_remove_self_loops : { Q | mma_no_self_loops (1,Q)
                                       /\ (forall i x j, (i,DEC x j::nil) <sc (1,Q) -> j <= 1+length Q)
                                       /\ forall v, (1,P) // (1,v) ↓ <-> (1,Q) // (1,v) ↓ }.
    Proof.
      exists Q; msplit 2.
      + apply gc_no_self_loops.
      + apply gc_bounded.
      + intros; apply compiler_syntactic_term_equiv with (simul := eq); auto.
        * apply mma_sss_total_ni.
        * apply mma_sss_fun.
    Qed.

  End no_self_loops.

End remove_self_loops.