(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Relations Lia.

Import ListNotations.

Require Import Undecidability.Synthetic.Definitions.

From Undecidability.Shared.Libs.DLW Require Import utils sss subcode compiler compiler_correction.
From Undecidability.MinskyMachines Require Import MM2.

Set Implicit Arguments.

#[local] Notation "i '//' r '⇢' s" := (mm2_atom i r s) (at level 70, no associativity).
#[local] Notation "P '//' r '→' s" := (sss_step mm2_atom P r s) (at level 70, no associativity).
#[local] Notation "P '//' r '-[' k ']->' s" := (sss_steps mm2_atom P k r s) (at level 70, no associativity).
#[local] Notation "P '//' r '↠' s" := (sss_compute mm2_atom P r s) (at level 70, no associativity).
#[local] Notation "P '//' r '~~>' s" := (sss_output mm2_atom P r s) (at level 70, no associativity).
#[local] Notation "P '//' s ↓" := (sss_terminates mm2_atom P s) (at level 70, no associativity).

Fact mm2_atom_fun i st st1 st2 : i // st ⇢ st1 -> i // st ⇢ st2 -> st1 = st2.
Proof. 
  intros H; revert H st2.
  now induction 1; inversion 1.
Qed.

Fact mm2_atom_total i st : { st' | i // st ⇢ st' }.
Proof.
  destruct st as (j,(a,b)).
  destruct i as [ | | k | k ].
  + exists (1+j,(S a,b)); constructor.
  + exists (1+j,(a,S b)); constructor.
  + destruct a as [|a].
    * exists (1+j,(0,b)); constructor.
    * exists (k,(a,b)); constructor.
  + destruct b as [|b].
    * exists (1+j,(a,0)); constructor.
    * exists (k,(a,b)); constructor.
Qed.

Fact mm2_atom_total_ni i st : exists st', i // st ⇢ st'.
Proof. destruct (mm2_atom_total i st); eauto. Qed.

Section MM2_to_MM2.

  (* The identity compiler behaves a relinking the code so that the
     output PC value is always at the code end *)

  Local Definition mm2_instr_compile lnk (_ : nat) (ii : mm2_instr) :=
    match ii with
      | mm2_inc_a   => [mm2_inc_a]
      | mm2_inc_b   => [mm2_inc_b]
      | mm2_dec_a j => [mm2_dec_a (lnk j)]
      | mm2_dec_b j => [mm2_dec_b (lnk j)]
    end.

  Local Definition mm2_instr_compile_length (_ : mm2_instr) := 1.

  Local Fact mm2_instr_compile_length_eq lnk i ii : length (mm2_instr_compile lnk i ii) = mm2_instr_compile_length ii.
  Proof. destruct ii; simpl; auto. Qed.

  Local Fact mm2_instr_compile_length_geq ii : 1 <= mm2_instr_compile_length ii.
  Proof. cbv; lia. Qed.

  Hint Resolve mm2_instr_compile_length_eq mm2_instr_compile_length_geq : core.
  Hint Resolve subcode_refl : core.

  (* This main soundness lemma per simulated instruction *)

  Tactic Notation "finish" "with" constr(t) ident(H) :=
    exists t; split; trivial; apply sss_one_steps; try rewrite H; constructor.

  Local Lemma mm2_instr_compile_sound : instruction_compiler_sound mm2_instr_compile mm2_atom mm2_atom eq.
  Proof.
    intros lnk I i1 v1 i2 v2 w1 H; revert H w1.
    change v1 with (snd (i1,v1)) at 2.
    change i1 with (fst (i1,v1)) at 2 3 4 6 7 8.
    change v2 with (snd (i2,v2)) at 2.
    change i2 with (fst (i2,v2)) at 2.
    generalize (i1,v1) (i2,v2); clear i1 v1 i2 v2.
    induction 1 
      as [ i a b | i a b | i j a b | i j a b | i j b | i j a ]; 
      simpl; intros w1 Hw1 <-.
    + finish with (S a,b) Hw1.
    + finish with (a,S b) Hw1.
    + finish with (a,b) Hw1.
    + finish with (a,b) Hw1.
    + finish with (0,b) Hw1.
    + finish with (a,0) Hw1.
  Qed.

  Hint Resolve mm2_instr_compile_sound : core.

  Theorem mm2_auto_compiler : compiler_t mm2_atom mm2_atom eq.
  Proof.
    apply generic_compiler 
        with (icomp := mm2_instr_compile)
             (ilen := mm2_instr_compile_length); auto.
    + apply mm2_atom_total_ni.
    + apply mm2_atom_fun.
  Qed.

  (* While they compute the same output, the auto simulated MM2 
     starts at PC value 1 and stops at a unique PC value (code_end), 
     a more predictable outcome than the original MMA *)

  Theorem mm2_auto_simulator i (P : list mm2_instr) j : 
         { Q : list mm2_instr 
         | forall v, 
              (forall i' v', (i,P) // (i,v) ~~> (i',v') -> (j,Q) // (j,v) ~~> (length Q+j,v'))
           /\ ((j,Q) // (j,v) ↓ -> (i,P) // (i,v) ↓) 
         }.
  Proof.
    exists (gc_code mm2_auto_compiler (i,P) j).
    intros v; split.
    + intros i' v' H.
      apply (compiler_t_output_sound' mm2_auto_compiler)
        with (i := j) (w := v) 
        in H as (w' & H1 & <-); eauto.
      rewrite plus_comm; auto. 
    + apply compiler_t_term_equiv; auto.
  Qed.

End MM2_to_MM2.

Section MM2_incs.

  Local Fixpoint mm2_incs_a n := 
    match n with 
      | 0 => nil 
      | S n => mm2_inc_a :: mm2_incs_a n
    end.

  Local Fact mm2_incs_a_length n : length (mm2_incs_a n) = n.
  Proof. now induction n; simpl; f_equal. Qed. 

  Local Fact mm2_incs_a_steps n i a b : (i, mm2_incs_a n) // (i,(a,b)) -[n]-> (n+i,(n+a,b)).
  Proof.
    induction n as [ | n IHn ] in i, a |- *.
    + constructor.
    + constructor 2 with (1+i,(S a,b)).
      * apply in_sss_step with (l := nil); simpl; try lia.
        constructor.
      * replace (S n+a) with (n+S a) by lia.
        replace (S n+i) with (n+S i) by lia.
        generalize (IHn (1+i) (S a)).
        apply subcode_sss_steps, subcode_cons, subcode_refl.
  Qed.

  Local Lemma mm2_incs_a_compute n i a b : (i, mm2_incs_a n) // (i,(a,b)) ↠ (n+i,(n+a,b)).
  Proof. eexists; apply mm2_incs_a_steps. Qed.

  Local Fixpoint mm2_incs_b n := 
    match n with 
      | 0 => nil 
      | S n => mm2_inc_b :: mm2_incs_b n
    end.

  Local Fact mm2_incs_b_length n : length (mm2_incs_b n) = n.
  Proof. now induction n; simpl; f_equal. Qed. 

  Local Fact mm2_incs_b_steps n i a b : (i, mm2_incs_b n) // (i,(a,b)) -[n]-> (n+i,(a,n+b)).
  Proof.
    induction n as [ | n IHn ] in i, b |- *.
    + constructor.
    + constructor 2 with (1+i,(a,S b)).
      * apply in_sss_step with (l := nil); simpl; try lia.
        constructor.
      * replace (S n+b) with (n+S b) by lia.
        replace (S n+i) with (n+S i) by lia.
        generalize (IHn (1+i) (S b)).
        apply subcode_sss_steps, subcode_cons, subcode_refl.
  Qed.

  Local Lemma mm2_incs_b_compute n i a b : (i, mm2_incs_b n) // (i,(a,b)) ↠ (n+i,(a,n+b)).
  Proof. eexists; apply mm2_incs_b_steps. Qed.

End MM2_incs.

Section mm2_mm2_0_simulator.

  Variable (P : list mm2_instr) (a b : nat).

  Let Q1 := proj1_sig (mm2_auto_simulator 1 P (a+b)).
  Let HQ1 := proj2_sig (mm2_auto_simulator 1 P (a+b)).

  Let Q0 := mm2_incs_a a ++ mm2_incs_b b.
  Let R := Q0++Q1.

  Hint Rewrite mm2_incs_a_length mm2_incs_b_length : length_db.

  Local Fact Q0_length : length Q0 = a+b.
  Proof. now unfold Q0; rew length. Qed.

  Hint Rewrite Q0_length : length_db.

  Local Fact Q0_init : (0,Q0) // (0,(0,0)) ↠ (a+b,(a,b)).
  Proof.
    unfold Q0.
    apply subcode_sss_compute_trans with (P := (0,mm2_incs_a a)) (st2 := (a+0,(a+0,0))); auto.
    + apply mm2_incs_a_compute.
    + rewrite !(plus_comm a).
      apply subcode_sss_compute with (a,mm2_incs_b b); auto.
      replace b with (b+0) at 3 by lia.
      apply mm2_incs_b_compute.
  Qed.

  Local Lemma R_sim_1 : (1,P) // (1,(a,b)) ↓ -> (0,R) // (0,(0,0)) ↓.
  Proof.
    intros ((i,(a',b')) & H).
    exists (length Q1+(a+b),(a',b')); split.
    + generalize (proj1 (HQ1 (a,b)) _ _ H); intros (H1 & _).
      apply subcode_sss_compute_trans with (2 := Q0_init); unfold R; auto.
      apply subcode_sss_compute with (a+b,Q1); auto.
    + unfold R; simpl; rew length; lia.
  Qed.

  Local Lemma R_sim_2 : (0,R) // (0,(0,0)) ↓ -> (1,P) // (1,(a,b)) ↓.
  Proof.
    intros H.
    apply HQ1; fold Q1.
    apply subcode_sss_terminates with (0,R).
    1: unfold R; auto.
    apply subcode_sss_terminates_inv with (2 := H) (P := (0,mm2_incs_a a ++ mm2_incs_b b)).
    + apply mm2_atom_fun.
    + now apply subcode_left.
    + split. 
      * apply Q0_init.
      * simpl; rew length; lia.
  Qed. 

  Theorem mm2_mm2_0_simulator : { Q | (1,P) // (1,(a,b)) ↓ <-> (0,Q) // (0,(0,0)) ↓ }.
  Proof.
    exists R; split.
    + apply R_sim_1.
    + apply R_sim_2.
  Qed.

End mm2_mm2_0_simulator.

Check mm2_mm2_0_simulator.
