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
  Require Import utils pos vec subcode sss compiler_correction.

From Undecidability.MinskyMachines.MMA
  Require Import mma_defs mma_utils.

Set Implicit Arguments.

Tactic Notation "rew" "length" := autorewrite with length_db.

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).

Local Notation "P //ₐ s -+> t" := (sss_progress (@mma_sss _) P s t) (at level 70, no associativity).
Local Notation "P //ₐ s ->> t" := (sss_compute (@mma_sss _) P s t) (at level 70, no associativity).
Local Notation "P //ₐ s ~~> t" := (sss_output (@mma_sss _) P s t) (at level 70, no associativity).
Local Notation "P //ₐ s ↓" := (sss_terminates (@mma_sss _) P s) (at level 70, no associativity). 

(* We use the generic compiler with an identity map on instructions
    to simulate termination with termination on (0,vec_zero) *)

Section mma_sim.

  Variables (n : nat).

  (* The identity compiler behaves a relinking the code so that the
     output PC value is always at the code end *)

  Definition mma_instr_compile lnk (_ : nat) (ii : mm_instr (pos n)) :=
    match ii with
      | INCₐ k   => INCₐ k :: nil
      | DECₐ k j => DECₐ k (lnk j) :: nil
    end. 

  Definition mma_instr_compile_length (ii : mm_instr (pos n)) := 1.

  Fact mma_instr_compile_length_eq lnk i ii : length (mma_instr_compile lnk i ii) = mma_instr_compile_length ii.
  Proof using. destruct ii; simpl; auto. Qed.
    
  Fact mma_instr_compile_length_geq ii : 1 <= mma_instr_compile_length ii.
  Proof using. cbv; lia. Qed.

  Hint Resolve mma_instr_compile_length_eq mma_instr_compile_length_geq : core.
  Hint Resolve subcode_refl : core.

  (* This main soundness lemma per simulated instruction *)

  Lemma mma_instr_compile_sound : instruction_compiler_sound mma_instr_compile (@mma_sss _) (@mma_sss _) eq.
  Proof using .
    intros lnk I i1 v1 i2 v2 w1 H; revert H w1.
    change v1 with (snd (i1,v1)) at 2.
    change i1 with (fst (i1,v1)) at 2 3 4 6 7 8.
    change v2 with (snd (i2,v2)) at 2.
    change i2 with (fst (i2,v2)) at 2.
    generalize (i1,v1) (i2,v2); clear i1 v1 i2 v2.
    induction 1 
      as [ i x k | i x k v H | i x k v u H ]; 
      simpl; intros w1 H0 ->.
    + exists (w1 [(S (w1#>x))/x]); split; auto.
      mma sss INC with x.
      mma sss stop; now f_equal.
    + exists w1; split; auto.
      mma sss DEC zero with x (lnk k).
      mma sss stop; now f_equal.
    + exists (w1[u/x]); split; auto.
      mma sss DEC S with x (lnk k) u.
      mma sss stop.
  Qed.

  Hint Resolve mma_instr_compile_sound : core.

  Theorem mma_auto_compiler : compiler_t (@mma_sss n) (@mma_sss n) eq.
    Proof using.
      apply generic_compiler 
        with (icomp := mma_instr_compile)
             (ilen := mma_instr_compile_length); auto.
      + apply mma_sss_total_ni.
      + apply mma_sss_fun.
    Qed.

  (* While they compute the same output, the auto simulated MMA 
     starts at PC value 1 and stops at a unique PC value (code_end), 
     a more predictable outcome than the original MMA *)

  Theorem mma_auto_simulator i (P : list (@mm_instr (pos n))) : 
         { Q : list (@mm_instr (pos n)) 
         | forall v, 
              (forall i' v', (i,P) //ₐ (i,v) ~~> (i',v') -> (1,Q) //ₐ (1,v) ~~> (length Q+1,v'))
           /\ ((1,Q) //ₐ (1,v) ↓  -> (i,P) //ₐ (i,v) ↓) 
         }.
  Proof using .
    exists (gc_code mma_auto_compiler (i,P) 1).
    intros v; split.
    + intros i' v' H.
      eapply compiler_t_output_sound' 
        with (c := mma_auto_compiler) (i := 1) (w := v) 
        in H as (w' & H1 & <-); eauto.
      rewrite plus_comm; auto. 
    + apply compiler_t_term_equiv; auto.
  Qed.

End mma_sim.

Section mma_mma0_sim.

  Variable (n i : nat) (P : list (mm_instr (pos (S n)))).

  Let Q := proj1_sig (mma_auto_simulator i P).
  Let HQ := proj2_sig (mma_auto_simulator i P).

  Definition mma_mma0_sim := Q ++ mma_null_all _ (length Q+1) ++ mma_jump 0 pos0.

  Notation R := mma_mma0_sim.

  Hint Rewrite mma_null_all_length : length_db.

  Theorem mma_mma0_sim_spec v : (i,P) //ₐ (i,v) ↓ <-> (1,R) //ₐ (1,v) ~~> (0,vec_zero).
  Proof using .
    split.
    + intros ((i',v') & H).
      apply HQ in H; fold Q in H.
      destruct H as [ H _ ].
      split; [ | simpl; lia ].
      unfold R.
      apply subcode_sss_compute_trans with (2 := H); auto.
      apply subcode_sss_compute_trans with (2 := mma_null_all_spec _ _); auto.
      apply subcode_sss_compute with (2 := mma_jump_spec _ pos0 _ _); auto.
    + intros H.
      apply HQ; fold Q.
      apply subcode_sss_terminates with (Q := (1,R)).
      * unfold R; auto.
      * exists (0,vec_zero); auto.
  Qed.

End mma_mma0_sim.

(* Termination can be simulated with termination on (0,vec_zero) *)

Theorem mma2_simulator n i (P : list (mm_instr (pos (S n)))) :
  { Q | forall v, (i,P) //ₐ (i,v) ↓ <-> (1,Q) //ₐ (1,v) ~~> (0,vec_zero) }.
Proof using . exists (mma_mma0_sim i P); apply mma_mma0_sim_spec. Qed.
