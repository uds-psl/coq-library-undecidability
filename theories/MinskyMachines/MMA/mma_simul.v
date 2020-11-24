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

Local Notation "P // s -+> t" := (sss_progress (@mma_sss _) P s t).
Local Notation "P // s ->> t" := (sss_compute (@mma_sss _) P s t).
Local Notation "P // s ~~> t" := (sss_output (@mma_sss _) P s t).
Local Notation "P // s ↓" := (sss_terminates (@mma_sss _) P s).

(* We use the generic compiler with an identity map on instructions
    to simulate termination with termination on (0,vec_zero) *)

Section mma_sim.

  Variables (n : nat).

  (* The identity compiler, just the jump address changes according to the linker *)

  Definition mma_instr_compile lnk (_ : nat) (ii : mm_instr (pos n)) :=
    match ii with
      | INC k   => INC k :: nil
      | DEC k j => DEC k (lnk j) :: nil
    end. 

  Definition mma_instr_compile_length (ii : mm_instr (pos n)) := 1.

  Fact mma_instr_compile_length_eq lnk i ii : length (mma_instr_compile lnk i ii) = mma_instr_compile_length ii.
  Proof. destruct ii; simpl; auto. Qed.
    
  Fact mma_instr_compile_length_geq ii : 1 <= mma_instr_compile_length ii.
  Proof. cbv; lia. Qed.

  Hint Resolve mma_instr_compile_length_eq mma_instr_compile_length_geq : core.
  Hint Resolve subcode_refl : core.

  (* This main soundness lemma per simulated instruction *)

  Lemma mma_instr_compile_sound : instruction_compiler_sound mma_instr_compile (@mma_sss _) (@mma_sss _) eq.
  Proof.
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
      mma sss DEC 0 with x (lnk k).
      mma sss stop; now f_equal.
    + exists (w1[u/x]); split; auto.
      mma sss DEC S with x (lnk k) u.
      mma sss stop.
  Qed.

  Hint Resolve mma_instr_compile_sound : core.

  Section mma_sim.

    Variable (iP : nat) (cP : list (mm_instr (pos n))).

    Let lnk_Q_pair := @gen_compiler_correction _ _ _ _ mma_instr_compile_length_eq _ _ _ _  (@mma_sss_total_ni _)
                     (@mma_sss_fun _) _ mma_instr_compile_sound (iP,cP) 1. 

    Let lnk := projT1 lnk_Q_pair.
    Let Q := proj1_sig (projT2 lnk_Q_pair).

    Let Hlnk : fst Q = 1 /\ lnk iP = 1 /\ forall i, out_code i (iP,cP) -> lnk i = code_end Q.
    Proof.
      repeat split; apply (proj2_sig (projT2 lnk_Q_pair)).
    Qed.

    Infix "⋈" := (@eq (vec nat n)) (at level 70, no associativity).

    Let HQ1 : forall i1 v1 w1 i2 v2, v1 ⋈ w1 /\ (iP,cP) // (i1,v1) ~~> (i2,v2)     
                    -> exists w2,    v2 ⋈ w2 /\ Q // (lnk i1,w1) ~~> (lnk i2,w2).
    Proof. apply (proj2_sig (projT2 lnk_Q_pair)). Qed.

    Let HQ1' i1 v1 i2 v2 : (iP,cP) // (i1,v1) ~~> (i2,v2) 
                        ->   Q // (lnk i1,v1) ~~> (lnk i2,v2).
    Proof.
      intros H; destruct (@HQ1 i1 v1 v1 i2 v2) as (w2 & <- & ?); auto.
    Qed.

    Let HQ2 : forall i1 v1 w1 j2 w2, v1 ⋈ w1 /\ Q // (lnk i1,w1) ~~> (j2,w2) 
                    -> exists i2 v2, v2 ⋈ w2 /\ (iP,cP) // (i1,v1) ~~> (i2,v2) /\ j2 = lnk i2.
    Proof. apply (proj2_sig (projT2 lnk_Q_pair)). Qed.

    Let HQ2' i1 v1 j2 v2 :         Q // (lnk i1,v1) ~~> (j2,v2) 
               -> exists i2, (iP,cP) // (i1,v1) ~~> (i2,v2) /\ j2 = lnk i2.
    Proof.
      intros H; destruct (@HQ2 i1 v1 v1 j2 v2) as (i2 & ? & <- & ? & ->); auto.
      exists i2; auto.
    Qed.

    Variable v : vec nat n.
 
    (* Q simulates termination of (iP,cP) while ensuring tmp1 and tmp2 stay void when it terminates *)

    Let Q_spec1 : (iP,cP) // (iP,v) ↓ -> exists w', Q // (1,v) ~~> (code_end Q, w').
    Proof.
      intros ((i1,v1) & H1).
      exists v1.
      rewrite <- (proj2 (proj2 Hlnk) i1), <- (proj1 (proj2 Hlnk)); auto.
      destruct H1; auto.
    Qed.

    Let Q_spec2 : Q // (1,v) ↓ -> (iP,cP) // (iP,v) ↓.
    Proof.
      intros ((j,w2) & H1).
      rewrite <- (proj1 (proj2 Hlnk)) in H1.
      destruct HQ2' with (1 := H1) as (i2 & ? & ->).
      exists (i2,w2); auto.
    Qed.

    Definition mma_sim := snd Q.
    Definition mma_sim_end := code_end Q.

    Theorem mma_sim_spec : ((iP,cP) // (iP,v) ↓ -> exists w', (1,mma_sim) // (1,v) ~~> (1+length mma_sim, w'))
                        /\ ((1,mma_sim) // (1,v) ↓ -> (iP,cP) // (iP,v) ↓).
    Proof.
      replace (1+length mma_sim) with (code_end Q).
      replace (1,mma_sim) with Q. 
      + split; auto.
      + rewrite (surjective_pairing Q); f_equal; auto.
        apply (proj1 Hlnk).
      + unfold code_end; f_equal.
        apply (proj1 Hlnk).
    Qed.

  End mma_sim.

End mma_sim.

Section mma2_simul.

  (* To generalize for n register, we need a recursive nullifying code 
     not compilcated though *)

  Variable (iP : nat) (cP : list (mm_instr (pos 2))).

  Let Q := mma_sim iP cP.
  Let eQ := 1+length Q.

  Let cN : list (mm_instr (pos 2)) := mma_null pos0 eQ ++ mma_null pos1 (1+eQ) ++ mma_jump 0 pos0.

  Let L1 := @mma_null_length 2 pos0 eQ.
  Let L2 := @mma_null_length 2 pos1 (1+eQ).

  Let N_spec v : (eQ,cN) // (eQ,v) -+> (0,vec_zero).
  Proof.
    unfold cN.
    apply sss_progress_trans with (1+eQ,v[0/pos0]).
    1: { apply subcode_sss_progress with (P := (eQ,mma_null pos0 eQ)); auto.
         apply mma_null_progress; auto. }
    apply sss_progress_trans with (2+eQ,(v[0/pos0])[0/pos1]).
    1: { apply subcode_sss_progress with (P := (1+eQ,mma_null pos1 (1+eQ))); auto.
         apply mma_null_progress; auto. }
    replace ((v[0/pos0])[0/pos1]) with (@vec_zero 2).
    2: { apply vec_pos_ext; intros p.
         repeat (invert pos p; rew vec). }
    apply subcode_sss_progress with (P := (2+eQ,mma_jump 0 pos0)); auto. 
    apply mma_jump_progress.
  Qed.

  Definition mma2_simul := Q ++ cN.

  Let cQ_sim : (1,Q) <sc (1,mma2_simul).
  Proof. unfold mma2_simul; auto. Qed.
  
  Let cN_sim : (eQ,cN) <sc (1,mma2_simul).
  Proof. unfold mma2_simul, eQ; auto. Qed.

  Theorem mma2_simul_spec v : (iP,cP) // (iP,v) ↓ <-> (1,mma2_simul) // (1,v) ~~> (0,vec_zero).
  Proof.
    split.
    * intros H; apply mma_sim_spec in H; revert H.
      intros (w & Hw & _).
      split; try (simpl; lia).
      apply sss_compute_trans with (eQ,w).
      + revert Hw; apply subcode_sss_compute; auto.
      + apply sss_progress_compute.
        generalize (N_spec w).
        apply subcode_sss_progress; auto.
    * intros H1.
      apply mma_sim_spec; fold Q.
      apply subcode_sss_terminates with (1 := cQ_sim).
      now exists (0,vec_zero).
  Qed.

End mma2_simul.

(* Termination can be simulated with termination on (0,vec_zero) *)

Theorem mma2_simulator i (P : list (mm_instr (pos 2))) :
  { Q | forall v, (i,P) // (i,v) ↓ <-> (1,Q) // (1,v) ~~> (0,vec_zero) }.
Proof. exists (mma2_simul i P); apply mma2_simul_spec. Qed.
