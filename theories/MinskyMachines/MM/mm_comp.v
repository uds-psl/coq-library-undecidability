(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW 
  Require Import utils list_bool pos vec
                 subcode sss compiler_correction.

From Undecidability.StackMachines.BSM
  Require Import bsm_defs.

From Undecidability.MinskyMachines.MM
  Require Import mm_defs mm_utils.

Set Implicit Arguments.
Set Default Goal Selector "!".

(* ** BSM reduces to MM *)

Tactic Notation "rew" "length" := autorewrite with length_db.

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).

Local Notation "I '/BSM/' s -1> t" := (bsm_sss I s t) (at level 70, no associativity).
Local Notation "P '/BSM/' s -+> t" := (sss_progress (@bsm_sss _) P s t) (at level 70, no associativity).
Local Notation "P '/BSM/' s ->> t" := (sss_compute (@bsm_sss _) P s t) (at level 70, no associativity).
Local Notation "P '/BSM/' s ~~> t" := (sss_output (@bsm_sss _) P s t) (at level 70, no associativity).
Local Notation "P '/BSM/' s ↓" := (sss_terminates (@bsm_sss _) P s)(at level 70, no associativity).

Local Notation "P '/MM/' s -+> t" := (sss_progress (@mm_sss _) P s t) (at level 70, no associativity).
Local Notation "P '/MM/' s ->> t" := (sss_compute (@mm_sss _) P s t) (at level 70, no associativity).
Local Notation "P '/MM/' s '~~>' t" := (sss_output (@mm_sss _) P s t) (at level 70, no associativity).
Local Notation "P '/MM/' s ↓" := (sss_terminates (@mm_sss _) P s)(at level 70, no associativity).

Section bsm_mm0_simulator.

  Ltac dest x y := destruct (pos_eq_dec x y) as [ | ]; [ subst x | ]; rew vec.

  Variables (m : nat).

  (** We consider BSM with m stacks and build a compiler to MM with 2+m registers. 
      Each stack i : pos m is encoded in registers 2+i : pos (2+m) using stack_enc.
      The extra registers are tmp1 := pos0 and tmp2 := pos1. *)

  (* The registers of the MM *)

  Let n := 2+m.
  Let tmp1 :  pos n := pos0.
  Let tmp2 :  pos n := pos1.
  Let reg p : pos n := pos_nxt (pos_nxt p).
   
  Local Fact Hv12 : tmp1 <> tmp2.             Proof. discriminate. Qed.
  Local Fact Hvr1 : forall p, reg p <> tmp1.  Proof. discriminate. Qed.
  Local Fact Hvr2 : forall p, reg p <> tmp2.  Proof. discriminate. Qed.
  Local Fact Hreg : forall p q, reg p = reg q -> p = q.
  Proof. intros ? ? H; do 2 apply pos_nxt_inj; apply H. Qed.

  Hint Resolve Hv12 Hvr1 Hvr2 Hreg : core.

  (* The encoding of BSM states *)

  Definition bsm_state_enc (v : vec _ m) := 0##0##vec_map stack_enc v.

  Definition bsm_state_equiv (v : vec _ m) w := 
            w#>tmp1 = 0
         /\ w#>tmp2 = 0
         /\ forall p, w#>(reg p) = stack_enc (v#>p).

  Infix "⋈" := bsm_state_equiv (at level 70, no associativity).

  Fact bsm_state_enc_spec v : v ⋈ bsm_state_enc v.
  Proof. 
    red; unfold tmp1, tmp2; repeat split; rew vec.
    intros p; unfold reg; simpl.
    rewrite vec_pos_map; trivial.
  Qed.

  (* The compiler from the generic one: we only need to
     explain how to simulate each individual instruction *)

  Section bsm_mm_compiler.

    Implicit Type ρ : bsm_instr m.

    Local Definition bsm_instr_compile lnk i ρ :=
      match ρ with
        | PUSH s Zero => mm_push_Zero (reg s) tmp1 tmp2 (lnk i)
        | PUSH s One  => mm_push_One  (reg s) tmp1 tmp2 (lnk i)
        | POP  s j k  => mm_pop (reg s) tmp1 tmp2 (lnk i) (lnk j) (lnk (1+i)) (lnk k)
      end.

    Local Definition bsm_instr_compile_length ρ :=
      match ρ with 
        | PUSH _ Zero => 7
        | PUSH _ One  => 8
        | POP  _ _ _  => 16
      end.

    Local Fact bsm_instr_compile_length_eq lnk i ρ : 
          length (bsm_instr_compile lnk i ρ) = bsm_instr_compile_length ρ.
    Proof. destruct ρ as [ | ? [] ]; simpl; auto. Qed.

    Hint Resolve bsm_instr_compile_length_eq : core.

    (* This main soundness lemma per simulated instruction *)

    Lemma bsm_instr_compile_sound : 
        instruction_compiler_sound bsm_instr_compile 
                                   (@bsm_sss _) 
                                   (@mm_sss _) 
                                   bsm_state_equiv.
    Proof.
      intros lnk ρ i1 v1 i2 v2 w1 H; revert H w1.
      change v1 with (snd (i1,v1)) at 2.
      change i1 with (fst (i1,v1)) at 2 3 4 6 7 8.
      change v2 with (snd (i2,v2)) at 2.
      change i2 with (fst (i2,v2)) at 2.
      generalize (i1,v1) (i2,v2); clear i1 v1 i2 v2.
      induction 1 as    [ i p j k v Hv
                        | i p j k v ll Hll 
                        | i p j k v ll Hll
                        | i p [] v
                        ]; simpl; intros w1 H0 H; generalize H; intros (H1 & H2 & H3).

      + exists w1; split; auto.
        apply mm_pop_void_progress; auto using Hv12, Hvr1, Hvr2.
        rewrite H3, Hv; auto.

      + exists (w1[(stack_enc ll)/reg p]); repeat split; auto; rew vec.
        * apply mm_pop_Zero_progress; auto using Hv12, Hvr1, Hvr2.
          rewrite H3, Hll; auto.
        * intros q; dest p q.
          assert (reg p <> reg q); rew vec.
    
      + exists (w1[(stack_enc ll)/reg p]); repeat split; auto; rew vec.
        * apply mm_pop_One_progress; auto using Hv12, Hvr1, Hvr2.
          rewrite H3, Hll; auto.
        * intros q; dest p q.
          assert (reg p <> reg q); rew vec.
   
      + exists (w1[(stack_enc (One::v#>p))/reg p]); repeat split; auto; rew vec.
        1: rewrite H0; apply mm_push_One_progress; auto using Hv12, Hvr1, Hvr2.
        intros q; dest p q.
        assert (reg p <> reg q); rew vec.

      + exists (w1[(stack_enc (Zero::v#>p))/reg p]); repeat split; auto; rew vec.
        1: rewrite H0; apply mm_push_Zero_progress; auto using Hv12, Hvr1, Hvr2.
        intros q; dest p q.
        assert (reg p <> reg q); rew vec.
    Qed.

    Hint Resolve bsm_instr_compile_sound : core.

    Theorem bsm_mm_compiler : compiler_t (@bsm_sss _) (@mm_sss _) bsm_state_equiv.
    Proof.
      apply generic_compiler 
        with (icomp := bsm_instr_compile)
             (ilen := bsm_instr_compile_length); auto.
      + apply bsm_sss_total'.
      + apply mm_sss_fun.
    Qed.

  End bsm_mm_compiler.

  (* Using the compiler, we can simulate any BSM with a MM *)

  Theorem bsm_mm_simulator i (P : list (@bsm_instr m)) : 
         { Q : list (@mm_instr (pos n)) 
         | forall v w, v ⋈ w 
         ->   (forall i' v', (i,P) /BSM/ (i,v) ~~> (i',v') -> exists w', (1,Q) /MM/ (1,w) ~~> (1+length Q,w') /\ v' ⋈ w')
           /\ ((1,Q) /MM/ (1,w) ↓  -> (i,P) /BSM/ (i,v) ↓) 
         }.
  Proof.
    exists (gc_code bsm_mm_compiler (i,P) 1).
    intros v w Hw; split.
    + intros ? ?; now apply (compiler_t_output_sound' bsm_mm_compiler). 
    + apply compiler_t_term_equiv; auto.
  Qed.

  (* We simulate a BSM (i,P) with a MM (1,Q) such that
        (i,P) terminates iff (1,Q) terminates iff (1,Q) terminates on zero *)

  Section bsm_mm0_sim.

    Variables (i : nat) (P : list (bsm_instr m)).

    Let Q := proj1_sig (bsm_mm_simulator i P).
    Let HQ := proj2_sig (bsm_mm_simulator i P).

    Definition bsm_mm0_sim := Q ++ mm_zeroify tmp1 (code_end (1,Q)).

    Notation R := bsm_mm0_sim.

    Theorem bsm_mm0_sim_spec v w : 
           v ⋈ w 
        -> ((i,P) /BSM/ (i,v) ↓ -> (1,R) /MM/ (1,w) ~~> (0,vec_zero))
        /\ ((1,R) /MM/ (1,w) ~~> (0,vec_zero) -> (1,R) /MM/ (1,w) ↓)
        /\ ((1,R) /MM/ (1,w) ↓ -> (i,P) /BSM/ (i,v) ↓).
    Proof.
      intros Hw; split; [ | split ].
      + intros ((i',v') & H).
        apply (HQ Hw) in H as (w' & (H1 & H2) & H3); fold Q in H1, H2; unfold fst in H2.
        unfold bsm_mm0_sim; split; [ | simpl; lia ]. 
        apply subcode_sss_compute_trans with (2 := H1); auto.
        unfold code_end, fst, snd.
        assert (w'#>tmp1 = 0) by apply H3.
        apply sss_progress_compute, subcode_sss_progress with (2 := mm_zeroify_spec _ _ _ H); auto.
      + exists (0,vec_zero); auto.
      + intros H2; apply HQ with (1 := Hw).
        revert H2; apply subcode_sss_terminates.
        unfold R, Q; auto.
    Qed.

    Corollary bsm_mm0_terminates v w :
        v ⋈ w -> (i,P) /BSM/ (i,v) ↓ <-> (1,R) /MM/ (1,w) ↓.
    Proof. intros Hw; split; intro; repeat (apply bsm_mm0_sim_spec with (1 := Hw); auto). Qed.

    Corollary bsm_mm0_terminates_on_zero v w :
        v ⋈ w -> (i,P) /BSM/ (i,v) ↓ <-> (1,R) /MM/ (1,w) ~~> (0,vec_zero).
    Proof. intros Hw; split; intro; repeat (apply bsm_mm0_sim_spec with (1 := Hw); auto). Qed.

    End bsm_mm0_sim.

End bsm_mm0_simulator.

#[local] Hint Resolve bsm_state_enc_spec : core.

(* Both compilers below produce the same code *)

Theorem bsm_mm_compiler_1 n i (P : list (bsm_instr n)) :
  { Q : list (mm_instr (pos (2+n))) | forall v, (i,P) /BSM/ (i,v) ↓ <-> (1,Q) /MM/ (1,bsm_state_enc v) ↓ }.
Proof. exists (bsm_mm0_sim i P); intro; apply bsm_mm0_terminates; auto. Qed.

Theorem bsm_mm_compiler_2 n i (P : list (bsm_instr n)) :
  { Q : list (mm_instr (pos (2+n))) | forall v, (i,P) /BSM/ (i,v) ↓ <-> (1,Q) /MM/ (1,bsm_state_enc v) ~~> (0,vec_zero) }.
Proof. exists (bsm_mm0_sim i P); intro; apply bsm_mm0_terminates_on_zero; auto. Qed.
