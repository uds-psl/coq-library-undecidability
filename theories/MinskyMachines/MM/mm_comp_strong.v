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
  Require Import utils list_bool pos vec
                 subcode sss compiler_correction.

From Undecidability.StackMachines.BSM
  Require Import bsm_defs.

From Undecidability.MinskyMachines.MM
  Require Import mm_defs mm_utils. 

Set Implicit Arguments.

Set Default Proof Using "Type".

(* ** BSM recues to MM *)

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

Section simulator.

  Ltac dest x y := destruct (pos_eq_dec x y) as [ | ]; [ subst x | ]; rew vec.

  Variables (m : nat).
  
  (* each stack of the BSM corresponds to a (unique) register in the MM 
      and there are extra registers: tmp1, tmp2 which must have value 0 at start 
      they might change value during a simulated BSM instruction but when
      the instruction is finished, their values are back to 0 

      This is expressed in the below bsm_state_enc invariant
  *)
  
  Let n := m + 2.
  Variable tmp1 : pos n. 
  Variable tmp2 : pos n.
  Variable reg : pos m -> pos n.
   
  Hypothesis Hv12 : tmp1 <> tmp2.
  Hypothesis Hvr1 : forall p, reg p <> tmp1. 
  Hypothesis Hvr2 : forall p, reg p <> tmp2.
  
  Hypothesis Hreg : forall p q, reg p = reg q -> p = q.

  Variable cases : forall p : pos n, {p = tmp1} + {p = tmp2} + {q | p = reg q}.

  Definition bsm_state_enc (v : vec (list bool) m) w := 
            w#>tmp1 = 0
         /\ w#>tmp2 = 0
         /\ forall p, w#>(reg p) = stack_enc (v#>p).

  (* i is the position in the source code *)

  Definition bsm_instr_compile lnk i ii :=
    match ii with
      | PUSH s Zero => mm_push_Zero (reg s) tmp1 tmp2 (lnk i)
      | PUSH s One  => mm_push_One  (reg s) tmp1 tmp2 (lnk i)
      | POP  s j k  => mm_pop (reg s) tmp1 tmp2 (lnk i) (lnk j) (lnk (1+i)) (lnk k)
    end.

  Definition bsm_instr_compile_length (ii : bsm_instr m) :=
    match ii with 
      | PUSH _ Zero => 7
      | PUSH _ One  => 8
      | POP  _ _ _  => 16
    end.

  Fact bsm_instr_compile_length_eq lnk i ii : length (bsm_instr_compile lnk i ii) = bsm_instr_compile_length ii.
  Proof. destruct ii as [ | ? [] ]; simpl; auto. Qed.
    
  Fact bsm_instr_compile_length_geq ii : 1 <= bsm_instr_compile_length ii.
  Proof. destruct ii as [ | ? [] ]; simpl; auto; lia. Qed.

  Hint Resolve bsm_instr_compile_length_eq bsm_instr_compile_length_geq : core.

  (* This main soundness lemma per simulated instruction *)

  Lemma bsm_instr_compile_sound : instruction_compiler_sound bsm_instr_compile (@bsm_sss _) (@mm_sss _) bsm_state_enc.
  Proof using Hvr1 Hvr2 Hv12 Hreg.
    intros lnk I i1 v1 i2 v2 w1 H; revert H w1.
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
      * rewrite vec_change_neq. 2: congruence. eauto. 
      * rewrite vec_change_neq. 2: congruence. eauto. 
      * intros q; dest p q.
        assert (reg p <> reg q); rew vec.
    
    + exists (w1[(stack_enc ll)/reg p]); repeat split; auto; rew vec.
      * apply mm_pop_One_progress; auto using Hv12, Hvr1, Hvr2.
        rewrite H3, Hll; auto.
      * rewrite vec_change_neq. 2: congruence. eauto. 
      * rewrite vec_change_neq. 2: congruence. eauto. 
      * intros q; dest p q.
        assert (reg p <> reg q); rew vec.
   
    + exists (w1[(stack_enc (One::v#>p))/reg p]); repeat split; auto; rew vec.
      2:{ rewrite vec_change_neq. 2: congruence. eauto. } 
      2:{ rewrite vec_change_neq. 2: congruence. eauto. }
      rewrite H0; apply mm_push_One_progress; auto using Hv12, Hvr1, Hvr2.
      intros q; dest p q.
      assert (reg p <> reg q); rew vec.

    + exists (w1[(stack_enc (Zero::v#>p))/reg p]); repeat split; auto; rew vec.
      rewrite H0; apply mm_push_Zero_progress; auto using Hv12, Hvr1, Hvr2.
      * rewrite vec_change_neq. 2: congruence. eauto. 
      * rewrite vec_change_neq. 2: congruence. eauto. 
      * intros q; dest p q.
        assert (reg p <> reg q); rew vec.
  Qed.

  Hint Resolve bsm_instr_compile_sound : core.

  Section bsm_sim.

    Variable (iP : nat) (cP : list (bsm_instr m)) (iQ : nat).

    Local Definition lnk_Q_pair := @gen_compiler_correction _ _ _ _ bsm_instr_compile_length_eq _ _ _ _  (@bsm_sss_total' _)
                     (@mm_sss_fun _) _ bsm_instr_compile_sound (iP,cP) iQ. 

    Local Definition lnk := projT1 lnk_Q_pair.
    Local Definition Q := proj1_sig (projT2 lnk_Q_pair).
    
    Local Lemma code_endQ : code_end Q = iQ + length (snd Q).
    Proof.
      unfold Q, lnk_Q_pair. cbn.
      f_equal. now destruct gen_compiler_correction as (? & ? & ? & ?); cbn.
    Qed.

    Local Lemma Hlnk : fst Q = iQ /\ lnk iP = iQ /\ forall i, out_code i (iP,cP) -> lnk i = code_end Q.
    Proof.
      repeat split; apply (proj2_sig (projT2 lnk_Q_pair)).
    Qed.

    Infix "⋈" := bsm_state_enc (at level 70, no associativity).

    Local Lemma HQ1 : forall i1 v1 w1 i2 v2, v1 ⋈ w1 /\ (iP,cP) /BSM/ (i1,v1) ~~> (i2,v2)     
                    -> exists w2,    v2 ⋈ w2 /\ Q /MM/ (lnk i1,w1) ~~> (lnk i2,w2).
    Proof. apply (proj2_sig (projT2 lnk_Q_pair)). Qed.

    Local Lemma HQ2 : forall i1 v1 w1 j2 w2, v1 ⋈ w1 /\ Q /MM/ (lnk i1,w1) ~~> (j2,w2) 
                    -> exists i2 v2, v2 ⋈ w2 /\ (iP,cP) /BSM/ (i1,v1) ~~> (i2,v2) /\ j2 = lnk i2.
    Proof. apply (proj2_sig (projT2 lnk_Q_pair)). Qed.

    Variable v : vec (list bool) m. 

    Definition vec_enc v := vec_set_pos (fun p => match cases p with inl _ => 0 | inr (exist _ q _) => (stack_enc (v#>q)) end).

    Local Definition w := vec_enc v.

    Let vec_enc_spec : forall v, bsm_state_enc v (vec_enc v).
    Proof.
      red; unfold vec_enc; repeat split; rew vec.
      - destruct (cases tmp1) as [[ | ] | [q Hq]]; try firstorder congruence.
      - destruct (cases tmp2) as [[ | ] | [q Hq]]; try firstorder congruence.
      - intros p. rewrite vec_pos_set.  destruct (cases (reg p)) as [[ | ] | [q Hq]]; try now firstorder congruence.
    Qed.

    Let w_prop : bsm_state_enc v w.
    Proof.
      eapply vec_enc_spec.
    Qed.

    (* (iQ,cQ) simulates termination of (iP,cP) while ensuring tmp1 and tmp2 stay void when it terminates *)

    Local Lemma Q_spec1 : (iP,cP) /BSM/ (iP,v) ↓ -> exists w', Q /MM/ (iQ,w) ~~> (code_end Q, w') /\ w'#>tmp1 = 0 /\ w'#>tmp2 = 0.
    Proof.
      intros ((i1,v1) & H1).
      destruct HQ1 with (1 := conj w_prop H1) as (w' & H2 & H3).
      rewrite <- (proj2 (proj2 Hlnk) i1), <- (proj1 (proj2 Hlnk)).
      * exists w'; split; auto; red in H2; tauto.
      * apply H1.
    Qed.

    Local Lemma Q_spec1_strong i1 v1 : (iP,cP) /BSM/ (iP,v) ~~> (i1, v1) -> Q /MM/ (iQ,w) ~~> (code_end Q, vec_enc v1).
    Proof.
      intros H1.
      destruct HQ1 with (1 := conj w_prop H1) as (w' & H2 & H3).
      rewrite <- (proj2 (proj2 Hlnk) i1), <- (proj1 (proj2 Hlnk)).
      * eenough (w' = vec_enc v1) as <- by eassumption.
        destruct H2 as (H2 & H4 & H5).
        eapply vec_pos_ext. intros p. unfold vec_enc. rewrite vec_pos_set.
        destruct (cases p) as [[E | E ] | [q E]]; subst; rew vec.
      * apply H1.
    Qed.    

    Local Lemma Q_spec2 : Q /MM/ (iQ,w) ↓ -> (iP,cP) /BSM/ (iP,v) ↓.
    Proof.
      intros ((j,w2) & H1).
      rewrite <- (proj1 (proj2 Hlnk)) in H1.
      destruct HQ2 with (1 := conj w_prop H1) as (i2 & v2 & H2 & H3 & _).
      exists (i2,v2); auto.
    Qed.

    Definition bsm_mm_sim := snd Q.

    Theorem bsm_mm_sim_spec : (iP,cP) /BSM/ (iP,v) ↓ <-> (iQ,bsm_mm_sim) /MM/ (iQ,w) ↓.
    Proof.
      rewrite <- (proj1 Hlnk) at 1.
      rewrite <- surjective_pairing.
      split; auto using Q_spec2.
      intros H.
      destruct (Q_spec1 H) as (w' & H1 & _).
      exists (code_end Q, w'); auto.
    Qed.

    Theorem bsm_mm_sim_spec_strong i1 v1 : (iP,cP) /BSM/ (iP,v) ~~> (i1, v1) -> (iQ,bsm_mm_sim) /MM/ (iQ,w) ~~> (iQ + length bsm_mm_sim, vec_enc v1).
    Proof.
      rewrite <- (proj1 Hlnk) at 1.
      rewrite <- surjective_pairing.
      unfold bsm_mm_sim. rewrite <- code_endQ.
      apply Q_spec1_strong.
    Qed.

    End bsm_sim.

End simulator.

Theorem bsm_mm_compiler_strong n i (P : list (bsm_instr n)) (tmp1 tmp2 : pos (n + 2)) (reg : pos n -> pos (n + 2)) iQ :
  tmp1 <> tmp2 -> (forall p, tmp1 <> reg p) -> (forall p, tmp2 <> reg p) -> (forall p q, reg p = reg q -> p = q) ->
  forall cases : (forall p : pos _, {p = tmp1} + {p = tmp2} + {q | p = reg q}),
  { Q : list (mm_instr (pos (n+2))) | (forall v, (i,P) /BSM/ (i,v) ↓ <-> (iQ,Q) /MM/ (iQ,(@vec_enc _ tmp1 tmp2 reg cases v)) ↓) /\
                                      forall v j w, (i,P) /BSM/ (i,v) ~~> (j,w) -> (iQ,Q) /MM/ (iQ, @vec_enc _ tmp1 tmp2 reg cases v) ~~> (iQ + length Q, @vec_enc _ tmp1 tmp2 reg cases w) }.
Proof. 
  intros.    
  unshelve eexists (@bsm_mm_sim _ tmp1 tmp2 reg _ _ _ _ i P _); eauto.
  split.
  - apply bsm_mm_sim_spec.
  - intros. match goal with [ |- context[ iQ + length ?Q ]] => change (iQ + length Q) with (code_end (iQ, Q)) end.
    eapply bsm_mm_sim_spec_strong; eauto.
Qed.