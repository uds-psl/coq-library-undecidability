(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Arith Lia.

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
  
  Let n := m + 3.
  Variable tmp1 : pos n. 
  Variable tmp2 : pos n.
  Variable tmp3 : pos n.
  Variable reg : pos m -> pos n.
   
  Hypothesis Hv12 : tmp1 <> tmp2.
  Hypothesis Hvr1 : forall p, reg p <> tmp1. 
  Hypothesis Hvr2 : forall p, reg p <> tmp2.
  Hypothesis Hv13 : tmp1 <> tmp3.
  Hypothesis Hv23 : tmp2 <> tmp3.
  Hypothesis Hvr3 : forall p, reg p <> tmp3.
  
  Hypothesis Hreg : forall p q, reg p = reg q -> p = q.

  Variable cases : forall p : pos n, {p = tmp1} + {p = tmp2} + {p = tmp3} + {q | p = reg q}.

  Definition bsm_state_enc (v : vec (list bool) m) w := 
            w#>tmp1 = 0
         /\ w#>tmp2 = 0
         /\ w#>tmp3 = 0
         /\ forall p, w#>(reg p) = stack_enc (v#>p).

  Fact bsm_state_enc_fun (v : vec (list bool) m) w1 w2 :
       bsm_state_enc v w1 -> bsm_state_enc v w2 -> w1 = w2.
  Proof using cases.
    intros (H0 & H1 & H2 & H3) (H4 & H5 & H6 & H7).
    apply vec_pos_ext; intros p.
    destruct (cases p) as [ [ [ -> | -> ] | -> ] | (q & ->) ]; try lia.
    now rewrite H3, H7.
  Qed.

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
  Proof using Hvr1 Hvr2 Hvr3 Hv12 Hv13 Hv23 Hreg.
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
                      ]; simpl; intros w1 H0 H; generalize H; intros (H1 & H2 & Htmp3 & H3).

    + exists w1; split; auto.
      apply mm_pop_void_progress; auto using Hv12, Hvr1, Hvr2.
      rewrite H3, Hv; auto.

    + exists (w1[(stack_enc ll)/reg p]); repeat split; auto; rew vec.
      * apply mm_pop_Zero_progress; auto using Hv12, Hvr1, Hvr2.
        rewrite H3, Hll; auto.
      * rewrite vec_change_neq. 2: congruence. eauto. 
      * rewrite vec_change_neq. 2: congruence. eauto.
      * rewrite vec_change_neq. 2: congruence. eauto.
      * intros q; dest p q.
        assert (reg p <> reg q); rew vec.
    
    + exists (w1[(stack_enc ll)/reg p]); repeat split; auto; rew vec.
      * apply mm_pop_One_progress; auto using Hv12, Hvr1, Hvr2.
        rewrite H3, Hll; auto.
      * rewrite vec_change_neq. 2: congruence. eauto. 
      * rewrite vec_change_neq. 2: congruence. eauto. 
      * rewrite vec_change_neq. 2: congruence. eauto. 
      * intros q; dest p q.
        assert (reg p <> reg q); rew vec.
   
    + exists (w1[(stack_enc (One::v#>p))/reg p]); repeat split; auto; rew vec.
      2:{ rewrite vec_change_neq. 2: congruence. eauto. } 
      2:{ rewrite vec_change_neq. 2: congruence. eauto. }
      2:{ rewrite vec_change_neq. 2: congruence. eauto. }
      rewrite H0; apply mm_push_One_progress; auto using Hv12, Hvr1, Hvr2.
      intros q; dest p q.
      assert (reg p <> reg q); rew vec.

    + exists (w1[(stack_enc (Zero::v#>p))/reg p]); repeat split; auto; rew vec.
      rewrite H0; apply mm_push_Zero_progress; auto using Hv12, Hvr1, Hvr2.
      * rewrite vec_change_neq. 2: congruence. eauto. 
      * rewrite vec_change_neq. 2: congruence. eauto. 
      * rewrite vec_change_neq. 2: congruence. eauto. 
      * intros q; dest p q.
        assert (reg p <> reg q); rew vec.
  Qed.

  Hint Resolve bsm_instr_compile_sound : core.

  Theorem bsm_mm_compiler : compiler_t (@bsm_sss _) (@mm_sss _) bsm_state_enc.
  Proof using Hvr3 Hvr2 Hvr1 Hv23 Hv13 Hv12 Hreg.
    apply generic_compiler 
        with (icomp := bsm_instr_compile)
             (ilen := bsm_instr_compile_length); auto.
      + apply bsm_sss_total'.
      + apply mm_sss_fun.
  Qed.

  Theorem bsm_mm_simulator i (P : list (@bsm_instr m)) j : 
         { Q : list (@mm_instr (pos n)) 
         | forall v w, bsm_state_enc v w 
         ->   (forall i' v', (i,P) /BSM/ (i,v) ~~> (i',v') -> exists w', (j,Q) /MM/ (j,w) ~~> (j+length Q,w') /\ bsm_state_enc v' w')
           /\ ((j,Q) /MM/ (j,w) ↓  -> (i,P) /BSM/ (i,v) ↓) 
         }.
  Proof using Hvr3 Hvr2 Hvr1 Hv23 Hv13 Hv12 Hreg.
    exists (gc_code bsm_mm_compiler (i,P) j).
    intros v w Hw; split.
    + intros ? ?; now apply (compiler_t_output_sound' bsm_mm_compiler). 
    + apply compiler_t_term_equiv; auto.
  Qed.

  Definition vec_enc v := vec_set_pos (fun p => match cases p with inl _ => 0 | inr (exist _ q _) => (stack_enc (v#>q)) end).

  Local Fact vec_enc_spec : forall v, bsm_state_enc v (vec_enc v).
  Proof using Hvr3 Hvr2 Hvr1 Hv23 Hv13 Hv12 Hreg.
    red; unfold vec_enc; repeat split; rew vec.
    - destruct (cases tmp1) as [[ | ] | [q Hq]]; try firstorder congruence.
    - destruct (cases tmp2) as [[ | ] | [q Hq]]; try firstorder congruence.
    - destruct (cases tmp3) as [[ | ] | [q Hq]]; try firstorder congruence.
    - intros p. rewrite vec_pos_set.  destruct (cases (reg p)) as [[ | ] | [q Hq]]; try now firstorder congruence.
  Qed.

End simulator.

Theorem bsm_mm_compiler_strong n i (P : list (bsm_instr n)) (tmp1 tmp2 tmp3 : pos (n + 3)) (reg : pos n -> pos (n + 3)) iQ :
  tmp1 <> tmp2 -> (forall p, tmp1 <> reg p) -> (forall p, tmp2 <> reg p) -> (forall p q, reg p = reg q -> p = q) ->
  tmp1 <> tmp3 -> tmp2 <> tmp3 -> (forall p, tmp3 <> reg p) ->
  forall cases : (forall p : pos _, {p = tmp1} + {p = tmp2} + {p = tmp3} + {q | p = reg q}),
  { Q : list (mm_instr (pos (n+3))) | (forall v, (i,P) /BSM/ (i,v) ↓ <-> (iQ,Q) /MM/ (iQ,(@vec_enc _ tmp1 tmp2 tmp3 reg cases v)) ↓) /\
                                      forall v j w, (i,P) /BSM/ (i,v) ~~> (j,w) -> (iQ,Q) /MM/ (iQ, @vec_enc _ tmp1 tmp2 tmp3 reg cases v) ~~> (iQ + length Q, @vec_enc _ tmp1 tmp2 tmp3 reg cases w) }.
Proof. 
  intros.
  destruct bsm_mm_simulator with (tmp1 := tmp1) (tmp2 := tmp2) (tmp3 := tmp3) (reg := reg) (i := i) (P := P) (j := iQ)
    as (Q & HQ); auto.
  exists Q; split.
  + intros v; split.
    * intros ((j,w) & Hw).
      apply (HQ v (vec_enc _ cases v)) in Hw as (w' & Hw' & _).
      2: apply vec_enc_spec; auto.
      now exists (iQ+length Q,w').
    * apply HQ, vec_enc_spec; auto.
  + intros v j w G.
    destruct (HQ v (vec_enc _ cases v)) as [ HQ' _ ]. 
    1: apply vec_enc_spec; auto.
    destruct HQ' with (1 := G) as (w' & Hw1 & Hw2).
    assert (vec_enc _ cases w = w') as ->; auto.
    apply bsm_state_enc_fun with (3 := Hw2); auto.
    apply vec_enc_spec; auto.
Qed.