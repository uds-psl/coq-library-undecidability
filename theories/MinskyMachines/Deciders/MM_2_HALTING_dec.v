(*
  Autor(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  Decision Procedure(s):
    Two-counter Minsky Machine Halting (MM_2_HALTING)
*)

Require Import PeanoNat Lia List.
Import ListNotations.

From Undecidability.MinskyMachines Require Import MM MM_sss.
Require Undecidability.MinskyMachines.Deciders.MPM2_HALT_dec.
Module MPM2 := MPM2_HALT_dec.

From Undecidability.Shared.Libs.DLW
  Require Import Vec.pos Vec.vec Code.sss.

Require Import Undecidability.CounterMachines.Util.Facts.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

#[local] Notation "P // s ↓" := (sss_terminates (@mm_sss _) P s).
#[local] Notation "P // r ->> s" := (sss_compute (@mm_sss _) P r s).

Section Construction.
Context (P : list (mm_instr (pos 2))).

Lemma decompose_vec2 {X : Type} (v : vec X 2) : v = vec_head v ## vec_head (vec_tail v) ## vec_nil.
Proof.
  by rewrite [LHS](vec_head_tail v) [in LHS](vec_head_tail (vec_tail v)) [in LHS](vec_0_nil (vec_tail (vec_tail v))).
Qed.

Lemma case_pos2 (v : pos 2) : (v = Fin.F1) + (v = Fin.FS Fin.F1).
Proof.
  have [?|] := pos_S_inv v; first by left.
  move=> [w] ->. right.
  have [->|] := pos_S_inv w; first done.
  move=> [?]. exfalso. by apply: pos_O_inv.
Qed.

Definition to_Instruction (i : mm_instr (pos 2)) : MPM2.Instruction :=
  match i with
  | INC d => MPM2.inc (if case_pos2 d then false else true)
  | DEC d p => MPM2.dec (if case_pos2 d then false else true) (if p is S q then q else length P)
  end.

Definition to_Config (s : mm_state 2) : MPM2.Config :=
  match s with
  | (S p, Vector.cons _ a _ (Vector.cons _ b _ _)) => (p, (a, b))
  | (0, Vector.cons _ a _ (Vector.cons _ b _ _)) => (length P, (a, b))
  | _ => (0, (0, 0))
  end.

(* corresponding Mpm 2 *)
Definition M := map to_Instruction P.

Lemma P_to_M_step s t : sss_step (@mm_sss _) (1, P) s t -> MPM2.step M (to_Config s) = Some (to_Config t).
Proof.
  rewrite /sss_step.
  move=> [k] [P1] [i] [P2] [v] [[<- HP]] [->].
  rewrite /MPM2.step.
  have -> : nth_error M (MPM2.state (to_Config (1 + length P1, v))) = Some (to_Instruction i).
  { rewrite /M HP map_app (decompose_vec2 v) nth_error_app2.
    { by rewrite /= map_length. }
    by rewrite /= map_length Nat.sub_diag. }
  move Hc: (1 + length P1, v) => c H.
  case: H Hc.
  - move=> ? d w [<- <-]. rewrite [to_Instruction _]/= (decompose_vec2 v).
    by case: (case_pos2 d) => /= ->.
  - move=> ? d q w + [<- ?]. subst w. rewrite (decompose_vec2 v) /=.
    case: (case_pos2 d).
    + move=> /= -> ->. by case: q.
    + move=> /= -> ->. by case: q.
  - move=> ? d q w u + [<- ?]. subst w. rewrite (decompose_vec2 v) /=.
    case: (case_pos2 d).
    + by move=> /= -> ->.
    + by move=> /= -> ->.
Qed.

Lemma P_to_M s t : ((1, P) // s ->> t) ->
  exists n, Nat.iter n (obind (MPM2.step M)) (Some (to_Config s)) = Some (to_Config t).
Proof.
  move=> [n Hn]. exists n.
  elim: n s Hn. { by move=> s /sss_steps_0_inv <-. }
  move=> n IH s /sss_steps_S_inv' [u] [/P_to_M_step Hsu] /IH {}IH.
  by rewrite /= obind_oiter Hsu.
Qed.

Lemma M_to_P_step s y : MPM2.step M (to_Config s) = Some y ->
  exists t, y = to_Config t /\ sss_step (@mm_sss _) (1, P) s t.
Proof.
  rewrite /MPM2.step. case Hi: (nth_error M (MPM2.state (to_Config s))) => [i|]; last done.
  case: i Hi.
  - done.
  - rewrite /M. move=> ? /(@nth_error_In MPM2.Instruction) /in_map_iff.
    by move=> [[]] /= => [?|??] [].
  - move=> c. rewrite /M nth_error_map.
    case Hi: (nth_error P (MPM2.state (to_Config s))) => [i|]; last done.
    move: Hi => /(@nth_error_split (mm_instr _)) [P1] [P2] [HP HP1] [Hi] [<-].
    move: s HP1 => [p v] HP1.
    have Hp : p = S (p - 1).
    { move: p HP1 => [|p].
      { rewrite (decompose_vec2 v) /= HP app_length /=. lia. }
      move=> ? /=. lia. }
    exists (S (S (MPM2.state (to_Config (p, v)))),
      ((if c then 0 else 1) + MPM2.value1 (to_Config (p, v))) ##
      ((if c then 1 else 0) + MPM2.value2 (to_Config (p, v))) ##
      vec_nil).
    split; first done.
    exists 1, P1, i, P2, v.
    split; first by congr pair.
    split. 
    { move: HP1. by rewrite (decompose_vec2 v) Hp /= => <-. }
    have -> : i = INC (if c then pos1 else pos0).
    { move: i Hi {HP} => []; last done. move=> d /=.
      by case: (case_pos2 d) => /= -> [<-]. }
    have := @in_mm_sss_inc 2 p (if c then pos1 else pos0) v.
    congr mm_sss. congr pair. { by rewrite (decompose_vec2 v) Hp. }
    case: c {Hi}.
    + by rewrite (decompose_vec2 v) Hp /=.
    + by rewrite (decompose_vec2 v) Hp /=.
  - move=> c q.
    rewrite /M nth_error_map.
    case Hi: (nth_error P (MPM2.state (to_Config s))) => [i|]; last done.
    move: Hi => /(@nth_error_split (mm_instr _)) [P1] [P2] [HP HP1] [Hi] [<-].
    move: s HP1 => [p v] HP1.
    have Hp : p = S (p - 1).
    { move: p HP1 => [|p].
      { rewrite (decompose_vec2 v) /= HP app_length /=. lia. }
      move=> ? /=. lia. }
    move: HP1. rewrite (decompose_vec2 v) Hp /= => HP1.
    move: i HP Hi => [] /=; first done.
    move=> d r.
    move: (case_pos2 d) => [|] /= -> HP [] <- <-.
    + exists (if (vec_head v) is S a then
        (S p, a ## vec_head (vec_tail v) ## vec_nil) else 
        (r, 0 ## vec_head (vec_tail v) ## vec_nil)).
      split.
      { case: (vec_head v).
        - by case: (r).
        - move=> ?. by rewrite [in to_Config _]Hp /to_Config. }
      case Hv: (vec_head v) => [|a].
      * exists 1, P1, (DEC pos0 r), P2, v.
        split; first by congr pair.
        split. 
        { by rewrite [in (_, v)](decompose_vec2 v) /= HP1 Hv. }
        have := @in_mm_sss_dec_0 2 p pos0 r v.
        rewrite [in vec_pos v](decompose_vec2 v) /=.
        move=> /(_ Hv).
        by congr mm_sss; rewrite -?Hp [in (_, v)](decompose_vec2 v) Hv.
      * exists 1, P1, (DEC pos0 r), P2, v.
        split; first by congr pair.
        split. 
        { by rewrite [in (_, v)](decompose_vec2 v) /= HP1 Hv. }
        have := @in_mm_sss_dec_1 2 p pos0 r v.
        rewrite [in vec_pos v](decompose_vec2 v) /=.
        move=> /(_ a Hv).
        congr mm_sss; rewrite -?Hp.
        ** by rewrite -Hv -(decompose_vec2 v).
        ** by rewrite [in vec_change v](decompose_vec2 v).
    + exists (if (vec_head (vec_tail v)) is S b then
        (S p, vec_head v ## b ## vec_nil) else 
        (r, vec_head v ## 0 ## vec_nil)).
      split.
      { case: (vec_head (vec_tail v)).
        - by case: (r).
        - move=> ?. by rewrite [in to_Config _]Hp /to_Config. }
      case Hv: (vec_head (vec_tail v)) => [|b].
      * exists 1, P1, (DEC pos1 r), P2, v.
        split; first by congr pair.
        split. 
        { by rewrite [in (_, v)](decompose_vec2 v) /= HP1 Hv. }
        have := @in_mm_sss_dec_0 2 p pos1 r v.
        rewrite [in vec_pos v](decompose_vec2 v) /=.
        move=> /(_ Hv).
        by congr mm_sss; rewrite -?Hp [in (_, v)](decompose_vec2 v) Hv.
      * exists 1, P1, (DEC pos1 r), P2, v.
        split; first by congr pair.
        split. 
        { by rewrite [in (_, v)](decompose_vec2 v) /= HP1 Hv. }
        have := @in_mm_sss_dec_1 2 p pos1 r v.
        rewrite [in vec_pos v](decompose_vec2 v) /=.
        move=> /(_ b Hv).
        congr mm_sss; rewrite -?Hp.
        ** by rewrite -Hv -(decompose_vec2 v).
        ** by rewrite [in vec_change v](decompose_vec2 v).
Qed.

Lemma M_to_P n s y : Nat.iter n (obind (MPM2.step M)) (Some (to_Config s)) = Some y ->
  exists t, y = to_Config t /\ ((1, P) // s ->> t).
Proof.
  move=> Hn.
  suff : exists t : mm_state 2, y = to_Config t /\ sss_steps (@mm_sss _) (1, P) n s t.
  { move=> [t] [? ?]. exists t. split; [done|by exists n]. }
  elim: n s Hn.
  { move=> s [<-]. exists s. split; first done. by apply: sss_steps_0. }
  move=> n IH s /=. rewrite obind_oiter.
  case Hz: (MPM2.step M (to_Config s)) => [z|]; last by rewrite oiter_None.
  move: Hz => /M_to_P_step [u] [->] Hsu.
  move=> /IH [t] [? ?]. exists t.
  split; first done. have ->: S n = 1 + n by done.
  apply: sss_steps_trans; last by eassumption.
  by apply: sss_steps_1.
Qed.

#[local] Arguments to_Config : simpl never.

(* informative decision statement for halting for Mm2 *)
Lemma decision (v: vec nat 2) : ((1, P) // (1, v) ↓) + (not ((1, P) // (1, v) ↓)).
Proof.
  have [H|H] := MPM2.decision M (to_Config (1, v)).
  - left. move: H => [n]. elim: n; first done.
    move=> n IH /=.
    case Hy: (MPM2.steps M n (to_Config (1, v))) => [y|].
    + move: Hy => /M_to_P [t] [->] Ht H't.
      exists t. split; first done.
      move: t {Ht} H't => [[|p] w] /=; first by lia.
      rewrite (decompose_vec2 w) /to_Config /= /MPM2.step /=.
      case Hi: (nth_error M p) => [i|]; first last.
      { move: Hi => /nth_error_None. rewrite /M map_length. lia. }
      case: i Hi; [|done..].
      move=> /(@nth_error_In MPM2.Instruction) /in_map_iff.
      by move=> [[]] => [?|??] [].
    + by move: (IH Hy).
  - right. move=> [t] [/=] /P_to_M [n] Hn Ht.
    apply: (H (S n)).
    rewrite /= /MPM2.steps Hn.
    move: t Ht {Hn} => [[|p] w].
    + rewrite /= /MPM2.step /to_Config (decompose_vec2 w) /=.
      suff ->: nth_error M (length P) = None by done.
      apply /nth_error_None. by rewrite /M map_length.
    + move=> /= [|?]; first by lia.
      rewrite /= /MPM2.step /to_Config (decompose_vec2 w) /=.
      suff ->: nth_error M p = None by done.
      apply /nth_error_None. rewrite /M map_length. lia.
Qed.

End Construction.

Require Import Undecidability.Synthetic.Definitions.

(* decision procedure for the halting problem for MM with two counters *)
Definition decide : { P : list (mm_instr (pos 2)) & vec nat 2 } -> bool :=
  fun '(existT _ P v) =>
    match decision P v with
    | inl _ => true
    | inr _ => false
    end.

(* decision procedure correctness *)
Lemma decide_spec : decider decide MM_2_HALTING.
Proof.
  rewrite /decider /reflects /decide => - [P v].
  case: (decision P v).
  - tauto.
  - move=> H. split; [by move=> /H | done].
Qed.
