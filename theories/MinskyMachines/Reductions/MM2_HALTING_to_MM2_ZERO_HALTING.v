(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(* 
  Reduction(s):
    Halting of Minsky machines with two counters (MM2_HALTING) to
    Halting of Minsky machines with two counters starting from (0, 0) (MM2_ZERO_HALTING)
*)

Require Import List PeanoNat Lia Relations.Relation_Operators Relations.Operators_Properties.

Require Import Undecidability.MinskyMachines.MM2.
Require Import Undecidability.MinskyMachines.Util.MM2_facts.

Require Undecidability.Shared.deterministic_simulation.
Module sim := deterministic_simulation.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

Module Argument.
Section MM2_MM2.
  Variables (M : list mm2_instr) (a0 b0 : nat).

  Local Notation mm2_state := (nat*(nat*nat))%type.
  Local Notation mm2_reaches x y := (clos_refl_trans mm2_state (mm2_step M) x y).

  Definition shift_instr (mm2i : mm2_instr) : mm2_instr :=
    match mm2i with
    | mm2_dec_a q => mm2_dec_a (if q is 0 then 0 else q+a0+b0)
    | mm2_dec_b q => mm2_dec_b (if q is 0 then 0 else q+a0+b0)
    | _ => mm2i
    end.

  Definition shift_state (x : mm2_state) : mm2_state :=
    match x with
    | (p, (a, b)) => ((if p is 0 then 0 else p+a0+b0), (a, b))
    end.

  Definition M' := repeat mm2_inc_a a0 ++ repeat mm2_inc_b b0 ++ map shift_instr M.

  Local Notation mm2'_reaches x y := (clos_refl_trans mm2_state (mm2_step M') x y).

  Lemma length_M' : length M' = a0+b0+length M.
  Proof.
    by rewrite /M' !length_app !repeat_length length_map Nat.add_assoc.
  Qed.

  Lemma init_a0 n : n <= a0 -> mm2'_reaches (1, (0, 0)) (1+n, (n, 0)).
  Proof.
    elim: n. { move=> _. by apply: rt_refl. }
    move=> n IH ?. apply: rt_trans; [|apply: rt_step].
    - apply: IH. lia.
    - exists mm2_inc_a. split; [|constructor].
      rewrite /M'. apply /nth_error_Some_mm2_instr_at_iff.
      rewrite nth_error_app1. { by rewrite repeat_length. }
      by apply: nth_error_repeat.
  Qed.

  Lemma init_b0 n : n <= b0 -> mm2'_reaches (1+a0, (a0, 0)) (1+a0+n, (a0, n)).
  Proof.
    elim: n. { move=> _. rewrite Nat.add_0_r. by apply: rt_refl. }
    move=> n IH ?. apply: rt_trans; [|apply: rt_step].
    - apply: IH. lia.
    - exists mm2_inc_b. have ->: 1 + a0 + S n = S (1 + a0 + n) by lia.
      split; [|constructor].
      rewrite /M' /=. apply /nth_error_Some_mm2_instr_at_iff.
      rewrite nth_error_app2 repeat_length. { lia. }
      rewrite nth_error_app1. { rewrite repeat_length. lia. }
      apply: nth_error_repeat. lia.
  Qed.

  Lemma init_a0b0 : mm2'_reaches (1, (0, 0)) (1+a0+b0, (a0, b0)).
  Proof.
    by apply: rt_trans; [apply: (init_a0 a0)|apply: (init_b0 b0)].
  Qed.

  Lemma instr_at' mm2i p : mm2_instr_at mm2i p M -> mm2_instr_at (shift_instr mm2i) (p+a0+b0) M'.
  Proof.
    move=> /[dup] /mm2_instr_at_pos -> /nth_error_Some_mm2_instr_at_iff Hp /=.
    apply /nth_error_Some_mm2_instr_at_iff.
    rewrite /M'.
    rewrite nth_error_app2 repeat_length. { lia. }
    rewrite nth_error_app2 repeat_length. { lia. }
    have -> : Nat.pred p + a0 + b0 - a0 - b0 = Nat.pred p by lia.
    by rewrite nth_error_map Hp.
  Qed.

  Lemma mm2_step_sim x y :
    mm2_step M x y ->
    mm2_step M' (shift_state x) (shift_state y).
  Proof.
    move=> > [] instr [Hinstr Hxy].
    case: Hxy Hinstr.
    all: move=> > /= /[dup] /mm2_instr_at_pos -> /instr_at' H'instr; 
      (eexists; by split; [eassumption|constructor]).
  Qed.

  Definition sync x x' := shift_state x = x'.

  Lemma mm2_step_sim' x y x' :
    mm2_step M x y -> sync x x' -> exists y', clos_trans _ (mm2_step M') x' y' /\ sync y y'.
  Proof.
    move=> /mm2_step_sim Hxy. rewrite /sync => <-.
    exists (shift_state y). by split; [apply: t_step|].
  Qed.

  Lemma mm2_stuck_sim' x x' :
    sim.stuck (mm2_step M) x -> sync x x' -> sim.terminates (mm2_step M') x'.
  Proof.
    rewrite /sync => /mm2_stop_index_iff Hx <-. exists (shift_state x).
    split; [apply: rt_refl|].
    apply /mm2_stop_index_iff.
    rewrite length_M'.
    move: x Hx => [[|p] [a b]] /=; lia.
  Qed.

  Lemma transport : MM2_HALTING (M, a0, b0) -> MM2_ZERO_HALTING M'.
  Proof.
    have Hsim := sim.terminates_transport mm2_step_sim' mm2_stuck_sim'.
    move=> /Hsim => /(_ _ erefl) [y [Hxy Hy]].
    exists y. split; [|done].
    by apply: rt_trans; [apply: init_a0b0|apply: Hxy].
  Qed.

  Lemma reflection : MM2_ZERO_HALTING M' -> MM2_HALTING (M, a0, b0).
  Proof.
    move=> [y'] [Hxy' Hy']. have Hinit := init_a0b0.
    have Hx'y' : mm2'_reaches (shift_state (1, (a0, b0))) y'.
    { have [z [/mm2_steps_stop_refl Hyz Hinitz]] := mm2_steps_confluent Hxy' Hinit.
      by rewrite -(Hyz Hy'). }
    have Hsim := sim.terminates_reflection (@mm2_step_det M') mm2_step_sim' (mm2_exists_step_dec M).
    apply: (Hsim _ _ erefl).
    by exists y'.
  Qed.

End MM2_MM2.
End Argument.

Require Import Undecidability.Synthetic.Definitions.

(* halting of Minsky machines with two counters
   many-one reduces to
   halting of Minsky machines with two counters starting from (0, 0) *)
Theorem reduction : MM2_HALTING ⪯ MM2_ZERO_HALTING.
Proof.
  exists (fun '(P, a0, b0) => Argument.M' P a0 b0).
  intros [[P a0] b0]. constructor.
  - apply Argument.transport.
  - apply Argument.reflection.
Qed.
