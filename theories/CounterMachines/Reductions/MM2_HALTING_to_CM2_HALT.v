(* 
  Author(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Reduction(s):
    Halting of Minsky machines with two counters (MM2_HALTING) to
    Halting of two counter machines (CM2_HALT)
*)

Require Import List Lia Relations.Relation_Operators Relations.Operators_Properties.
Import ListNotations.

Require Import Undecidability.MinskyMachines.MM2.
Require Undecidability.CounterMachines.CM2.

From Undecidability.CounterMachines.Util Require Import 
  Facts Nat_facts MM2_facts CM2_facts.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

Module Argument.
Section MM2_CM2.
  Variable (P: list mm2_instr). (* MM2 program *)
  Variables (a0 b0: nat). (* MM2 initial counters *)

  Definition mm2_config : Set := (nat*(nat*nat)).

  (* instruction index map *)
  Definition fs (i: nat) : nat :=
    if i is S i then i + a0 + b0 else (length P) + a0 + b0.

  (* encode instruction mmi at position i using index map fs for current cm2 state p *)
  Definition encode_instruction (mmi: mm2_instr) : CM2.Instruction :=
    match mmi with
    | mm2_inc_a => CM2.inc false
    | mm2_inc_b => CM2.inc true
    | mm2_dec_a j => CM2.dec false (fs j)
    | mm2_dec_b j => CM2.dec true (fs j)
    end.

  (* two counter machine encoding P in start cofiguration (0, (0, 0)) *)
  Definition M : list CM2.Instruction :=
    (repeat (CM2.inc false) a0) ++ (repeat (CM2.inc true) b0) ++ map encode_instruction P.

  (* encode mm2 config as cm2 config *)
  Definition encode_config (x: mm2_config) : CM2.Config :=
    let: (i, (a, b)) := x in (fs i, (a, b)).

  Lemma fs_pos i : 0 < i -> fs i = ((i - 1) + a0 + b0).
  Proof. case: i => [|?] /=; lia. Qed.

  Lemma seek_M {i M'} : nth_error (repeat (CM2.inc false) a0 ++ repeat (CM2.inc true) b0 ++ M') (i + a0 + b0) = nth_error M' i.
  Proof.
    rewrite nth_error_app2; [rewrite ?repeat_length; by lia |].
    rewrite nth_error_app2; [rewrite ?repeat_length; by lia |].
    congr @nth_error. rewrite ?repeat_length. by lia.
  Qed.

  Lemma init_M_a0 (n: nat) : n <= a0 -> CM2.steps M n (0, (0, 0)) = 
    Some (n, (n, 0)).
  Proof.
    elim: n; first done.
    move=> n + /= ? => ->; first by lia.
    rewrite /M /CM2.step /= nth_error_app1 ?repeat_length; first by lia.
    rewrite (nth_error_nth' _  (CM2.inc false)) ?repeat_length ?nth_repeat /=; [by lia | done].
  Qed.

  Lemma init_M_b0 (n: nat) : n <= b0 -> CM2.steps M n (a0, (a0, 0)) = 
    Some (n + a0, (a0, n)).
  Proof.
    elim: n; first done.
    move=> n + /= ? => ->; first by lia.
    rewrite /M /CM2.step /= nth_error_app2 ?repeat_length; first by lia.
    rewrite nth_error_app1 ?repeat_length; first by lia.
    rewrite (nth_error_nth' _  (CM2.inc true)) ?repeat_length ?nth_repeat; [by lia | done].
  Qed.

  (* after a0 + b0 steps the counters of M are initialized to a0, b0 *)
  Lemma init_M : CM2.steps M (a0 + b0) (0, (0, 0)) = 
    Some (a0 + b0, (a0, b0)).
  Proof.
    have /steps_plus -> := init_M_a0 a0 ltac:(lia).
    have ->: a0 + b0 = b0 + a0 by lia.
    apply: init_M_b0. lia.
  Qed.

  Lemma length_M : length M = a0 + b0 + length P.
  Proof.
    rewrite /M ?app_length ?repeat_length ?map_length. by lia.
  Qed.

  (* relation between M indices and P indices *)
  Inductive program_index : nat -> Prop :=
  | seek_M_None {i} : nth_error M (fs i) = None -> (forall op, not (mm2_instr_at op i P)) -> program_index i
  | seek_M_Some {i op} : nth_error M (fs (1+i)) = Some (encode_instruction op) -> 
      mm2_instr_at op (1+i) P -> program_index (1+i).

  Lemma program_index_spec (i: nat) : program_index i.
  Proof.
    move Ht: (nth_error M (fs i)) => t. case: t Ht.
    - move: i => [|i] op.
      + move=> ?. have /nth_error_Some : nth_error M (fs 0) <> None by congruence.
        rewrite length_M /=. by lia.
      + move=> H. have /nth_error_None : nth_error M (fs (S i)) <> None by congruence.
        rewrite length_M /= => ?. have /mm2_mmi_lookup [op' HP] : i < length P by lia.
        move=> [:Hop']. apply: (@seek_M_Some i op'); last (abstract: Hop').
        * rewrite /M HP seek_M nth_error_map nth_error_app2 ?firstn_length; first by lia.
          by have ->: i - Nat.min i (length P) = 0 by lia.
        * do 2 eexists. constructor; [by eassumption | rewrite firstn_length; by lia].
    - rewrite /M. move=> Hi. apply: seek_M_None; first done.
      move=> op [l] [r] [HP ?]. subst i. move: HP Hi => ->.
      by rewrite seek_M nth_error_map nth_error_app2 ?PeanoNat.Nat.sub_diag.
  Qed.

  (* M simulates each step of P *)
  Lemma P_to_M_step {x y: mm2_config}  : 
    mm2_step P x y -> CM2.step M (encode_config x) = Some (encode_config y).
  Proof.
    case. move: x => [i [a b]] op.
    move: (program_index_spec i) => [? ? H [/H] | ]; first done.
    rewrite /CM2.step.
    move=> {}i op' /= -> Hop' [/(mm2_instr_at_unique Hop') <- H]. by inversion H.
  Qed.

  (* M simulates P *)
  Lemma P_to_M (x y: mm2_config) : 
    clos_refl_trans _ (mm2_step P) x y -> 
    exists n, CM2.steps M n (encode_config x) = Some (encode_config y).
  Proof.
    move /clos_rt_rtn1_iff. elim; first by (exists 0).
    move=> {}y z /P_to_M_step Hyz _ [n Hnxy].
    exists (1+n) => /=. by rewrite Hnxy.
  Qed.

  Lemma M_to_P_step (x: mm2_config) (y: CM2.Config) :
    CM2.step M (encode_config x) = Some y ->
    exists z, y = encode_config z /\ mm2_step P x z.
  Proof.
    move: x y => [i [a b]] [i' [a' b']]. rewrite /CM2.step.
    move: (program_index_spec i) => [{}i | {}i op] -> HiP /=; first done.
    move=> H.
    suff: exists z : mm2_config,
      (i', (a', b')) = encode_config z /\ mm2_atom op (S i, (a, b)) z.
    { move=> [z [? ?]]. exists z. split; first done. by exists op. }
    move: HiP => /mm2_instr_at_bounds ?.
    move: op H => [||j|j] /=.
    - move=> [???]. exists (S (S i), (S a, b)). split.
      + rewrite /=. congr (_, (_, _)); lia.
      + by apply: in_mm2s_inc_a.
    - move=> [???]. exists (S (S i), (a, S b)). split.
      + rewrite /=. congr (_, (_, _)); lia.
      + by apply: in_mm2s_inc_b.
    - move: a => [|a] [???].
      + exists (S (S i), (0, b)). split.
        * rewrite /=. congr (_, (_, _)); lia.
        * by apply: in_mm2s_dec_a0.
      + exists (j, (a, b)). split.
        * rewrite /=. congr (_, (_, _)); lia.
        * by apply: in_mm2s_dec_aS.
    - move: b => [|b] [???].
      + exists (S (S i), (a, 0)). split.
        * rewrite /=. congr (_, (_, _)); lia.
        * by apply: in_mm2s_dec_b0.
      + exists (j, (a, b)). split.
        * rewrite /=. congr (_, (_, _)); lia.
        * by apply: in_mm2s_dec_bS.
  Qed.

  Lemma M_to_P (n: nat) (x: mm2_config) (y: CM2.Config) :
    CM2.steps M n (encode_config x) = Some y ->
    exists z, y = encode_config z /\ clos_refl_trans _ (mm2_step P) x z.
  Proof.
    elim: n x y.
    { move=> x y [] <-. exists x. split; [done|by apply: rt_refl]. }
    move=> n IH x y /=. rewrite obind_oiter.
    case Hx': (CM2.step M (encode_config x)) =>[x'|]; last by rewrite oiter_None.
    move: Hx' => /M_to_P_step [y'] [->] Hxy'.
    move=> /IH [z] [?] ?. exists z. split; first done.
    apply: rt_trans; [apply rt_step|]; by eassumption.
  Qed.

   (* P stops iff M halts *)
  Lemma P_stop_iff_M_halting (x: mm2_config) :
    mm2_stop P x <-> CM2.step M (encode_config x) = None.
  Proof.
    move: x => [i [a b]]. rewrite /CM2.step /=. constructor.
    - move: (program_index_spec i) => [{}i | {}i op] ->; first done.
      have [y Hy] := @mm2_progress op (1 + i, (a, b)).
      move=> ? /(_ y) + /ltac:(exfalso). apply. by exists op.
    - move: (program_index_spec i) => [{}i | {}i op] ->.
      + move=> + _ y [] op [? ?] => /(_ op). by apply.
      + by move: op a b => [||j|j] [|a] [|b] _.
  Qed.

  Lemma transport : MM2_HALTING (P, a0, b0) -> CM2.CM2_HALT M.
  Proof.
    move=> [z] [/P_to_M] [n /= Hn] /P_stop_iff_M_halting Hz.
    exists ((a0 + b0) + (n + 1)).
    by rewrite (steps_plus init_M) (steps_plus Hn).
  Qed.

  Lemma reflection: CM2.CM2_HALT M -> MM2_HALTING (P, a0, b0).
  Proof.
    move=> [n] /(steps_k_monotone ((a0 + b0) + n)) => /(_ ltac:(lia)).
    rewrite (steps_plus init_M) -/(encode_config (1, (a0, b0))).
    elim: n; first done.
    move=> n /=.
    case Hy: (CM2.steps M n (a0 + b0, (a0, b0))) => [y|]; first last.
    { move=> IH _. by apply: IH. }
    move: Hy. rewrite -/(encode_config (1, (a0, b0))).
    move=> /M_to_P [z] [->] Hz _ /P_stop_iff_M_halting ?.
    by exists z.
  Qed.

End MM2_CM2.
End Argument.

Require Import Undecidability.Synthetic.Definitions.

(* halting of Minsky machines with two counters 
  many-one reduces to halting of two counter machines *)
Theorem reduction : MM2_HALTING ⪯ CM2.CM2_HALT.
Proof.
  exists (fun '(P, a0, b0) => Argument.M P a0 b0).
  move => [[P a0] b0]. constructor.
  - exact (Argument.transport P a0 b0).
  - exact (Argument.reflection P a0 b0).
Qed.
