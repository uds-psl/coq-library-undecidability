Require Import List Arith Lia.
Import ListNotations.

Require Import Undecidability.MinskyMachines.MM2.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

Definition mm2_config : Set := (nat*(nat*nat)).

Lemma mm2_progress {mmi: mm2_instr} {x: mm2_config} : 
  exists y, mm2_atom mmi x y.
Proof. move: x mmi => [i [[|a] [|b]]] [||j|j]; eexists; by constructor. Qed.

Lemma mm2_mmi_lookup {P: list mm2_instr} {i: nat} : i < length P ->
  exists (mmi : mm2_instr), P = firstn i P ++ mmi :: skipn (1+i) P.
Proof.
  elim: i P.
  { move=> [|mmi' P'] /=; first by lia.
    move=> _. by eexists. }
  move=> i IH [|mmi' P'] /=; first by lia.
  move /Lt.lt_S_n /IH => [? ?]. eexists. f_equal.
  by eassumption.
Qed.

Lemma mm2_instr_at_bounds {P: list mm2_instr} {mmi: mm2_instr} {i: nat} : 
  mm2_instr_at mmi i P -> 0 < i /\ i <= length P.
Proof. move=> [l] [r] [-> <-]. rewrite app_length /=. by lia. Qed.

Lemma mm2_step_or_halt (P: list mm2_instr) (x: mm2_config) : 
  (exists y, mm2_step P x y) \/ (mm2_stop P x).
Proof.
  move: x => [i [a b]].
  have [? | [? ?]] : ((i = 0 \/ i > length P) \/ (1 <= i /\ i <= length P)) by lia.
  { right. move=> y [? [/mm2_instr_at_bounds]] /=. by lia. }
  have [mmi ?] := mm2_mmi_lookup (i := i-1) (P := P) ltac:(lia).
  have [y Hy] := mm2_progress (mmi := mmi) (x := (i, (a, b))).
  left. exists y, mmi. constructor; last done.
  eexists. eexists. constructor; first by eassumption.
  rewrite firstn_length_le /=; by lia.
Qed.

Lemma mm2_step_neq {P: list mm2_instr} {x y: mm2_config} : 
  mm2_step P x y -> x <> y.
Proof. by move=> [[||j|j]] [_ +]; (case=> * []; lia). Qed.

Lemma mm2_instr_at_unique {P: list mm2_instr} {i op op'} : mm2_instr_at op i P -> mm2_instr_at op' i P -> op = op'.
Proof.
  move=> [l] [r] [+ +] [l'] [r'] => -> <- [+ ?] => /(f_equal (skipn (length l))).
  have Hll': length l = length l' by lia. 
  by rewrite ?skipn_app ?[in RHS] Hll' ?Nat.sub_diag ?skipn_all => [[]].
Qed.
