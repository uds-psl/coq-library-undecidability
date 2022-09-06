Require Import List PeanoNat Lia.
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
  move /(iffRL (Nat.succ_lt_mono _ _)) /IH => [? ?]. eexists. f_equal.
  by eassumption.
Qed.

Lemma mm2_instr_at_bounds {P: list mm2_instr} {mmi: mm2_instr} {i: nat} : 
  mm2_instr_at mmi i P -> 0 < i /\ i <= length P.
Proof. move=> [l] [r] [-> <-]. rewrite app_length /=. by lia. Qed.

Lemma mm2_instr_at_unique {P: list mm2_instr} {i op op'} : mm2_instr_at op i P -> mm2_instr_at op' i P -> op = op'.
Proof.
  move=> [l] [r] [+ +] [l'] [r'] => -> <- [+ ?] => /(f_equal (skipn (length l))).
  have Hll': length l = length l' by lia. 
  by rewrite ?skipn_app ?[in RHS] Hll' ?Nat.sub_diag ?skipn_all => [[]].
Qed.
