Require Import List PeanoNat Lia Relation_Operators Operators_Properties.
Import ListNotations.

Require Import Undecidability.MinskyMachines.MM2.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

#[local] Notation mm2_steps P x y := (clos_refl_trans _ (mm2_step P) x y).

(* TODO Notation *)
Definition mm2_config : Set := (nat*(nat*nat))%type.

Lemma mm2_progress (mmi: mm2_instr) (x: mm2_config) : 
  { y | mm2_atom mmi x y }.
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

Lemma mm2_instr_at_pos {P: list mm2_instr} {mmi: mm2_instr} {i: nat} : mm2_instr_at mmi i P -> i = S (Nat.pred i).
Proof. by move=> [?] [?] [_ <-] /=. Qed.

Lemma nth_error_Some_mm2_instr_at_iff {P: list mm2_instr} i instr :
  nth_error P i = Some instr <-> mm2_instr_at instr (S i) P.
Proof.
  split.
  - move=> /(@nth_error_split mm2_instr) [?] [?] [-> <-].
    by do 2 eexists.
  - move=> [?] [?] [-> [<-]].
    by rewrite nth_error_app2 ?Nat.sub_diag.
Qed.

Lemma mm2_instr_at_unique {P: list mm2_instr} {i op op'} : mm2_instr_at op i P -> mm2_instr_at op' i P -> op = op'.
Proof.
  move=> /[dup] /mm2_instr_at_pos ->.
  move=> /nth_error_Some_mm2_instr_at_iff + /nth_error_Some_mm2_instr_at_iff.
  by move=> -> [].
Qed.

Lemma mm2_stuck_index {P: list mm2_instr} {x} : (forall y, not (mm2_step P x y)) <-> fst x = 0 \/ length P < fst x.
Proof.
  split.
  - move: x => [[|i] [a b]] /=; [lia|].
    move=> H. suff: not (i < length P) by lia.
    move=> /nth_error_Some.
    move Hinstr: (nth_error P i) => [instr|]; [|done].
    move=> /nth_error_Some_mm2_instr_at_iff in Hinstr.
    have [y Hy] := @mm2_progress instr (S i, (a, b)).
    move=> _. apply: (H y).
    by exists instr.
  - move=> Hx y Hxy. case: Hxy Hx.
    move=> ? [/mm2_instr_at_bounds]. lia.
Qed.

Lemma mm2_atom_det {mm2i x y z} :
  mm2_atom mm2i x y -> mm2_atom mm2i x z -> y = z.
Proof.
  move=> [] > H; inversion H; by subst.
Qed.

Lemma mm2_step_det {P x y z} :
  mm2_step P x y -> mm2_step P x z -> y = z.
Proof.
  by move=> [?] [/mm2_instr_at_unique H /mm2_atom_det H'] [?] [/H <- /H'].
Qed.

Lemma mm2_sn {P x y} :
  clos_refl_trans _ (mm2_step P) x y ->
  mm2_stop P y ->
  Acc (fun y' x' => mm2_step P x' y') x.
Proof.
  move=> /clos_rt_rt1n_iff. elim.
  { move=> {}x Hx. by constructor => ? /Hx. }
  move=> {}x {}y z /mm2_step_det Hxy Hyz IH Hz. constructor.
  move=> y' /Hxy <-. by apply: IH.
Qed.

(* use mm2_progress ? *)
Lemma mm2_sig_step_dec P x :
  { y | mm2_step P x y } + { forall y, not (mm2_step P x y) }.
Proof.
  move: x => [[|i] [a b]].
  { right => y [?] /= [] [?] [?]. lia. }
  case Hinstr: (nth_error P i) => [instr|].
  + left.
    have [y Hxy] := mm2_progress instr (S i, (a, b)).
    exists y. exists instr.
    split; [|done].
    have [? [? [-> <-]]] := nth_error_split _ _ Hinstr.
    by do 2 eexists.
  + right => y.
    move=> [?] /= [] [?] [?] [HP ?] _.
    move: Hinstr => /nth_error_None.
    rewrite HP app_length /=. lia.
Qed.

Lemma mm2_exists_step_dec P x :
  (exists y, mm2_step P x y) \/ (forall y, not (mm2_step P x y)).
Proof.
  have [[y Hy]|Hx] := mm2_sig_step_dec P x.
  - left. by exists y.
  - by right.
Qed.

Lemma mm2_steps_confluent {P x y1 y2} :
  mm2_steps P x y1 -> mm2_steps P x y2 ->
  exists z, mm2_steps P y1 z /\ mm2_steps P y2 z.
Proof.
  move=> /clos_rt_rt1n_iff H. elim: H y2.
  - move=> *. eexists. by split; [|apply rt_refl].
  - move=> ? {}y1 z1 Hx /clos_rt_rt1n_iff Hyz IH ? /clos_rt_rt1n_iff Hxy2.
    case: Hxy2 Hx IH.
    + move=> ? _. eexists. split; [apply: rt_refl|].
      apply: rt_trans; [apply: rt_step|]; by eassumption.
    + move=> y2 z2 /mm2_step_det Hx /clos_rt_rt1n_iff Hy2z2 /Hx {Hx} ? IH.
      subst y2. move: Hy2z2 => /IH [z [??]].
      by exists z.
Qed.

Lemma mm2_stop_steps_refl {P x y} :
  mm2_steps P x y -> mm2_stop P x -> y = x.
Proof.
  move=> /clos_rt_rt1n_iff []; [done|].
  by move=> > + _ H => /H.
Qed.
