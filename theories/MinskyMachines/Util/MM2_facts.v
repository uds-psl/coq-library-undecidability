Require Import List PeanoNat Lia
  Relation_Operators Operators_Properties Wellfounded.Transitive_Closure.
Import ListNotations.
Require Import Undecidability.MinskyMachines.MM2.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

Import MM2Notations.

#[local] Arguments Acc_clos_trans {A R x}.

Lemma mm2_state_eq_dec (x y: mm2_state) : {x = y} + {x <> y}.
Proof. do ? decide equality. Qed. 

Lemma mm2_state_eta (x : mm2_state) : x = (index x, (value1 x, value2 x)).
Proof. by move: x => [? [? ?]]. Qed.

Lemma mm2_progress (mmi: mm2_instr) (x: mm2_state) : 
  { y | mm2_atom mmi x y }.
Proof. move: x mmi => [i [[|a] [|b]]] [||j|j]; eexists; by constructor. Qed.

Lemma mm2_mmi_lookup {P: list mm2_instr} {i: nat} : i < length P ->
  exists (mmi : mm2_instr), P = firstn i P ++ mmi :: skipn (1+i) P.
Proof.
  elim: i P.
  { move=> [|mmi' P'] /=; first by lia.
    move=> _. by eexists. }
  move=> i IH [|mmi' P'] /=; first by lia.
  move=> /(iffRL (Nat.succ_lt_mono _ _)) /IH => - [? ?].
  eexists. congr cons. by eassumption.
Qed.

Lemma mm2_instr_at_bounds {P: list mm2_instr} {mmi: mm2_instr} {i: nat} : 
  mm2_instr_at mmi i P -> 0 < i /\ i <= length P.
Proof. move=> [l] [r] [-> <-]. rewrite length_app /=. by lia. Qed.

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

Lemma mm2_stop_index_iff {P: list mm2_instr} {x} : mm2_stop P x <-> fst x = 0 \/ length P < fst x.
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

Lemma mm2_terminates_Acc {P x y} :
  clos_refl_trans _ (mm2_step P) x y ->
  mm2_stop P y ->
  Acc (fun y' x' => mm2_step P x' y') x.
Proof.
  move=> /clos_rt_rt1n_iff. elim.
  { move=> {}x Hx. by constructor => ? /Hx. }
  move=> {}x {}y z /mm2_step_det Hxy Hyz IH Hz. constructor.
  move=> y' /Hxy <-. by apply: IH.
Qed.

Lemma mm2_sig_step_dec P x :
  { y | mm2_step P x y } + { forall y, not (mm2_step P x y) }.
Proof.
  move: x => [[|i] [a b]].
  { right => y [?] /= [] [?] [?]. lia. }
  case Hinstr: (nth_error P i) => [instr|].
  + left. have [y Hxy] := mm2_progress instr (S i, (a, b)).
    exists y. exists instr.
    by split; [apply /nth_error_Some_mm2_instr_at_iff|].
  + right => y [?] /= [/nth_error_Some_mm2_instr_at_iff].
    by rewrite Hinstr.
Qed.

Lemma mm2_exists_step_dec P x :
  (exists y, mm2_step P x y) \/ (forall y, not (mm2_step P x y)).
Proof.
  have [[y Hy]|Hx] := mm2_sig_step_dec P x.
  - left. by exists y.
  - by right.
Qed.

Lemma mm2_steps_confluent {P x y1 y2} :
  P // x ↠ y1 -> P // x ↠ y2 ->
  exists z, P // y1 ↠ z /\ P // y2 ↠ z.
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

Lemma mm2_steps_stop_refl {P x y} :
  P // x ↠ y -> mm2_stop P x -> y = x.
Proof.
  move=> /clos_rt_rt1n_iff []; [done|].
  by move=> > + _ H => /H.
Qed.

Lemma mm2_step_values_bound {P x y} : mm2_step P x y ->
  value1 y + value2 y <= 1 + value1 x + value2 x /\
  value1 x + value2 x <= 1 + value1 y + value2 y /\
  value1 x <= 1 + value1 y /\ value1 y <= 1 + value1 x /\
  value2 x <= 1 + value2 y /\ value2 y <= 1 + value2 x.
Proof.
  move=> [i] [_ []] /=; lia.
Qed.

Lemma mm2_step_intro {P i p} :
  mm2_instr_at i p P ->
  forall a b, mm2_step P (p, (a, b))
    match i with
    | mm2_inc_a => (S p, (S a, b))
    | mm2_inc_b => (S p, (a, S b))
    | mm2_dec_a q => if a is S a' then (q, (a', b)) else (S p, (0, b))
    | mm2_dec_b q => if b is S b' then (q, (a, b')) else (S p, (a, 0))
    end.
Proof.
  case: i => > ?.
  - move=> >. eexists. by split; [eassumption|constructor].
  - move=> >. eexists. by split; [eassumption|constructor].
  - move=> [|a] b; eexists; by split; [eassumption|constructor].
  - move=> a [|b]; eexists; by split; [eassumption|constructor].
Qed.

(* step with counters of same positivity *)
Lemma mm2_step_parallel {P x y} x' :
  mm2_step P x y ->
  (index x = index x' /\ (value1 x > 0 <-> value1 x' > 0) /\ (value2 x > 0 <-> value2 x' > 0)) ->
  exists y', mm2_step P x' y' /\
  index y = index y' /\
  value1 x + value1 y' = value1 x' + value1 y /\
  value2 x + value2 y' = value2 x' + value2 y.
Proof.
  move=> [?] [+ Hxy]. move: x' => [i' [a' b']].
  case: Hxy => [i a b|i a b|i j a b|i j a b|i j b|i j a] /= Hi [<- ?].
  - eexists. split; [eexists; split; [eassumption|constructor]|cbn; lia].
  - eexists. split; [eexists; split; [eassumption|constructor]|cbn; lia].
  - have ->: a' = S (Nat.pred a') by lia.
    eexists. split; [eexists; split; [eassumption|constructor]|cbn; lia].
  - have ->: b' = S (Nat.pred b') by lia.
    eexists. split; [eexists; split; [eassumption|constructor]|cbn; lia].
  - have ->: a' = 0 by lia.
    eexists. split; [eexists; split; [eassumption|constructor]|cbn; lia].
  - have ->: b' = 0 by lia.
    eexists. split; [eexists; split; [eassumption|constructor]|cbn; lia].
Qed.

Lemma mm2_stop_index_eq {P x y} : mm2_stop P x -> index x = index y -> mm2_stop P y.
Proof.
  move=> Hx Hxy z Hyz.
  move: Hyz => [i]. rewrite -Hxy => - [Hi _].
  have [z' Hxz'] := mm2_progress i x.
  apply: Hx. eexists. by split; eassumption.
Qed.

Lemma mm2_steps_terminates_l {P x y} : P // x ↠ y -> P // y ↓ -> P // x ↓.
Proof.
  move=> Hxy [z] [Hyz Hz]. exists z. split; [|done].
  by apply: rt_trans; eassumption.
Qed.

Lemma mm2_stop_terminates {P x} : mm2_stop P x -> P // x ↓.
Proof.
  move=> ?. exists x. by split; [apply: rt_refl|].
Qed.

Lemma mm2_steps_terminates_r {P x y} : P // x ↠ y -> P // x ↓ -> P // y ↓.
Proof.
  move=> Hxy [z] [Hxz Hz].
  have [z' [Hyz' Hzz']] := mm2_steps_confluent Hxy Hxz.
  apply: (mm2_steps_terminates_l Hyz').
  move: Hzz' (Hz) => /mm2_steps_stop_refl /[apply] ->.
  by apply: mm2_stop_terminates.
Qed.

Lemma mm2_steps_not_terminates_l {P x y} :  P // x ↠ y -> not (P // y ↓) -> not (P // x ↓).
Proof.
  move=> Hxy Hy Hx. apply: Hy. by apply: mm2_steps_terminates_r; eassumption.
Qed.

Lemma mm2_clos_trans_not_terminates {P} (R : mm2_state -> Prop) :
  (forall x, R x -> exists y, (clos_trans _ (mm2_step P) x y) /\ R y) ->
  forall x, R x -> not (P // x ↓).
Proof.
  move=> H x Hx [?] [/mm2_terminates_Acc] /[apply] /Acc_clos_trans H'x.
  elim: H'x Hx => {}x _ IH Hx.
  have [y [Hxy Hy]] := H x Hx.
  apply: (IH y _ Hy). move: Hxy.
  elim; by eauto using clos_trans with nocore.
Qed.

Corollary mm2_loop_not_terminates {P x} : (clos_trans _ (mm2_step P) x x) -> not (P // x ↓).
Proof.
  move=> ?. apply: (mm2_clos_trans_not_terminates (fun y => y = x)); last done.
  move=> y ->. by exists x.
Qed.
