From Undecidability.MuRec Require Import MuRec Util.ra_mm.
From Undecidability.MinskyMachines Require Import MM Util.MM_sss
  Util.MMA_facts MM.mm_defs
  Util.MM_computable.
Require Import Undecidability.Shared.Libs.DLW.Code.sss
  Undecidability.Shared.Libs.DLW.Vec.vec.
Require Import Undecidability.Shared.simulation.

From Stdlib Require Import List Lia Relations PeanoNat ssreflect.
Import ListNotations.

Set Default Goal Selector "!".

#[local] Arguments Vector.nil {_}.
#[local] Arguments Vector.cons {_} _ {_} _.

(* general facts *)

Lemma sss_compute_sss_output {n M st st'} : S (length M) = fst st' ->
  sss_compute (@mm_sss n) (1, M) st st' -> sss_output (@mm_sss n) (1, M) st st'.
Proof.
  move=> ??. split; [done|right]. simpl. lia.
Qed.

Lemma sss_output_sss_terminates {n M st st'} : sss_output (@mm_sss n) (1, M) st st' ->
  sss_terminates (@mm_sss n) (1, M) st.
Proof.
  move=> ?. eexists. by eassumption.
Qed.

Lemma vec_app_spec {X n m} (v : Vector.t X n) (w : Vector.t X m) :
  vec_app v w = Vector.append v w.
Proof.
  induction v.
  - cbn. eapply vec_pos_ext. intros. now rewrite vec_pos_set.
  - rewrite vec_app_cons. cbn. congruence.
Qed.

Lemma vec_set_const {X : Type} {n} {x : X} :
  vec_set_pos (fun _ => x) = Vector.const x n.
Proof.
  elim: n; first done.
  by move=> ? /= ->.
Qed.

Lemma vec_intro {n} (P : nat -> nat -> Prop) : (forall i, i < n -> exists m, P i m) ->
  exists v, forall (x : Fin.t n), P (pos.pos2nat x) (vec_pos v x).
Proof.
  elim: n P.
  - move=> P _. exists Vector.nil. by apply: Fin.case0.
  - move=> n IH P H.
    have /IH : forall i : nat, i < n -> exists m : nat, P (S i) m.
    { move=> i ?. apply: H. lia. }
    move=> [v Hv].
    have /H [m Hm] : 0 < S n by lia.
    exists (Vector.cons m v).
    move=> x. pattern x. apply: Fin.caseS'.
    + by apply: Hm.
    + move=> ?. by apply: Hv.
Qed.

Section MuRec_MM.

Context {k : nat} (f : recalg k).
Definition k' := (projT1 (ra_mm_compiler f)).

Definition M := proj1_sig (projT2 (ra_mm_compiler f)).
Definition HM := proj2_sig (projT2 (ra_mm_compiler f)).

Definition shift_reg (x : Fin.t (k + S k')) : Fin.t (1 + k + (S k' + 1)).
Proof.
  refine (match pos.pos_both _ _ x with inl y => _ | inr y => _ end).
  - exact (Fin.FS (pos.pos_left (S k' + 1) y)).
  - exact (Fin.FS (pos.pos_right k (pos.pos_left 1 y))).
Defined.

Definition shift_instr (instr : mm_instr (Fin.t (k + S k'))) : mm_instr (Fin.t (1 + k + (S k' + 1))) :=
  match instr with
  | INC x => INC (shift_reg x)
  | DEC x j => DEC (shift_reg x) j
  end.

Definition r0 : Fin.t (1 + k + (S k' + 1)) := pos.pos_left (S k' + 1) Fin.F1.
Definition r1 : Fin.t (1 + k + (S k' + 1)) := pos.pos_right (1 + k) (pos.pos_left 1 Fin.F1).
Definition rx : Fin.t (1 + k + (S k' + 1)) := pos.pos_right (1 + k) (pos.pos_right (S k') Fin.F1).

Definition M' : list (mm_instr (Fin.t (1 + k + (S k' + 1)))) :=
  map shift_instr M ++ [DEC r1 (4 + length M); INC r0; DEC rx (S (length M))].

Lemma length_M' : length M' = 3 + (length M).
Proof. by rewrite /M' length_app length_map Nat.add_comm. Qed.

Definition shift_regs (v : Vector.t nat (k + S k')) : Vector.t nat (1 + k + (S k' + 1)) :=
  vec_app (Vector.cons 0 (fst (vec_split k _ v))) (vec_app (snd (vec_split k _ v)) (Vector.cons 0 Vector.nil)).

#[local] Opaque vec_split vec_app.

Lemma vec_change_shift v x n : vec_change (shift_regs v) (shift_reg x) n = shift_regs (vec_change v x n).
Proof.
  rewrite /shift_regs /shift_reg.
  rewrite [in RHS](eq_sym (pos.pos_lr_both _ _ x)).
  case: (pos.pos_both k (S k') x)=> {}x.
  - rewrite vec_app_cons /= vec_app_cons vec_change_app_left.
    have <- := vec_app_split _ _ v.
    by rewrite !vec_change_app_left !vec_split_app.
  - rewrite vec_app_cons /= vec_app_cons vec_change_app_right.
    have <- := vec_app_split _ _ v.
    by rewrite !vec_change_app_right !vec_split_app (vec_change_app_left _ _ x).
Qed.

Lemma vec_pos_shift v x : vec_pos (shift_regs v) (shift_reg x) = vec_pos v x.
Proof.
  rewrite /shift_regs /shift_reg.
  rewrite [in RHS](eq_sym (pos.pos_lr_both _ _ x)).
  case: (pos.pos_both k (S k') x)=> {}x.
  - by rewrite vec_app_cons /= vec_pos_app_left vec_pos_set.
  - rewrite vec_app_cons /= vec_pos_app_right (vec_pos_app_left _ _ x).
    pattern x. apply: Fin.caseS'; first done.
    move=> {}x /=. by rewrite vec_pos_set. 
Qed.

Lemma simulation_sss_step st st' : 
  sss_step (@mm_sss _) (1, M) st st' ->
  sss_step (@mm_sss _) (1, M') (fst st, shift_regs (snd st)) (fst st', shift_regs (snd st')).
Proof.
  move=> [c] [l] [instr] [r] [v] [[<- E]] [->] H.
  rewrite /M'. rewrite [in map shift_instr _]E map_app /= -!app_assoc /=.
  eexists _, _, _, _, _.
  split; first done.
  split; first by rewrite length_map.
  move: st' (instr) H=> [??] [].
  - move=> x /mm_sss_INC_inv [-> ->].
    have := in_mm_sss_inc (S (length l)) (shift_reg x) (shift_regs v).
    by rewrite vec_change_shift vec_pos_shift.
  - move=> x j.
    move E': (vec_pos v x) => [|m].
    + move=> /(mm_sss_DEC0_inv E') [-> ->].
      have := in_mm_sss_dec_0 (S (length l)) (shift_reg x) j (shift_regs v).
      rewrite !vec_pos_shift. by apply.
    + move=> /(mm_sss_DEC1_inv E') [-> ->].
      have := @in_mm_sss_dec_1 _ (S (length l)) (shift_reg x) j (shift_regs v) m.
      rewrite vec_change_shift !vec_pos_shift. by apply.
Qed.

Lemma simulation_sss_steps st st' : 
  clos_refl_trans _ (sss_step (@mm_sss _) (1, M)) st st' ->
  clos_refl_trans _ (sss_step (@mm_sss _) (1, M')) (fst st, shift_regs (snd st)) (fst st', shift_regs (snd st')).
Proof.
  elim.
  - move=> > /simulation_sss_step ?. by apply: rt_step.
  - move=> ?. by apply: rt_refl.
  - move=> *. apply: rt_trans; by eassumption.
Qed.

Lemma shift_regs_spec v :
  Vector.append (0 ## v) (Vector.const 0 (S k' + 1)) = shift_regs (vec_app v vec_zero).
Proof.
  rewrite /shift_regs /= -vec_app_spec vec_app_cons /=.
  rewrite vec_split_app /= vec_app_cons.
  congr Vector.cons. congr vec_app. congr Vector.cons.
  rewrite -!vec_set_const.
  apply: vec_pos_ext=> x.
  rewrite vec_pos_set. pattern x.
  apply: pos.pos_left_right_rect=> {}x.
  - by rewrite vec_pos_app_left vec_pos_set.
  - rewrite vec_pos_app_right.
    pattern x. apply: Fin.caseS'; first done.
    by apply Fin.case0.
Qed.

Lemma vec_init v : 
  vec_set_pos
    (fun p : Fin.t (k + S k') =>
      let s := pos.pos_both k (S k') p in
      match s with
      | inl t => vec_pos v t
      | inr t => vec_pos vec_zero t
      end) = vec_app v vec_zero.
Proof.
  apply: vec_pos_ext=> x.
  pattern x.
  apply: pos.pos_left_right_rect=> {}x.
  - by rewrite vec_pos_app_left.
  - by rewrite vec_pos_app_right.
Qed.

Lemma simulation_fin n v m w :
  clos_refl_trans _ (sss_step (@mm_sss _) (1, M'))
    (S (length M), vec_app (Vector.cons n v) (vec_app (Vector.cons m w) (Vector.cons 0 Vector.nil)))
    (4 + length M, vec_app (Vector.cons (n + m) v) (vec_app (Vector.cons 0 w) (Vector.cons 0 Vector.nil))).
Proof.
  elim: m n.
  - move=> n. apply: rt_trans.
    { apply: rt_step. eexists 1, _, (DEC r1 (4 + length M)), _, _.
      split; first done.
      split; first by rewrite length_map.
      apply: in_mm_sss_dec_0.
      by rewrite vec_pos_app_right vec_pos_app_left. }
    rewrite Nat.add_0_r. by apply: rt_refl.
  - move=> m IH n.
    apply: rt_trans.
    { apply: rt_step. eexists 1, _, (DEC r1 (4 + length M)), _, _.
      split; first done.
      split; first by rewrite length_map.
      apply: in_mm_sss_dec_1.
      by rewrite vec_pos_app_right vec_pos_app_left. }
    apply: rt_trans.
    { apply: rt_step. eexists 1, (_ ++ [_]), (INC r0), _, _.
      rewrite -!app_assoc.
      split; first done.
      split; first by rewrite length_app length_map (Nat.add_comm (length M)).
      by apply: in_mm_sss_inc. }
    apply: rt_trans.
    { apply: rt_step. eexists 1, (_ ++ [_; _]), (DEC rx (S (length M))), _, _.
      rewrite -!app_assoc.
      split; first done.
      split; first by rewrite length_app length_map (Nat.add_comm (length M)).
      apply: in_mm_sss_dec_0.
      rewrite vec_change_neq; first done.
      rewrite vec_change_neq; first by move=> /pos.pos_right_inj.
      by rewrite !vec_pos_app_right. }
    rewrite (Nat.add_succ_r n m).
    have := IH (S n). congr clos_refl_trans. congr pair.
    by rewrite vec_change_app_right !vec_change_app_left.
Qed.

#[local] Notation step1 := (sss_step (@mm_sss _) (1, M)).
#[local] Notation step2 := (sss_step (@mm_sss _) (1, M')).

Definition sync (st : nat * _) st' := st' = (fst st, shift_regs (snd st)).

Lemma simulation_sss_step' st st' p : 
  sss_step (@mm_sss _) (1, M) st st' -> sync st p ->
  exists q, clos_trans _ (sss_step (@mm_sss _) (1, M')) p q /\ sync st' q.
Proof.
  move=> /simulation_sss_step ? ->. eexists.
  by split; [apply: t_step|done].
Qed.

Lemma step2_det s' t1' t2' :
  sss_step (@mm_sss _) (1, M') s' t1' ->
  sss_step (@mm_sss _) (1, M') s' t2' -> t1' = t2'.
Proof.
  apply: sss_step_fun. by apply: mm_sss_fun.
Qed.

End MuRec_MM.

Theorem MuRec_computable_to_MM_computable k (R : Vector.t nat k -> nat -> Prop) :
  MuRec_computable R -> MM_computable R.
Proof.
  move=> [f] Hf. exists ((S (k' f) + 1)), (M' f).
  move=> v m. rewrite -/Nat.add. have [H1f H2f] := HM f.
  split.
  - move=> /Hf H'f. exists (S (length (M' f))), (vec_app v (vec_app (0 ## vec_zero) (0 ## vec_nil))).
    apply: sss_output_to_eval. split; last by right.
    apply /sss_compute_iff. rewrite shift_regs_spec.
    apply: rt_trans.
    + apply: (simulation_sss_steps f (_, _)).
      rewrite vec_init.
      apply /sss_compute_iff /H1f /recalg.ra_rel_spec.
      by eassumption.
    + rewrite length_M' /=.
      have := simulation_fin f 0 v m vec_zero.
      by rewrite /shift_regs vec_split_app !vec_app_cons /=.
  - move=> [c] [v'].
    move=> /[dup] /eval_to_sss_compute + /eval_to_sss_out_code.
    rewrite shift_regs_spec /= => H Hc. apply /Hf.
    have : sss_terminates (@mm_sss _) (1, M f) (1, vec_app v vec_zero).
    { apply /(sss_terminates_iff (@mm_sss_total_ni _)).
      apply: (terminates_reflection
        (deterministic_uniformly_confluent _ (step2_det f))
        (simulation_sss_step' f)
        (sss_step_or_stuck (@mm_sss_total_ni _) 1 (M f)) eq_refl).
      apply /(sss_terminates_iff (@mm_sss_total_ni _)).
      eexists. by split; first by eassumption. }
    move=> /H2f [m'] H'.
    suff: m = m'.
    { move=> -> *. apply /recalg.ra_rel_spec. by eassumption. }
    move: H' => /H1f /sss_compute_iff /simulation_sss_steps /= ?.
    have [v''] : exists v'', sss_output (@mm_sss _) (1, M' f)
      (1, shift_regs f (vec_app v vec_zero))
      (4 + length (M f), m' ## v'').
    { eexists. split.
      - apply /sss_compute_iff.
        apply: rt_trans; first by eassumption.
        have := simulation_fin f 0 v m' vec_zero.
        congr clos_refl_trans.
        by rewrite /shift_regs vec_split_app /=.
      - rewrite /= length_M'. by right. }
    have: sss_output (@mm_sss _) (1, M' f)
      (1, shift_regs f (vec_app v vec_zero))
      (c, m ## v') by split.
    by move=> /sss_output_fun /[apply] => /(_ (@mm_sss_fun _)) [_].
Qed.
