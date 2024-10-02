(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  If a relation R is MM_computable then it is MMA_computable
*)

From Undecidability.MinskyMachines Require Import MM MMA MMA.mma_defs MM.mm_defs Util.MMA_computable Util.MMA_facts Util.MM_computable MM.mm_defs.
Require Import Undecidability.MinskyMachines.Util.MM_sss.

From Undecidability.Shared.Libs.DLW
  Require Import Vec.pos Vec.vec Code.sss.

Require Import Undecidability.Shared.simulation.

Require Import List PeanoNat Lia Relations.
Import ListNotations.

Require Import ssreflect.

Set Default Goal Selector "!".

(* generic auxiliary facts *)
Lemma clos_t_rt_t {A : Type} {R : relation A} (x y z : A) :
  clos_trans A R x y -> clos_refl_trans A R y z -> clos_trans A R x z.
Proof.
  move=> H /clos_rt_rtn1_iff H'. elim: H' H; by eauto using clos_trans.
Qed.

Module MM_MMA.

Section FixedMMA.
Context {num_counters : nat}.
Context {P : list (mm_instr (pos num_counters))}.

Definition addr (i : nat) := (i * 3) - 2.

Lemma addr_spec i : addr i = (i * 3) - 2.
Proof. done. Qed.

Opaque addr.

Definition enc_instr '(i, instr) : list (mm_instr (pos num_counters)) :=
  match instr with
  | INC X => [INC X; INC X; DEC X (addr (S i))]
  | DEC X p => [DEC X (addr (S i)); INC X; DEC X (addr p)]
  end.

Definition P' : list (mm_instr (pos num_counters)) :=
  concat (map enc_instr (combine (seq 1 (length P)) P)).

Lemma length_P' : length P' = length P * 3.
Proof.
  rewrite /P' length_concat. move: (x in seq x).
  elim: (P); first done.
  move=> [] > /= IH ?; by rewrite IH.
Qed.

Lemma P'_spec i {instr l r} :
  i - 2 = 0 ->
  P = l ++ instr :: r ->
  nth_error P' (length l * 3 + i) = nth_error (enc_instr (S (length l), instr)) i.
Proof.
  move=> Hi. rewrite /P'=> ->.
  suff: forall k, nth_error
    (concat (map enc_instr (combine (seq k (length (l ++ instr :: r))) (l ++ instr :: r)))) (length l * 3 + i) =
      nth_error (enc_instr (k + (length l), instr)) i by apply.
  elim: l.
  - move=> k. rewrite /= Nat.add_0_r.
    by move: i Hi instr => [|[|[|?]]] ? [] /=; try lia.
  - move=> [] > IH ? /=.
    + rewrite IH. congr nth_error. by rewrite !(Nat.add_succ_r _ (length _)).
    + rewrite IH. congr nth_error. by rewrite !(Nat.add_succ_r _ (length _)).
Qed.

#[local] Arguments firstn_skipn_middle {A n l x}.

Lemma simulation_sss_step st st' : 
  sss_step (mm_sss (n:=num_counters)) (1, P) st st' ->
  clos_trans _ (sss_step (mma_sss (n:=num_counters)) (1, P')) (addr (fst st), snd st) (addr (fst st'), snd st').
Proof.
  move: st'=> [i' v'] [offset] [l] [[]] x > [r] [v] [[<- HP]] [->].
  - (* INC *)
    move=> /mm_sss_INC_inv [-> ->] /=.
    apply: t_trans.
    { apply: t_step.
      rewrite -(firstn_skipn_middle (P'_spec 0 eq_refl HP)). apply: in_sss_step.
      - rewrite /= addr_spec length_firstn length_P' HP length_app /=. lia.
      - by apply: in_mma_sss_inc. }
    apply: t_trans.
    { apply: t_step. rewrite -(firstn_skipn_middle (P'_spec 1 eq_refl HP)). apply: in_sss_step.
      - rewrite /= addr_spec length_firstn length_P' HP length_app /=. lia.
      - by apply: in_mma_sss_inc. }
    apply: clos_t_rt_t.
    { apply: t_step. rewrite -(firstn_skipn_middle (P'_spec 2 eq_refl HP)). apply: in_sss_step.
      - rewrite /= addr_spec length_firstn length_P' HP length_app /=. lia.
      - apply: in_mma_sss_dec_1. by rewrite vec_change_eq. }
    rewrite !vec_change_idem vec_change_eq; first done.
    by apply: rt_refl.
  - (* DEC *) 
    move E: (vec_pos v x) => [|?].
    + move=> /mm_sss_DEC0_inv => /(_ E) [-> ->] /=.
      apply: t_trans.
      { apply: t_step. rewrite -(firstn_skipn_middle (P'_spec 0 eq_refl HP)). apply: in_sss_step.
        - rewrite /= addr_spec length_firstn length_P' HP length_app /=. lia.
        - by apply: in_mma_sss_dec_0. }
      apply: t_trans.
      { apply: t_step. rewrite -(firstn_skipn_middle (P'_spec 1 eq_refl HP)). apply: in_sss_step.
        - rewrite /= addr_spec length_firstn length_P' HP length_app /=. lia.
        - by apply: in_mma_sss_inc. }
      apply: clos_t_rt_t.
      { apply: t_step. rewrite -(firstn_skipn_middle (P'_spec 2 eq_refl HP)). apply: in_sss_step.
        - rewrite /= addr_spec length_firstn length_P' HP length_app /=. lia.
        - apply: in_mma_sss_dec_1. by rewrite vec_change_eq. }
      rewrite !vec_change_idem vec_change_same. by apply: rt_refl.
    + move=> /mm_sss_DEC1_inv => /(_ _ E) [-> ->] /=.
      apply: clos_t_rt_t.
      { apply: t_step. rewrite -(firstn_skipn_middle (P'_spec 0 eq_refl HP)). apply: in_sss_step.
        - rewrite /= addr_spec length_firstn length_P' HP length_app /=. lia.
        - apply: in_mma_sss_dec_1. by eassumption. }
      by apply: rt_refl.
Qed.

Definition sync : nat * Vector.t nat num_counters -> nat * Vector.t nat num_counters -> Prop :=
  fun s s' => s' = (addr (fst s), snd s).

#[local] Notation step1 := (sss_step (@mm_sss num_counters) (1, P)).
#[local] Notation step2 := (sss_step (@mma_sss num_counters) (1, P')).

Lemma fstep s t s' : step1 s t -> sync s s' ->
  exists t', clos_trans _ step2 s' t' /\ sync t t'.
Proof.
  move=> /simulation_sss_step ? ->.
  eexists. by split; [eassumption|].
Qed.

Lemma step2_det s' t1' t2' :
  sss_step (@mma_sss _) (1, P') s' t1' ->
  sss_step (@mma_sss _) (1, P') s' t2' -> t1' = t2'.
Proof.
  apply: sss_step_fun. by apply: mma_sss_fun.
Qed.

Lemma simulation v v' c :
  sss_compute (mm_sss (n:= num_counters)) (1, P) (1, v) (c, v') ->
  c < 1 \/ S (length P) <= c ->
  sss_compute (mma_sss (n:= num_counters)) (1, P') (addr 1, v) (addr c, v').
Proof.
  move=> /sss_compute_iff.
  move=> /(clos_refl_trans_transport fstep) => /(_ _ eq_refl).
  move=> [t'] [->] ??.
  by apply /sss_compute_iff.
Qed.

End FixedMMA.
End MM_MMA.

Theorem MM_computable_to_MMA_computable k (R : Vector.t nat k -> nat -> Prop) :
  MM_computable R -> MMA_computable R.
Proof.
  move=> /MM_computable_iff [k'] [P] [H1P H2P].
  apply /MMA_computable_iff.
  exists k', (@MM_MMA.P' _ P). split.
  - move=> v m /H1P [c] [v'] /=.
    move=> /[dup] /eval_to_sss_compute + /eval_to_sss_out_code.
    move=> /= + /[dup] Hc => /MM_MMA.simulation /[apply] ?.
    eexists _, _. split; [eassumption|].
    rewrite /= MM_MMA.length_P' MM_MMA.addr_spec.
    move: Hc => /=. lia.
  - move=> v /(sss_terminates_iff (@mma_sss_total_ni _)) Hv. apply: H2P.
    apply /(sss_terminates_iff (@mm_sss_total_ni _)). move: Hv.
    by apply /(terminates_reflection (deterministic_uniformly_confluent _ MM_MMA.step2_det) MM_MMA.fstep (sss_step_or_stuck (@mm_sss_total_ni _) 1 P)).
Qed.
