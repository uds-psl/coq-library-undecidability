(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  If a relation R is MMA_mon_computable then it is TM_computable.

  Monotonicity of the first counter is needed because a TM cannot erase (only replace) type symbols.
*)

From Undecidability.TM Require Import TM.
From Undecidability.TM Require Util.TM_facts Util.TM_computable.

From Undecidability.MinskyMachines Require Import
  MM MMA.mma_defs Reductions.MMA_computable_to_MMA_mon_computable.

From Undecidability.Shared.Libs.DLW
  Require Import Vec.pos Vec.vec Code.sss Code.subcode.

Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypesDef.
From Undecidability.Shared.Libs.PSL Require Import CompoundFinTypes.
Require Import Undecidability.Shared.Libs.PSL.EqDec.

From Undecidability Require Shared.deterministic_simulation.
Module Sim := deterministic_simulation.

Require Import List Lia PeanoNat Compare_dec Relations.
Import ListNotations.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

#[local] Unset Implicit Arguments.

#[local] Notation enc := (encNatTM true false).

(* generic auxiliary facts *)
Module Facts.

Lemma vec_Forall2_append {X Y : Type} {P : X -> Y -> Prop} {n m : nat} {v : Vector.t X n} {w : Vector.t X m} {v' w'} :  
  Vector.Forall2 P v v' -> Vector.Forall2 P w w' ->
  Vector.Forall2 P (Vector.append v w) (Vector.append v' w').
Proof.
  elim. { done. }
  move=> > ? _ /[apply] ?. by constructor.
Qed.

Lemma vec_Forall2_forall {X Y : Type} {P : X -> Y -> Prop} {n : nat} {v : Vector.t X n} {w : Vector.t Y n} :
  (forall i, P (Vector.nth v i) (Vector.nth w i)) <->
  Vector.Forall2 P v w.
Proof.
  split.
  - elim: v w.
    + move=> w ?. rewrite (vec_0_nil w). by constructor.
    + move=> > IH w. rewrite (Vector.eta w) => IH'. constructor.
      * by apply: (IH' pos0).
      * apply: IH => i.
        by apply: (IH' (pos_nxt i)).
  - elim. { by apply: Fin.case0. }
    move=> > ? _ IH i.
    have [->|[j ->]] := pos_S_inv i.
    + done.
    + by apply: IH.
Qed.

Lemma split_nth_error {X : Type} {l : list X} {ls x rs} :
  l = ls ++ x :: rs ->
  nth_error l (length ls) = Some x.
Proof.
  move=> ->. by elim: ls.
Qed.

Lemma vec_pos_nth_eq {X : Type} {n} {v : Vector.t X n} {i} : vec_pos v i = Vector.nth v i.
Proof.
  elim: v i. { by apply: Fin.case0. }
  move=> > IH i.
  have [->|[? ->]] := pos_S_inv i.
  - done.
  - apply: IH.
Qed.

End Facts.
Import Facts.

Module Argument.
Section HaltTM_MMA_HALTING.

Context {n : nat} (M : list (mm_instr (Fin.t (S n)))).
Context (M_mon : forall l x q r, M = l ++ DEC x q :: r -> x <> pos0).

#[local] Notation maxState := (S (length M)).

Definition Σ : finType := finType_CS bool.

Definition state' : finType := finType_CS (bool * Fin.t maxState).

Definition toAddress (p : nat) : Fin.t maxState :=
  if le_lt_dec maxState p is right H then Fin.of_nat_lt H else Fin.F1.

Definition toState (d : bool) (p : nat) : state' := (d, toAddress p).

(*
  INC : write true, move left; write false
  DEC : move right ; write false
*)
Definition trans' : state' * Vector.t (option Σ) (S n) -> state' * Vector.t (option Σ * move) (S n) :=
  fun '((d, p), bs) =>
    match sval (Fin.to_nat p) with
    | 0 =>
        match d with
        | false => ((d, p), TM_facts.nop_action)
        | true => (toState false 1, Vector.const (Some false, Nmove) (S n))
        end
    | S m' =>
      match nth_error M m' with
      | None => ((d, p), TM_facts.nop_action)
      | Some (mm_inc i) =>
          match d with
          | false => ((true, p), vec_change TM_facts.nop_action i (Some true, Lmove))
          | true => (toState false (S (S m')), vec_change TM_facts.nop_action i (Some false, Nmove))
          end
      | Some (mm_dec i q) =>
          match d with
          | false => ((true, p), vec_change TM_facts.nop_action i (None, Rmove))
          | true =>
              match Vector.nth bs i with
              | Some true => (toState false q, vec_change TM_facts.nop_action i (Some false, Nmove))
              | _ => (toState false (S (S m')), vec_change TM_facts.nop_action i (Some false, Nmove))
              end
          end
      end
    end.

#[local] Opaque le_lt_dec Fin.of_nat_lt.

Definition halt' (q : bool * Fin.t maxState) := (negb (fst q)) && Fin.eqb (@Fin.F1 (length M)) (snd q).

Definition P : TM Σ (S n) :=
  {| state := state'; trans := trans'; start := (true, pos0); halt := halt' |}.

Inductive encodes_counter (c : nat) : tape Σ -> Prop :=
  | encodes_counter_intro m : encodes_counter c (midtape (repeat false m) false (repeat true c)).

#[local] Notation encodes_counters cs ts := (Vector.Forall2 encodes_counter cs ts).

#[local] Notation step1 := (sss_step (@mma_sss (S n)) (1, M)).
#[local] Notation step2 := (fun x y => halt' (TM_facts.cstate x) = false /\ y = @TM_facts.step _ _ P x).

#[local] Notation "P // s ->> t" := (sss_compute (@mma_sss _) P s t).

Inductive sync : nat * Vector.t nat (S n) -> TM_facts.mconfig Σ (state P) (S n) -> Prop :=
  | sync_intro i v bs :
    encodes_counters v bs ->
    Vector.nth bs pos0 = enc (Vector.nth v pos0) ->
    sync (i, v) (TM_facts.mk_mconfig (toState false i) bs).

Lemma syncE i v p bs : sync (i, v) (TM_facts.mk_mconfig p bs) ->
  encodes_counters v bs /\ Vector.nth bs pos0 = enc (Vector.nth v pos0) /\ p = toState false i.
Proof.
  intros H. now inversion H.
Qed.

Definition inc_bs {n} x (ts : Vector.t (tape Σ) (S n)) :=
  TM_facts.doAct_multi
    (TM_facts.doAct_multi ts (vec_change TM_facts.nop_action x (Some true, Lmove)))
    (vec_change TM_facts.nop_action x (Some false, Nmove)).

Definition dec_bs {n} x (ts : Vector.t (tape Σ) (S n)) :=
  TM_facts.doAct_multi
    (TM_facts.doAct_multi ts (vec_change TM_facts.nop_action x (None, Rmove)))
    (vec_change TM_facts.nop_action x (Some false, Nmove)).

Lemma to_nat_toAddress {l instr r} :
  M = l ++ instr :: r ->
  sval (Fin.to_nat (toAddress (S (length l)))) = S (length l).
Proof.
  move=> HM. rewrite /toAddress /=.
  case: (le_lt_dec maxState (S (length l))).
  - move: HM => /(f_equal (@length _)).
    rewrite length_app /=. lia.
  - move=> ?. by rewrite Fin.to_nat_of_nat.
Qed.

Lemma sync_inc p v i ts :
  Vector.nth ts pos0 = enc (Vector.nth v pos0) ->
  encodes_counters v ts ->
  sync (p, vec_change v i (S (Vector.nth v i))) (TM_facts.mk_mconfig (toState false p) (inc_bs i ts)).
Proof.
  move=> H0vts /vec_Forall2_forall Hvts. apply: sync_intro.
  - rewrite /inc_bs. apply /vec_Forall2_forall => j.
    have [<-|Hij] := pos_eq_dec i j.
    + rewrite /TM_facts.doAct_multi.
      rewrite !TM_facts.nth_map2'.
      rewrite -!vec_pos_nth_eq.
      rewrite !(vec_change_eq _ _ erefl).
      rewrite !vec_pos_nth_eq.
      move: (Vector.nth v i) (Vector.nth ts i) (Hvts i).
      move=> ? ? [] [|?].
      * by apply: (encodes_counter_intro _ 0).
      * by apply: encodes_counter_intro.
    + rewrite /TM_facts.doAct_multi.
      rewrite !TM_facts.nth_map2'.
      rewrite -!vec_pos_nth_eq.
      rewrite !(vec_change_neq _ _ Hij).
      rewrite !vec_pos_nth_eq !TM_facts.nth_nop_action.
      by apply: Hvts.
  - rewrite /inc_bs.
    move: H0vts. rewrite (Vector.eta v) (Vector.eta ts).
    have [->|[j ->]] := pos_S_inv i.
    + move=> /= ->. by case: (VectorDef.hd v) => /=.
    + by move=> /= ->.
Qed.

Lemma sync_dec_0 p v i ts :
  Vector.nth ts pos0 = enc (Vector.nth v pos0) ->
  encodes_counters v ts ->
  Vector.nth v i = 0 ->
  i <> pos0 ->
  sync (p, v) (TM_facts.mk_mconfig (toState false p) (dec_bs i ts)).
Proof.
  move=> H0vts /vec_Forall2_forall Hvts Hvi Hi. apply: sync_intro.
  - rewrite /dec_bs. apply /vec_Forall2_forall => j.
    have [<-|Hij] := pos_eq_dec i j.
    + rewrite /TM_facts.doAct_multi.
      rewrite !TM_facts.nth_map2'.
      rewrite -!vec_pos_nth_eq.
      rewrite !(vec_change_eq _ _ erefl).
      rewrite !vec_pos_nth_eq.
      move: (Vector.nth v i) (Vector.nth ts i) Hvi (Hvts i).
      move=> > -> [] m.
      by apply: (encodes_counter_intro _ (S m)).
    + rewrite /TM_facts.doAct_multi.
      rewrite !TM_facts.nth_map2'.
      rewrite -!vec_pos_nth_eq.
      rewrite !(vec_change_neq _ _ Hij).
      rewrite !vec_pos_nth_eq !TM_facts.nth_nop_action.
      by apply: Hvts.
  - rewrite /dec_bs.
    move: H0vts Hi. rewrite (Vector.eta v) (Vector.eta ts).
    have [->|[j ->]] := pos_S_inv i.
    + done.
    + by move=> /= ->.
Qed.

Lemma sync_dec_S p v i ts k :
  Vector.nth ts pos0 = enc (Vector.nth v pos0) ->
  encodes_counters v ts ->
  Vector.nth v i = S k ->
  i <> pos0 ->
  sync (p, vec_change v i k) (TM_facts.mk_mconfig (toState false p) (dec_bs i ts)).
Proof.
  move=> H0vts /vec_Forall2_forall Hvts Hvi Hi. apply: sync_intro.
  - rewrite /dec_bs. apply /vec_Forall2_forall => j.
    have [<-|Hij] := pos_eq_dec i j.
    + rewrite /TM_facts.doAct_multi.
      rewrite !TM_facts.nth_map2'.
      rewrite -!vec_pos_nth_eq.
      rewrite !(vec_change_eq _ _ erefl).
      rewrite !vec_pos_nth_eq.
      move: (Vector.nth v i) (Vector.nth ts i) Hvi (Hvts i).
      move=> > -> [] m.
      by apply: (encodes_counter_intro _ (S m)).
    + rewrite /TM_facts.doAct_multi.
      rewrite !TM_facts.nth_map2'.
      rewrite -!vec_pos_nth_eq.
      rewrite !(vec_change_neq _ _ Hij).
      rewrite !vec_pos_nth_eq !TM_facts.nth_nop_action.
      by apply: Hvts.
  - rewrite /dec_bs.
    move: H0vts Hi. rewrite (Vector.eta v) (Vector.eta ts).
    have [->|[j ->]] := pos_S_inv i.
    + done.
    + by move=> /= ->.
Qed.

Lemma current_chars_act k (ts : Vector.t (tape Σ) k) i actions action :
  Vector.nth (TM_facts.current_chars (TM_facts.doAct_multi ts
    (vec_change actions i action))) i = current (TM_facts.doAct (Vector.nth ts i) action).
Proof.
  elim: ts i actions. { by apply: Fin.case0. }
  move=> t ? ts IH i actions.
  rewrite (Vector.eta actions).
  have [->|[j ->]] := pos_S_inv i.
  - done.
  - by apply: IH.
Qed.

Lemma Vector_nth_tapes {k v ts} (i : Fin.t k) :
  encodes_counters v ts ->
  exists m, Vector.nth ts i = midtape (repeat false m) false (repeat true (Vector.nth v i)).
Proof.
  move=> H. elim: H i. { by apply: Fin.case0. }
  move=> > [] > ? IH i.
  have [->|[j ->]] := pos_S_inv i.
  - by eexists.
  - by apply: (IH j).
Qed.

#[local] Opaque toAddress.
#[local] Opaque vec_change TM_facts.nop_action.

Lemma fstep (s t : nat * vec nat (S n)) (s' : TM_facts.mconfig Σ (state P) (S n)) :
  sss_step (@mma_sss _) (1, M) s t ->
  sync s s' ->
  exists t', clos_trans _ step2 s' t' /\ sync t t'.
Proof using M_mon.
  move=> [?] [l] [instr] [r] [{}v] [[<- HM]] [->].
  move E: ((1 + (length l), v)) => st H.
  case: H HM E.
  - (* inc *)
    move=> ? x ? HM [<- <-].
    move: s' => [p ts] /syncE [Hvts [E0 ->]].
    exists (TM_facts.mk_mconfig (toState false (1 + (1 + (length l)))) (inc_bs x ts)).
    split; [apply: t_trans; (apply: t_step; split)|].
    + cbn. 
      have := to_nat_toAddress HM.
      by case: (toAddress (S (length l))).
    + by rewrite /TM_facts.step /= (to_nat_toAddress HM) (split_nth_error HM).
    + done.
    + by rewrite /TM_facts.step /= (to_nat_toAddress HM) (split_nth_error HM).
    + rewrite vec_pos_nth_eq. by apply: sync_inc.
  - (* dec_0 *)
    move=> ? x q v' Hx HM [<- ?]. subst v'.
    rewrite vec_pos_nth_eq in Hx.
    move: s' => [p ts] /syncE [Hvts [E0 ->]].
    exists (TM_facts.mk_mconfig (toState false (1 + (1 + (length l)))) (dec_bs x ts)).
    move: (HM) => /M_mon ?.
    split; [apply: t_trans; (apply: t_step; split)|].
    + cbn.
      have := to_nat_toAddress HM.
      by case: (toAddress (S (length l))).
    + by rewrite /TM_facts.step /= (to_nat_toAddress HM) (split_nth_error HM).
    + done.
    + rewrite /TM_facts.step /= (to_nat_toAddress HM) (split_nth_error HM).
      rewrite current_chars_act.
      have [? ->] := Vector_nth_tapes x Hvts.
      by rewrite Hx /=.
    + by apply: sync_dec_0.
  - (* dec_1 *)
    move=> ? x q v' ? Hx HM [<- ?]. subst v'.
    rewrite vec_pos_nth_eq in Hx.
    move: s' => [p ts] /syncE [Hvts [E0 ->]].
    exists (TM_facts.mk_mconfig (toState false q) (dec_bs x ts)).
    move: (HM) => /M_mon ?.
    split; [apply: t_trans; (apply: t_step; split)|].
    + cbn.
      have := to_nat_toAddress HM.
      by case: (toAddress (S (length l))).
    + by rewrite /TM_facts.step /= (to_nat_toAddress HM) (split_nth_error HM).
    + done.
    + rewrite /TM_facts.step /= (to_nat_toAddress HM) (split_nth_error HM).
      rewrite current_chars_act.
      have [? ->] := Vector_nth_tapes x Hvts.
      by rewrite Hx /=.
    + by apply: sync_dec_S.
Qed.

Lemma simulation i v i' v' st : (1, M) // (i, v) ->> (i', v') ->
  sync (i, v) st ->
  exists st', sync (i', v') st' /\ clos_refl_trans _ step2 st st'.
Proof using M_mon.
  move=> /sss_compute_iff H1 H2. by apply: (Sim.clos_refl_trans_transport fstep H2 H1).
Qed.

Lemma step2_det s t1 t2 : step2 s t1 -> step2 s t2 -> t1 = t2.
Proof.
  by move=> /= [_ ->] [_ ->].
Qed.

Lemma step1_intro s : (exists t, step1 s t) \/ (Sim.stuck step1 s).
Proof.
  have [|] := subcode.in_out_code_dec (fst s) (1, M).
  - move=> /in_code_step ?. by left.
  - move=> /out_code_iff ?. by right.
Qed.

Lemma halt'_terminates s' : halt' (TM_facts.cstate s') = true -> Sim.terminates step2 s'.
Proof.
  move:s' => [[[] p] ts] /=; [done|].
  rewrite /halt' /=.
  have [->|[q ->]] := pos_S_inv p; [|done].
  rewrite Nat.eqb_refl /= => _. eexists.
  split; [apply: rt_refl|].
  move=> {}t' /=. rewrite Nat.eqb_refl. by case.
Qed.

Lemma terminates2I k {s' t' : TM_facts.mconfig Σ (state P) (S n)} :
  TM_facts.loopM s' k = Some t' ->
  Sim.terminates step2 s'.
Proof.
  elim: k s'.
  { move=> s' /= Hs'. apply: halt'_terminates.
    by case: (halt' (TM_facts.cstate s')) Hs'. }
  move=> k IH s' /=.
  case E: (halt' (TM_facts.cstate s')) => [].
  - move=> ?. by apply: halt'_terminates.
  - move=> /IH [u'] [? ?]. exists u'. split; [|done].
    by apply: rt_trans; [apply: rt_step|eassumption].
Qed.

Lemma stuck_step2E s' :
  Sim.stuck step2 s' -> halt' (TM_facts.cstate s') = true.
Proof.
  move=> Hs'.
  case E: (halt' (TM_facts.cstate s')); [done|].
  exfalso.
  by apply: (Hs' (@TM_facts.step _ _ P s')).
Qed.

Lemma terminates2E {s' t' : TM_facts.mconfig Σ (state P) (S n)} :
  clos_refl_trans _ step2 s' t' -> Sim.stuck step2 t' ->
  exists k, TM_facts.loopM s' k = Some t'.
Proof.
  move=> /clos_rt_rt1n_iff. elim.
  - move=> {}s' /stuck_step2E Hs'.
    exists 0. by rewrite /= Hs'.
  - move=> > [E ->] _ /[apply] - [k] ?.
    exists (S k). by rewrite /= E.
Qed.

#[local] Transparent toAddress.

Lemma stuck_step2I {s s'} :
  sync s s' ->
  out_code (fst s) (1, M) ->
  Sim.stuck step2 s'.
Proof.
  case => i v bs _ _ /= Hi t' /=.
  rewrite /halt' /= /toAddress.
  case: (le_lt_dec maxState i) => /=.
  { rewrite Nat.eqb_refl => ?. by case. }
  move=> H'i. have ? : i = 0 by lia. subst i.
  suff -> : Fin.of_nat_lt H'i = pos0.
  { rewrite Nat.eqb_refl. by case. }
  rewrite [RHS](esym (Fin.of_nat_to_nat_inv pos0)).
  by apply: Fin.of_nat_ext.
Qed.

End HaltTM_MMA_HALTING.
End Argument.

Import Argument.

Lemma P_init {k k'} {M : list (mm_instr (pos (1+k+k')))} {v : Vector.t nat k} :
  @TM_facts.step _ _ (P M) (TM_facts.mk_mconfig (true, pos0) (niltape ## Vector.append (Vector.map enc v) (Vector.const niltape k'))) =
  TM_facts.mk_mconfig (toState M false 1) (enc 0 ## Vector.append (Vector.map enc v) (Vector.const (enc 0) k')).
Proof.
  cbn. congr TM_facts.mk_mconfig. congr Vector.cons.
  elim: v.
  - cbn. elim: (k'). { done. }
    by move=> > /= ->.
  - by move=> > /= ->.
Qed.

Lemma sync_init {k k'} {M : list (mm_instr (pos (1+k+k')))} {v : Vector.t nat k} : @sync _ M
  (1, Vector.append (0 ## v) (Vector.const 0 k'))
  (TM_facts.mk_mconfig (toState M false 1) (Vector.append ((enc 0) ## Vector.map enc v) (Vector.const (enc 0) k'))).
Proof.
  apply: sync_intro; [|done] => /=.
  constructor. { by apply: (encodes_counter_intro _ 0). }
  apply: vec_Forall2_append.
  - elim: v. { by constructor. }
    move=> *. constructor; [|done].
    by apply: (encodes_counter_intro _ 0).
  - clear. elim: k'. { by constructor. }
    move=> *. constructor; [|done].
    by apply: (encodes_counter_intro _ 0).
Qed.

Theorem MMA_mon_computable_to_TM_computable k (R : Vector.t nat k -> nat -> Prop) :
  MMA_mon_computable R -> TM_computable R.
Proof.
  move=> /MMA_mon_computable_iff [k'] [M] [H1M [H2M H3M]].
  have : forall l x q r, M = l ++ DEC x q :: r -> x <> pos0.
  { move=> > HM Hi. by move: HM Hi H1M => -> -> /Forall_app [_] /Forall_cons_iff []. }
  move=> {}H1M. apply /TM_computable.TM_computable_iff.
  exists k', Argument.Σ, true, false.
  split; [done|]. exists (Argument.P M). split.
  - move=> v m /H2M [c] [v'] [] /(simulation M H1M) => /(_ _ sync_init).
    move=> [[p' b's]] [Hst'] + Hc.
    move: (Hst') Hc => /stuck_step2I /[apply] /terminates2E /[apply].
    move=> [n] Hn. exists p', b's. split.
    + apply /TM_facts.TM_eval_iff.
      exists (S n) => /=. by rewrite P_init.
    + move: Hst' => /syncE. rewrite (Vector.eta b's) /=.
      by move=> [_ []].
  - move=> v q ts /TM_facts.TM_eval_iff [n HPn].
    apply: H3M. apply /sss_terminates_iff.
    apply /(Sim.terminates_reflection (step2_det M) (fstep M H1M) (step1_intro M) sync_init).
    move: n HPn => [|n]. { done. }
    rewrite /= P_init. by apply: terminates2I.
Qed.
