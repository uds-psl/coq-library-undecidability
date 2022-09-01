(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(* 
  Reduction from:
    (Alternative) Minsky Machine Halting with n Registers (MMA_HALTING n)
  to:
    Multi-tape Turing Machine Halting with n Tapes (HaltTM n)

  Argument:
    Read-only Turing machines with n tapes are n-counter machines [1].

  Literature
  [1] Marvin Minsky. Recursive unsolvability of Post’s problem of "tag" and
      other topics in theory of Turing machines. Annals of Mathematics, pages 437–455, 1961.
*)

From Undecidability.TM Require TM Util.TM_facts.
Import TM.
From Undecidability.MinskyMachines Require Import MM MMA.mma_defs.

From Undecidability.Shared.Libs.DLW
  Require Import Vec.pos Vec.vec Code.sss Code.subcode.

Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypesDef.

Require Import List Vector Lia PeanoNat Compare_dec.
Import ListNotations.
Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

Module Argument.
Section HaltTM_MMA_HALTING.

Context {n : nat} (M : list (mm_instr (Fin.t n))).

#[local] Notation maxState := (S (length M)).

Definition Σ : finType := finType_CS bool.

Definition state' : finType := finType_CS (Fin.t maxState).

Definition toState (p : nat) : state' :=
  if le_lt_dec maxState p is right H then Fin.of_nat_lt H else Fin.F1.

Definition trans' : state' * Vector.t (option Σ) n -> state' * Vector.t (option Σ * move) n :=
  fun '(p, bs) =>
    match sval (Fin.to_nat p) with
    | 0 => (p, TM_facts.nop_action)
    | S m' =>
        match nth_error M m' with
        | None => (p, TM_facts.nop_action)
        | Some (mm_inc i) =>
            let b := if (vec_pos bs i) is Some true then true else false in
            (toState (S (S m')), vec_change TM_facts.nop_action i (Some b, Rmove))
        | Some (mm_dec i q) =>
            match vec_pos bs i with
            | Some true => (toState (S (S m')), TM_facts.nop_action)
            | _ => (toState q, vec_change TM_facts.nop_action i (None, Lmove))
            end
        end
    end.

Definition halt' (q : Fin.t maxState) := Fin.eqb (@Fin.F1 (length M)) q.

Definition P : TM Σ n :=
  {| state := state'; trans := trans'; start := toState 1; halt := halt' |}.

Inductive encodes_counter : nat -> tape Σ -> Prop :=
  | encodes_counter_mid_0 m : encodes_counter 0 (midtape [] true (repeat false m))
  | encodes_counter_mid_S m c : encodes_counter (S c) (midtape (repeat false c ++ [true]) false (repeat false m))
  | encodes_counter_right_1 : encodes_counter 1 (rightof true [])
  | encodes_counter_right_S c : encodes_counter (S (S c)) (rightof false (repeat false c ++ [true])).

#[local] Notation encodes_counters cs ts := (Vector.Forall2 encodes_counter cs ts).

Definition encode_counter (c : nat) : tape Σ :=
  if c is S m then midtape (repeat false m ++ [true]) false [] else midtape [] true [].

Definition encode_counters {n} (cs : Vector.t nat n) : Vector.t (tape Σ) n :=
  Vector.map encode_counter cs.

Lemma read_instr {p instr} : (p, [instr]) <sc (1, M) ->
  exists q, sval (Fin.to_nat (toState p)) = S q /\ nth_error M q = Some instr /\ p = S q.
Proof.
  rewrite /toState. case: (le_lt_dec maxState p).
  { move=> ? [?] [?] [/(f_equal (@length _))].
    rewrite app_length /=. by lia. }
  move=> Hp [l] [r] [HM H'p]. exists (length l).
  by rewrite Fin.to_nat_of_nat /= HM nth_error_app2 ?Nat.sub_diag.
Qed.

Lemma doAct_nop_1 (t : tape Σ) : TM_facts.doAct t (None, Nmove) = t.
Proof. by case: t. Qed.

Lemma read_current_char {m} {cs : vec nat m} {ts i k} :
  encodes_counters cs ts -> vec_pos cs i = k ->
  match k with
  | 0 => vec_pos (TM_facts.current_chars ts) i = Some true
  | S _ =>
      vec_pos (TM_facts.current_chars ts) i = Some false \/
      vec_pos (TM_facts.current_chars ts) i = None
  end.
Proof.
  move=> H. elim: H i. { move=> i. by case: (pos_O_inv i). }
  move=> {}m c t {}cs {}ts Hct Hcsts IH i.
  have [->|[i' ->]] := pos_S_inv i.
  - case: Hct => /= *; subst k; by intuition done.
  - by apply: IH.
Qed.

#[local] Create HintDb counters.
Hint Extern 1 (encodes_counter _ _) => by [
  apply: encodes_counter_mid_0|apply: (encodes_counter_mid_0 0)|apply: (encodes_counter_mid_0 (S _))|
  apply: encodes_counter_mid_S|apply: (encodes_counter_mid_S 0)|apply: (encodes_counter_mid_S (S _))|
  apply: encodes_counter_right_1|apply: encodes_counter_right_S] : counters.

Lemma simulation_step {instr p1 cs1 p2 cs2 ts1} :
  (p1, [instr]) <sc (1, M) ->
  mma_sss instr (p1, cs1) (p2, cs2) ->
  encodes_counters cs1 ts1 ->
  exists ts2,
    TM_facts.step (M := P) (TM_facts.mk_mconfig (toState p1) ts1) = TM_facts.mk_mconfig (toState p2) ts2 /\
    encodes_counters cs2 ts2.
Proof.
  rewrite /TM_facts.step /= /trans'.
  move=> /read_instr [q [-> [-> ->]]].
  move E1: (S q, cs1) => p1cs1. move E2: (p2, cs2) => p2cs2 H.
  case: H E1 E2.
  - move=> ? i ? [<- <-] [-> ->] Hcs1ts1.
    eexists. split; first done.
    elim: Hcs1ts1 i. { move=> i. by case: (pos_O_inv i). }
    move=> m c t cs ts Hct Hcsts IH i.
    have [->|[i' ->]] := pos_S_inv i.
    + move=> /=. constructor; last by rewrite TM_facts.doAct_nop.
      rewrite /TM_facts.doAct. case: Hct => [[|?]|[|?] ?| |>].
      all: by eauto with counters nocore.
    + by constructor; [rewrite doAct_nop_1|apply: IH].
  - move=> ? i p' v Hcs1i [<- ?] [-> ->] Hcs1ts1. subst v.
    rewrite (read_current_char Hcs1ts1 Hcs1i).
    eexists. by split; [done|rewrite TM_facts.doAct_nop].
  - move=> ? i p' v k Hcs1i [_ ?] [-> ->] Hcs1ts1. subst v.
    move=> [:H].
    have [->|->] := (read_current_char Hcs1ts1 Hcs1i);
      eexists; split; [done|abstract: H|done|by apply: H].
    elim: Hcs1ts1 i Hcs1i. { move=> i. by case: (pos_O_inv i). }
    move=> m c t cs ts Hct Hcsts IH i.
    have [->|[i' ->]] := pos_S_inv i.
    + move=> /= Hc. constructor; last by rewrite TM_facts.doAct_nop.
      rewrite /TM_facts.doAct. case: Hct Hc => [//|? [|?]| |[|?]] [<-].
      all: by eauto with counters nocore.
    + move=> ?. by constructor; [rewrite doAct_nop_1|apply: IH].
Qed.

#[local] Notation "P // s ↓" := (sss_terminates (@mma_sss _) P s).

Lemma in_out_code_halt (p : nat) : 
  if halt' (toState p) then out_code p (1, M) else in_code p (1, M).
Proof.
  rewrite /halt' /toState.
  case: (le_lt_dec maxState p). { move=> ? /=. rewrite Nat.eqb_refl. by lia. }
  move: p => [|p] ? /=; rewrite ?Nat.eqb_refl; by lia.
Qed.

Lemma encodes_countersI (cs : Vector.t nat n) : encodes_counters cs (encode_counters cs).
Proof.
  elim: cs; first by constructor.
  move=> [|c] m cs IH; by eauto using @Forall2 with counters nocore.
Qed.

Lemma simulation st1 : (1, M) // st1 ↓ ->
  exists p ts,
    TM.eval P (toState (fst st1)) (encode_counters (snd st1)) p ts.
Proof.
  move=> Hst1.
  move: (encode_counters (snd st1)) (encodes_countersI (snd st1)).
  elim /sss_terminates_ind: Hst1.
  - by apply: mma_sss_fun.
  - move=> [p1 cs1].
    case Hp1: (halt' (toState p1)) (in_out_code_halt p1).
    + move=> *. do 2 eexists. by apply: eval_halt.
    + by move=> /in_out_code /[apply].
  - move=> [p1 cs1] IH ts Hts.
    case Hp1: (halt' (toState p1)) (in_out_code_halt p1).
    { do 2 eexists. by apply: eval_halt. }
    move=> /in_code_subcode [instr] HQ.
    have [[p2 cs2] H'p1p2] := mma_sss_total instr (p1, cs1).
    have /IH {}IH : sss_progress (mma_sss (n:=n)) (p1, [instr]) (p1, cs1) (p2, cs2).
    { exists 1. split; [done|]. apply: in_sss_steps_S; [|apply: in_sss_steps_0].
      exists p1, [], instr, [], cs1. by rewrite /= Nat.add_0_r. }
    have [ts' [H''p1p2]] := simulation_step HQ H'p1p2 Hts.
    move=> /(IH HQ) /= [p''] [ts''] /TM_facts.TM_eval_iff [k Hk].
    exists p'', ts''. apply /TM_facts.TM_eval_iff. exists (S k).
    by rewrite /= Hp1 H''p1p2.
Qed.

Lemma inverse_simulation p cs p' ts' :
  TM.eval P (toState p) (encode_counters cs) p' ts' -> (1, M) // (p, cs) ↓.
Proof.
  move: (encode_counters _) (encodes_countersI cs) => ts Hcsts.
  move=> /TM_facts.TM_eval_iff [k].
  have HM : forall p cs, out_code p (1, M) -> (1, M) // (p, cs) ↓.
  { move=> ???. eexists (_, _). split; [|by eassumption].
    exists 0. by apply: sss_steps_0. }
  elim: k p cs p' ts' ts Hcsts.
  - move=> p > ? /=.
    by move: (halt' (toState p)) (in_out_code_halt p) => [/HM|].
  - move=> k IH p1 cs1 p' ts' ts Hcsts /=.
    case: (halt' (toState p1)) (in_out_code_halt p1). { by move=> /HM. }
    move=> /in_code_subcode [instr] HQ.
    have [[p2 cs2] H'p1p2] := mma_sss_total instr (p1, cs1).
    have [ts'' [-> /IH /[apply]]] := simulation_step HQ H'p1p2 Hcsts.
    apply: subcode_sss_terminates_instr; by eassumption.
Qed.

End HaltTM_MMA_HALTING.
End Argument.

Require Import Undecidability.Synthetic.Definitions.

Theorem reduction {n} : @MMA_HALTING n ⪯ HaltTM n.
Proof.
  exists (fun '(M, cs) =>
    existT2 _ _ (finType_CS bool) (Argument.P M) (Argument.encode_counters cs)).
  move=> [M cs]. split.
  - by apply: Argument.simulation.
  - by move=> [p'] [ts] /Argument.inverse_simulation.
Qed.
