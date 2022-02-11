From Undecidability Require TM.TM TM.Util.TM_facts.
From Undecidability Require Import TM.SBTM2 TM.Util.SBTM2_facts.
Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypes.

Require Import PeanoNat Lia.

#[local] Unset Implicit Arguments.
#[local] Unset Strict Implicit.

Require Import List ssreflect ssrbool ssrfun.
Import ListNotations SBTM2Notations.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

#[local] Notation "| a |" := (Vector.cons _ a 0 (Vector.nil _)).

Section Construction.
  (* input SBTM2 and initial state *)
  Context (M : SBTM2) (q0 : state M).

  Definition encode_tape (t : tape) : TM.tape (finType_CS bool) :=
    match t with
    | (ls, a, rs) => TM.midtape ls a rs
    end.

  #[local] Notation state' := (option (Fin.t ((num_states M)))).

  Definition finTypeC_state' : finType := 
    @finType_CS state' _ (CompoundFinTypes.finTypeC_Option _).

  Definition halt' (q : state') : bool := if q is None then true else false.

  Definition get_symbol (ob : option (finType_CS bool)) : bool :=
    match ob with
    | None => false
    | Some b => b
    end.

  Definition encode_direction (d : direction) :=
    match d with
    | go_left => TM.Lmove
    | go_right => TM.Rmove
    end.

  Definition M' : TM.TM (finType_CS bool) 1.
  Proof using M q0.
    refine (@TM.Build_TM _ _ finTypeC_state' (fun '(q, bs) => _) (Some q0) halt').
    refine (
      match q with
      | Some qM => _
      | None => (None, | (None, TM.Nmove) | )
      end).
    refine (
      match trans M (qM, get_symbol (Vector.hd bs)) with
      | None => (None, | (None, TM.Nmove) | )
      | Some (q', a', d') => (Some q', | (Some a',encode_direction d') | )
      end).
  Defined.

  #[local] Notation TM_step x := (@TM_facts.step _ _ M' x).
  #[local] Notation TM_config := (@TM_facts.mconfig (finType_CS bool) (TM.state M') 1).

  Definition encode_config : config M -> TM_config :=
    fun '(q, t) => TM_facts.mk_mconfig (Some q) (| encode_tape t |).

  Definition canonize_tape (t : TM.tape (finType_CS bool)) :=
    match t with
    | TM.niltape => TM.midtape [] false []
    | TM.leftof r rs => TM.midtape [] false (r :: rs)
    | TM.rightof l ls => TM.midtape (l :: ls) false []
    | _ => t
    end.

  Lemma get_symbol_canonize_tape {t1 t2} : 
    canonize_tape t1 = canonize_tape t2 ->
    get_symbol (TM.current t1) = get_symbol (TM.current t2).
  Proof.
    move: t1 t2 => [ | ?? | ?? | ???] [] > /=; congruence.
  Qed.

  Lemma doAct_canonize_tape {t1 t2} a d : 
    canonize_tape t1 = canonize_tape t2 ->
    canonize_tape (TM_facts.doAct t1 (Some a, encode_direction d)) =
    canonize_tape (TM_facts.doAct t2 (Some a, encode_direction d)).
  Proof.
    move: d t1 t2.
    move=> [] [ | ?? | ?? | [|??]?[|??] ] [ | ?? | ?? | [|??]?[|??] ] /=; cbn; congruence.
  Qed.

  Lemma TM_step_canonize_tape oq oq1 t1 t'1 oq2 t2 t'2 :
    canonize_tape t1 = canonize_tape t2 ->
    TM_step (TM_facts.mk_mconfig oq (| t1 |)) = TM_facts.mk_mconfig oq1 (| t'1 |) ->
    TM_step (TM_facts.mk_mconfig oq (| t2 |)) = TM_facts.mk_mconfig oq2 (| t'2 |) ->
    oq1 = oq2 /\ canonize_tape t'1 = canonize_tape t'2.
  Proof.
    move=> Ht1t2.
    rewrite /TM_facts.step /= -(get_symbol_canonize_tape Ht1t2).
    case: oq => [q|].
    - move: (trans M _) => [[[q' a'] d']|] /=.
      + move=> [] <- <- [] <- <-. split; first done.
        by apply: doAct_canonize_tape.
      + by move=> [] <- <- [] <- <-.
    - by move=> [] <- <- [] <- <-.
  Qed.

  Lemma TM_loopM_canonize_tape (oq : TM.state M') t1 t2 k q' t'1 :
    canonize_tape t1 = canonize_tape t2 ->
    TM_facts.loopM (TM_facts.mk_mconfig oq (| t1 |)) k = Some (TM_facts.mk_mconfig q' t'1) ->
    { t'2 | TM_facts.loopM (TM_facts.mk_mconfig oq (| t2 |)) k = Some (TM_facts.mk_mconfig q' t'2) }.
  Proof.
    elim: k oq t1 t2.
    { move=> > _ /=. case: (halt' _) => [|]; last done.
      move=> [] /= -> _. by eexists. }
    move=> k IH oq t1 t2 Ht1t2 /=.
    case: (halt' _) => [|] /=. { move=> [] -> _. by eexists. }
    move E1: (TM_step _) => [q1 ts1]. move E2: (TM_step _) => [q2 ts2].
    move: E1 E2.
    rewrite (Vector.eta ts1). move: (VectorDef.tl ts1). apply: Vector.case0.
    rewrite (Vector.eta ts2). move: (VectorDef.tl ts2). apply: Vector.case0.
    move: (Ht1t2) => /TM_step_canonize_tape /[apply] /[apply].
    move=> [<-] /IH. by apply.
  Qed.

  (* step simulation up to canonize_tape *)
  Lemma simulation_step q t q' t' : step M (q, t) = Some (q', t') ->
    { t'' |
      TM_step (encode_config (q, t)) = TM_facts.mk_mconfig (Some q') (| t'' |) /\
      encode_tape t' = canonize_tape t'' }.
  Proof.
    rewrite /step /TM_facts.step /=.
    move: t => [[ls a] rs] /=. case: (trans M _) => [[[? ?] d]|] /=; last done.
    move=> [] -> <-. case: d => /=.
    - case: ls => [|??] /=; eexists; split; reflexivity.
    - case: rs => [|??] /=; eexists; split; reflexivity.
  Qed.

  Lemma simulation_halt q t : step M (q, t) = None ->
    TM_step (encode_config (q, t)) = TM_facts.mk_mconfig None (| encode_tape t |).
  Proof.
    rewrite /step /TM_facts.step /=.
    move: t => [[ls a] rs] /=.
    by case: (trans M _) => [[[? ?] d]|] /=.
  Qed.

  Lemma simulation q t k :
    steps M k (q, t) = None ->
    exists q' ts', TM.eval M' (Some q) (| encode_tape t |) q' ts'.
  Proof.
    elim: k q t; first done.
    move=> k IH q t.
    rewrite (steps_plus 1 k). case E: (steps M 1 _) => [[q' t']|].
    - move: E => /simulation_step [t'' [HM' Ht't'']] /IH.
      move=> [q'''] [t'''] /TM_facts.TM_eval_iff [k'].
      rewrite Ht't''. move=> /TM_loopM_canonize_tape => /(_ t'').
      move=> /(_ ltac:(by case: (t''))). move=> [{}t''' ?].
      exists q''', t'''. apply /TM_facts.TM_eval_iff. exists (S k').
      by rewrite /= HM'.
    - move=> _. exists None, (| encode_tape t |).
      apply /TM_facts.TM_eval_iff. exists 1.
      move: E.
      rewrite /= /step /TM_facts.step /=.
      move: t => [[ls a] rs] /=.
      by case: (trans M (q, a)) => [[[??]?]|].
  Qed.

  Lemma inverse_simulation q t q' ts' :
    TM.eval M' (Some q) (| encode_tape t |) q' ts' ->
    exists k, steps M k (q, t) = None.
  Proof.
    move=> /TM_facts.TM_eval_iff => - [k Hk]. exists k.
    elim: k q t q' ts' Hk; first done.
    move=> k IH q t q' ts' Hk. rewrite (steps_plus 1 k).
    case Hqt: (steps M 1 (q, t)) => [[q'' t'']|]; last done.
    move: Hqt => /simulation_step [t'''] [H'qt Et''t'''].
    move: Hk => /=. rewrite H'qt.
    have : canonize_tape t''' = canonize_tape (encode_tape t'').
    { rewrite Et''t'''. by case: (t'''). }
    by move=> /TM_loopM_canonize_tape /[apply] => - [?] /IH.
  Qed.

End Construction.

Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts.

Theorem reduction :
  SBTM2_HALT ⪯ TM.HaltTM 1.
Proof.
  exists ((fun '(existT _ M (q, t)) =>
    existT2 _ _ (finType_CS bool) (M' M q) (| encode_tape t |)) ).
  move=> [M [q t]] /=. split.
  - by move=> [k] /simulation => /(_ q).
  - by move=> [?] [?] /inverse_simulation.
Qed.
