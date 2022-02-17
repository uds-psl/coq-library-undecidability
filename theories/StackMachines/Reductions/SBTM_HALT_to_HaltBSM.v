
From Undecidability.StackMachines Require Import BSM BSM.bsm_defs.
From Undecidability.TM Require Import SBTM Util.SBTM_facts.
From Undecidability.Shared.Libs.DLW Require Import vec subcode sss.

Require Import List Lia.
Import Vector.VectorNotations ListNotations SBTMNotations.
#[local] Open Scope list_scope.

Require Import ssreflect ssrbool ssrfun.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

#[local] Notation "P // s -[ k ]-> t" := (sss_steps (@bsm_sss _) P k s t).
#[local] Notation "P // s ->> t" := (sss_compute (@bsm_sss _) P s t).
#[local] Notation CURR := (@Fin.FS 3 (@Fin.F1 2)).
#[local] Notation LEFT := (@Fin.F1 3).
#[local] Notation RIGHT := (@Fin.FS 3 (@Fin.FS 2 (@Fin.F1 1))).
#[local] Notation ZERO := (@Fin.FS 3 (@Fin.FS 2 (@Fin.FS 1 (@Fin.F1 0)))).

(* induction principle wrt. a decreasing measure f *)
(* example: elim /(measure_ind length) : l. *)
Lemma measure_ind {X : Type} (f : X -> nat) (P : X -> Prop) :
(forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
  exact: (well_founded_ind (Wf_nat.well_founded_lt_compat X f _ (fun _ _ => id)) P).
Qed.

Section Construction.

  Context (M : SBTM) (q0 : state M).

  #[local] Notation δ := (trans' M).

  Definition c := 13.

  #[local] Arguments Vector.cons {A} _ {n}.

  Definition encode_tape (t : tape) : Vector.t (list bool) 4 := 
    match t with
    | (ls, a, rs) => [ ls ; [a]%list ; rs ; []%list ]%vector
    end.

  Definition encode_state (q : state M) := (2 + sval (Fin.to_nat q) * c).

  #[local] Arguments encode_state : simpl never.
  #[local] Notation "! p" := (encode_state p) (at level 1).

  Definition encode_config '(q, t) : bsm_state 4 := (!q, encode_tape t).

  #[local] Notation JMP i := (POP ZERO i i).
  
  Definition box '(q, a) (f : (state M * bool * direction) -> bsm_instr 4) : bsm_instr 4 :=
    match δ (q, a) with
    | None => JMP 0
    | Some t => f t
    end.

  Definition CURR' := CURR. (* to distinguish duplicate operations for subcode_tac *)

  Definition PROG (q : state M) :=
    let off := !q in
  (*      off *) POP CURR (7 + off) (7 + off) ::

  (*  1 + off *) box (q, true) (fun '(q', a', d) => PUSH (match d with go_left => RIGHT | go_right => LEFT end) a') ::
  (*  2 + off *) box (q, true) (fun '(q', a', d) => POP (match d with go_left => LEFT | go_right => RIGHT end) (5+off) (5+off)) ::
  (*  3 + off *) PUSH CURR true ::
  (*  4 + off *) JMP (6 + off) ::
  (*  5 + off *) PUSH CURR false ::
  (*  6 + off *) box (q, true) (fun '(q', a', d) => JMP (!q')) :: 

  (*  7 + off *) box (q, false) (fun '(q', a', d) => PUSH (match d with go_left => RIGHT | go_right => LEFT end) a') ::
  (*  8 + off *) box (q, false) (fun '(q', a', d) => POP (match d with go_left => LEFT | go_right => RIGHT end) (11+off) (11+off)) ::
  (*  9 + off *) PUSH CURR' true ::
  (* 10 + off *) JMP (12 + off) ::
  (* 11 + off *) PUSH CURR' false ::
  (* 12 + off *) box (q, false) (fun '(q', a', d) => JMP (!q')) :: [].

  Lemma PROG_length q : length (PROG q) = c.
  Proof. reflexivity. Qed.

  Opaque c.

  Fixpoint all_fins (n : nat) : list (Fin.t n) :=
    if n is S n' then Fin.F1 :: map Fin.FS (all_fins n') else nil.

  (* constructed BSM *)
  Definition P : list (bsm_instr 4) :=
    JMP (!q0) :: flat_map PROG (all_fins (num_states M)).

  Lemma P_length : length P = 1 + num_states M * c.
  Proof.
    rewrite /P /=. congr S. have := PROG_length.
    elim: (num_states M) (PROG); first done.
    move=> n IH PROG' H. have ->: S n * c = n * c + c by lia.
    rewrite /= app_length flat_map_concat_map map_map -flat_map_concat_map H.
    by rewrite IH; [|lia].
  Qed.

  Definition Q_step (Q : list (bsm_instr 4)) offset i v : option (bsm_state 4) :=
    match nth_error Q i with
    | None => None
    | Some (bsm_pop x p' q') => Some (
        match vec_pos v x with
        | [] => (q', v)
        | false :: l => (p', vec_change v x l)
        | true :: l => ((S i) + offset, vec_change v x l)
        end)
    | Some (bsm_push x b) => Some ((S i) + offset, vec_change v x (b :: vec_pos v x))
    end.

  Arguments Q_step : simpl never.

  Lemma Q_step_spec (Q : list (bsm_instr 4)) offset i v j w : 
    Q_step Q offset i v = Some (j, w) ->
    sss_step (bsm_sss (n:=4)) (offset, Q) (i + offset, v) (j, w).
  Proof.
    rewrite /Q_step. case E: (nth_error Q i) => [t|]; last done.
    move: E => /(@nth_error_split (bsm_instr 4)) => - [l] [r] [-> <-].
    move=> Ht. exists offset, l, t, r, v. split; [|split]; [done|congr pair; lia|].
    move: t Ht => [].
    - move=> x p' q' [<-]. 
      move Ex: (vec_pos v x) => [|[] ?]; by auto using bsm_sss.
    - move=> x b [<-] <-. by auto using bsm_sss.
  Qed.

  Arguments nth_error : simpl never.

  Lemma PROG_spec_Some q t q' t' : step M (q, t) = Some (q', t') ->
    exists k, (!q, PROG q) // (encode_config (q, t)) -[S k]-> (encode_config (q', t')).
  Proof.
    move: t => [[ls a] rs] /=. rewrite /step.
    case E: (δ (q, a)) => [[[??]d]|]; last done.
    move=> [<- <-]. have ->: !q = 0 + !q by done.
    move: d a ls rs E => [] [] [|[] ls] [|[] rs] E.
    all: eexists; rewrite /PROG /box E.
    all: do ? ((by apply: in_sss_steps_0) || (apply: in_sss_steps_S; [by apply: Q_step_spec|])).
  Qed.

  Lemma PROG_spec_None q t : step M (q, t) = None ->
    exists v, (!q, PROG q) // (encode_config (q, t)) ->> (0, v).
  Proof.
    move: t => [[ls a] rs] /=. rewrite /step.
    case E: (δ (q, a)) => [[[??]d]|]; first done.
    move=> _. have ->: !q = 0 + !q by done.
    move: a E => [] E.
    all: exists [ ls ; []%list ; rs ; []%list ]%vector.
    all: eexists; rewrite /PROG /box E.
    all: do ? ((by apply: in_sss_steps_0) || (apply: in_sss_steps_S; [by apply: Q_step_spec|])).
  Qed.

  Lemma PROG_sc (q : state M) : (!q, PROG q) <sc (1, P).
  Proof.
    apply: subcode_cons. rewrite /P /encode_state [1+1]/=.
    suff: forall n, (n + sval (Fin.to_nat q) * c, PROG q) <sc
      (n, flat_map PROG (all_fins (num_states M))) by done.
    have := PROG_length. move: (num_states M) q (PROG) => ?.
    elim. { move=> /= *. by eexists [], _. }
    move=> m q IH PROG' H' n.
    have := IH (fun q => PROG' (Fin.FS q)) => /(_ ltac:(done) (n+c)).
    rewrite /= !flat_map_concat_map map_map -!flat_map_concat_map.
    move=> [l] [r] [{}IH {}IH']. exists (PROG' Fin.F1 ++ l), r. split.
    - by rewrite IH -app_assoc.
    - move: (Fin.to_nat q) IH' => [? ?] /=. rewrite app_length H'. lia.
  Qed.

  Opaque P.

  Lemma simulation_step_Some q t q' t' : step M (q, t) = Some (q', t') ->
    exists k, (1, P) // (encode_config (q, t)) -[S k]-> (encode_config (q', t')).
  Proof.
    move=> /PROG_spec_Some [k] H. exists k.
    apply: subcode_sss_steps; [|by eassumption].
    by apply: PROG_sc.
  Qed.

  Lemma simulation_step_None q t : step M (q, t) = None ->
    exists v, (1, P) // (encode_config (q, t)) ->> (0, v).
  Proof.
    move=> /PROG_spec_None [v Hv]. exists v.
    by apply: subcode_sss_compute; [apply: PROG_sc|].
  Qed.

  Lemma simulation q t k :
    steps M k (q, t) = None ->
    exists v, (1, P) // (encode_config (q, t)) ->> (0, v).
  Proof.
    elim: k q t; first done.
    move=> k IH q t. rewrite (steps_plus 1) /=.
    case E: (step M (q, t)) => [[q' t']|].
    - move=> /IH [v] Hv. exists v.
      move: E => /simulation_step_Some [?] /sss_steps_compute /sss_compute_trans.
      by apply.
    - by move: E => /simulation_step_None.
  Qed.

  Lemma inverse_simulation q t n i v :
    (1, P) // (encode_config (q, t)) -[n]-> (i, v) ->
    out_code i (1, P) ->
    exists k, steps M k (q, t) = None.
  Proof.
    elim /(@measure_ind nat id) : n q t => - [|n] IH q t.
    { move=> /sss_steps_0_inv [] /= <- _.
      rewrite /encode_state P_length (ltac:(done) : c = (S (c-1))).
      have := svalP (Fin.to_nat q). nia. }
    case E: (step M (q, t)) => [[q' t']|]; last by (move=> _; exists 1).
    move: (E) => /simulation_step_Some [m].
    move=> Hn Hm Hi. have := (IH (n - m) ltac:(lia) q' t' _ Hi).
    case.
    { move: Hn Hm Hi => /subcode_sss_subcode_inv /[apply] /[apply].
      case.
      - by exact: bsm_sss_fun.
      - by apply: subcode_refl.
      - move=> n' [?]. by have ->: n' = n - m by lia. }
    move=> k Hk. exists (1+k). by rewrite (steps_plus 1) /= E.
  Qed.

End Construction.

Require Import Undecidability.Synthetic.Definitions.

Theorem reduction :
  SBTM_HALT ⪯ BSM_HALTING.
Proof.
  exists (fun '(existT _ M (q, t)) =>
    existT _ 4 (existT _ 1 (existT _ (@P M q) (encode_tape t)))).
  move=> [M [q [[ls a] rs]]]. split.
  - move=> [k] /simulation => /(_ q) [v Hv] /=.
    exists (0, v). split => /=; [|lia].
    rewrite /P.
    bsm sss POP empty with ZERO (encode_state M q) (encode_state M q).
  - move=> [] [i v] [] [?] H /= ?.
    rewrite /P in H.
    bsm inv POP empty with H ZERO (encode_state M q) (encode_state M q).
    + move: H => [?] [?] /inverse_simulation. by apply.
    + move=> []. lia.
Qed.
