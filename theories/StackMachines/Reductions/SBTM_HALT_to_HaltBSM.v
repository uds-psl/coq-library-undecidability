
From Undecidability.StackMachines Require Import BSM BSM.bsm_defs.
From Undecidability.TM Require Import SBTM Util.SBTM_facts.
From Undecidability.Shared.Libs.DLW Require Import vec subcode sss.

From Stdlib Require Import PeanoNat List Lia.
Import Vector.VectorNotations ListNotations SBTMNotations.
#[local] Open Scope list_scope.

From Stdlib Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

#[local] Notation "P // s -[ k ]-> t" := (sss_steps (@bsm_sss _) P k s t).
#[local] Notation "P // s ->> t" := (sss_compute (@bsm_sss _) P s t).
#[local] Notation CURR := (@Fin.FS 3 (@Fin.F1 2)).
#[local] Notation LEFT := (@Fin.F1 3).
#[local] Notation RIGHT := (@Fin.FS 3 (@Fin.FS 2 (@Fin.F1 1))).
#[local] Notation ZERO := (@Fin.FS 3 (@Fin.FS 2 (@Fin.FS 1 (@Fin.F1 0)))).

Section Construction.

  (* Shift by shift to the right*)
  Context (M : SBTM) (q0 : state M) (shift : nat).

  #[local] Notation δ := (trans' M).

  Definition c := 13.

  #[local] Arguments Vector.cons {A} _ {n}.

  Definition encode_tape (t : tape) : Vector.t (list bool) 4 := 
    match t with
    | (ls, a, rs) => [ ls ; [a]%list ; rs ; []%list ]%vector
    end.

  (* Shift everything back by one *)
  Definition encode_state (q : state M) := (1 + shift + sval (Fin.to_nat q) * c).

  #[local] Arguments encode_state : simpl never.
  #[local] Notation "! p" := (encode_state p) (at level 1).

  Definition encode_config '(q, t) : bsm_state 4 := (!q, encode_tape t).

  #[local] Notation JMP i := (POP ZERO i i).

  (* Jump to after Program *)
  Notation POST_TRUE := (1 + shift + c * (num_states M)).
  Notation POST_FALSE := (3 + shift + c * (num_states M)).
  Notation END := (5 + shift + c * (num_states M)).

  Definition box '(q, a) (f : (state M * bool * direction) -> bsm_instr 4) : bsm_instr 4 :=
    match δ (q, a) with
    | None => JMP (if a then POST_TRUE else POST_FALSE)
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

  Lemma c_spec : c = 13.
  Proof. easy. Qed.

  Fixpoint all_fins (n : nat) : list (Fin.t n) :=
    if n is S n' then Fin.F1 :: map Fin.FS (all_fins n') else nil.

  Definition POST : list (bsm_instr 4) :=
    PUSH CURR' true ::
    JMP END ::
    PUSH CURR' false :: 
    JMP END :: [].

  (* constructed BSM *)
  Definition P : list (bsm_instr 4) :=
    JMP (!q0) :: flat_map PROG (all_fins (num_states M)) ++ POST.

  Lemma length_flat_map_PROG_M : length (flat_map PROG (all_fins (num_states M))) = num_states M * c.
  Proof.
    have := PROG_length.
    elim: (num_states M) (PROG); first done.
    move=> n IH PROG' H. have ->: S n * c = n * c + c by lia.
    rewrite /= length_app flat_map_concat_map map_map -flat_map_concat_map H.
    by rewrite IH; [|lia].
  Qed.

  Lemma state_map_length_spec M1 : length (all_fins (num_states M1)) = num_states M1.
  Proof.
    induction (num_states M1) as [| n IHn];[reflexivity|].
    cbn. 
    rewrite length_map.
    now rewrite IHn.
  Qed.

  Lemma state_number_length M1 (q1 : SBTMNotations.state M1) :
    proj1_sig (Fin.to_nat q1) < length (all_fins (num_states M1)).
  Proof.
    unfold proj1_sig.
    destruct (Fin.to_nat q1) as [n H].
    rewrite state_map_length_spec.
    apply H.
  Qed.

  Lemma P_length : length P = 5 + num_states M * c.
  Proof.
    rewrite /= length_app /= length_flat_map_PROG_M. lia.
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

  Lemma PROG_spec_None a q ls rs : step M (q, (ls, a, rs)) = None ->
    (!q, PROG q) // (encode_config (q, (ls, a, rs))) ->> (if a then POST_TRUE else POST_FALSE, [ls; []%list; rs; []%list]%vector).
  Proof.
    rewrite /step.
    case E: (δ (q, a)) => [[[??]?]|]; first done.
    move=> _.
    rewrite /PROG. eexists _.
    apply in_sss_steps_S with (st2:= (if a then 1 +! q else 7 +! q, [ls; []%list; rs; []%list]%vector)).
    { eexists _, [], _, _, _.
      split; [reflexivity|split; [by rewrite (Nat.add_comm (!q))|]].
      replace ([ls; []%list; rs; []%list]%vector) with (vec_change ([ls; [a]%list; rs; []%list]%vector) CURR' []) by done.
      destruct a; by constructor. }
    apply in_sss_steps_S with (st2:= (if a then POST_TRUE else POST_FALSE, [ls; []%list; rs; []%list]%vector)).
    { destruct a.
      - eexists _, [_], _, _, _.
        split; [reflexivity|split; [by rewrite (Nat.add_comm (!q))|]].
        rewrite /= E. by constructor.
      - eexists _, [_; _; _; _; _; _; _], _, _, _.
        split; [reflexivity|split; [by rewrite (Nat.add_comm (!q))|]].
        rewrite /= E; by constructor. }
    by apply: in_sss_steps_0.
  Qed.

  Lemma PROG_sc (q : state M) : (!q, PROG q) <sc (shift, P).
  Proof.
    apply: subcode_cons.
    apply: subcode_app_end.
    suff: forall n, (n + shift + sval (Fin.to_nat q) * c, PROG q) <sc
      (n + shift, flat_map PROG (all_fins (num_states M))) by apply.
    move: (num_states M) q (PROG) (PROG_length)=> ?.
    elim; first by eexists [], _.
    move=> m q IH PROG' H' n. apply: subcode_trans.
    - have := (IH (fun q => PROG' (Fin.FS q)) (fun q => H' (Fin.FS q)) (n+c)).
      congr subcode. congr pair.
      rewrite /=. move: (Fin.to_nat q) => [] /=. lia.
    - rewrite /= !flat_map_concat_map map_map -!flat_map_concat_map.
      exists (PROG' Fin.F1), []. rewrite app_nil_r H'.
      by split; [|lia].
  Qed.

  Lemma POST_spec a ls rs:
    (POST_TRUE, POST) // (if a then POST_TRUE else POST_FALSE, [ls; []%list; rs; []%list]%vector) ->> (END, encode_tape (ls, a, rs)).
  Proof.
    exists 2.
    apply in_sss_steps_S with (st2:= (1 + if a then POST_TRUE else POST_FALSE, [ls; [a]%list; rs; []%list]%vector)).
    { case: a.
      - eexists _, [], _, _, _.
        split; [reflexivity|split;[by rewrite (Nat.add_comm _ (length _))|]].
        by constructor.
      - eexists _, [_; _], _, _, _.
        split; [reflexivity|split;[by rewrite (Nat.add_comm _ (length _))|]].
        by constructor. }
    apply in_sss_steps_S with (st2:= (END, [ls; [a]%list; rs; []%list]%vector)).
    { case: a.
      - eexists _, [_], _, _, _.
        split; [reflexivity|split;[by rewrite (Nat.add_comm _ (length _))|]].
        by constructor.
      - eexists _, [_; _; _], _, _, _.
        split; [reflexivity|split;[by rewrite (Nat.add_comm _ (length _))|]].
        by constructor. }
    by apply in_sss_steps_0.
  Qed.

  Lemma POST_sc : (POST_TRUE, POST) <sc (shift, P).
  Proof.
    eexists (_ :: _), [].
    rewrite app_nil_r /=.
    split; first done.
    rewrite length_flat_map_PROG_M. lia.
  Qed.

  (* Opaque P. *)

  Lemma simulation_step_Some q t q' t' : step M (q, t) = Some (q', t') ->
    exists k, (shift, P) // (encode_config (q, t)) -[S k]-> (encode_config (q', t')).
  Proof.
    move=> /PROG_spec_Some [k] H. exists k.
    apply: subcode_sss_steps; [|by eassumption].
    by apply: PROG_sc.
  Qed.

  Lemma simulation_step_None q t : step M (q, t) = None ->
    (shift, P) // (encode_config (q, t)) ->> (shift + length P, encode_tape t).
  Proof.
    move: t => [[ls a] rs] /PROG_spec_None.
    have /subcode_sss_compute := PROG_sc q.
    move=> /[apply] /sss_compute_trans. apply.
    apply: subcode_sss_compute; first by apply POST_sc.
    have ->: shift + length P = END.
    { rewrite P_length. cbn. lia. }
    by apply: POST_spec.
  Qed.

  Lemma simulation_output q q' t t' k :
    steps M k (q, t) = Some (q', t') ->
    (shift, P) // (encode_config (q, t)) ->> (encode_config (q', t')).
  Proof.
    elim: k q t.
    - move=> ?? [-> ->].
      exists 0.
      by constructor.
    - move=> k IH q t. rewrite (steps_plus 1) /=.
      case E: (step M (q, t)) => [[q'' t'']|].
      + move=> /IH [v] Hv.
        move: E => /simulation_step_Some [k' Hk'].
        exists ((S k') + v).
        apply: sss_steps_trans; by eassumption.
      + by move: E => /simulation_step_None.
  Qed.

  Lemma simulation_output'' q q' t t' k :
    steps M k (q, t) = Some (q', t') ->
    steps M (S k) (q, t) = None ->
    (shift, P) // (encode_config (q, t)) ->> (shift + length P, encode_tape t').
  Proof.
    have ->: S k = k + 1 by lia.
    rewrite (steps_plus).
    move=> /[dup] /simulation_output /sss_compute_trans + -> /= H. apply.
    by apply: simulation_step_None.
  Qed.

  Lemma simulation q t k :
    steps M k (q, t) = None ->
    exists v, (shift, P) // (encode_config (q, t)) ->> (shift + length P, v).
  Proof.
    elim: k q t; first done.
    move=> k IH q t /[dup] HSk.
    have ->: S k = k + 1 by lia.
    rewrite steps_plus.
    case E: (steps M k (q, t)) => [[q' t']|].
    - move: E HSk => /simulation_output'' /[apply] ??.
      eexists. by eassumption.
    - move=> ?. by apply: IH.
  Qed.

  Lemma sss_step_shift t : sss_step (bsm_sss (n:=4)) (shift, P) (shift, encode_tape t) (encode_config (q0, t)).
  Proof.
    eexists _, [], _, _, _.
    split; [reflexivity|split; [by rewrite Nat.add_comm|]].
    move: (t) => [[??]?].
    by constructor.
  Qed.

  Lemma simulation_output' q' t t' k :
    steps M k (q0, t) = Some (q', t') ->
    steps M (S k) (q0, t) = None ->
    (shift, P) // (shift, encode_tape t) ->> (shift + length P, encode_tape t').
  Proof.
    move=> /simulation_output'' /[apply] ?.
    apply: sss_compute_trans; last by eassumption. 
    exists 1.
    apply: in_sss_steps_S; last by apply: in_sss_steps_0.
    by apply: sss_step_shift.
  Qed.

  Lemma simulation' t k :
    steps M k (q0, t) = None ->
    exists v, (shift, P) // (shift, encode_tape t) ->> (shift + length P, v).
  Proof.
    elim: k; first done.
    move=> k IH /[dup] HSk.
    have ->: S k = k + 1 by lia.
    rewrite steps_plus.
    case E: (steps M k (q0, t)) => [[??]|].
    - move: E HSk => /simulation_output' /[apply] *.
      eexists. by eassumption.
    - move=> ?. by apply: IH.
  Qed.

  Lemma inverse_simulation q t n i v :
    (shift, P) // (encode_config (q, t)) -[n]-> (shift + i, v) ->
    out_code (shift + i) (shift, P) ->
    exists k, steps M k (q, t) = None.
  Proof.
    elim /(Nat.measure_induction _ id) : n q t => - [|n] IH q t.
    { move=> /sss_steps_0_inv [] /= <- _ [|].
      - rewrite /encode_state. lia.
      - rewrite /encode_state length_app length_flat_map_PROG_M.
        destruct (Fin.to_nat q).
        cbn. nia. }
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

  Lemma inverse_simulation' t i v :
    sss_output (bsm_sss (n := 4)) (shift, P)  (shift, encode_tape t) (shift + i, v) ->
    exists k, steps M k (q0, t) = None.
  Proof.
    intros H.
    destruct H as [[n H1] H2].
    revert H1 H2.
    case n.
    - move=> /sss_steps_0_inv [] <- _ /=. lia.
    - move=> n' /sss_steps_S_inv' [[q' t']] [].
      have := @bsm_sss_fun 4.
      have := sss_step_shift t.
      move=> /sss_step_fun /[apply] /[apply] <-.
      by apply: inverse_simulation.
  Qed.

End Construction.

Require Import Undecidability.Synthetic.Definitions.

Theorem reduction :
  SBTM_HALT ⪯ BSM_HALTING.
Proof.
  exists (fun '(existT _ M (q, t)) =>
    existT _ 4 (existT _ 0 (existT _ (@P M q 0) (encode_tape t)))).
  move=> [M [q [[ls a] rs]]]. split.
  - move=> [k] /simulation => /(_ q 0) [v Hv] /=.
    exists ((5 + (num_states M) * c), v). split => /=.
    + rewrite /P.
      rewrite P_length in Hv.
      bsm sss POP empty with ZERO (encode_state M 0 q ) (encode_state M 0 q).
    + right.
      rewrite length_app length_flat_map_PROG_M /=. lia.
  - move=> [] [i v] [] [?] H /= ?.
    rewrite /P in H.
    bsm inv POP empty with H ZERO (encode_state M 0 q) (encode_state M 0 q).
    + move: H => [?] [?] /inverse_simulation. by apply.
    + move=> []. lia.
Qed.
