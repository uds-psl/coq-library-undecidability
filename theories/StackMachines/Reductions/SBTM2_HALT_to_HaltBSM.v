
From Undecidability.StackMachines Require Import BSM BSM.bsm_defs.
From Undecidability.TM Require Import SBTM2 Util.SBTM2_facts.
From Undecidability.Shared.Libs.DLW Require Import subcode sss.

Require Import List Lia.
Import Vector.VectorNotations ListNotations SBTM2Notations.
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

(* transforms a goal (A -> B) -> C into goals A and B -> C *)
Lemma unnest : forall (A B C : Type), A -> (B -> C) -> (A -> B) -> C.
Proof. auto. Qed.

(* induction principle wrt. a decreasing measure f *)
(* example: elim /(measure_ind length) : l. *)
Lemma measure_ind {X : Type} (f : X -> nat) (P : X -> Prop) :
(forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
  exact: (well_founded_ind (Wf_nat.well_founded_lt_compat X f _ (fun _ _ => id)) P).
Qed.

Section Construction.

  Context (M : SBTM2) (q0 : state M).

  #[local] Notation δ := (trans' M).

  Definition c := 13.

  #[local] Arguments Vector.cons {A} _ {n}.

  Definition encode_tape (t : tape) : Vector.t (list bool) 4 := 
    match t with
    | (ls, a, rs) => [ ls ; [a]%list ; rs ; []%list ]%vector
    end.

  Definition encode_state (q : state M) := (sval (Fin.to_nat q) * c + 2).

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

  Lemma subcode_cons' {X : Type} i j x (l1 l2 : list X) :
    (i, l1) <sc (j, l2) -> (S i, l1) <sc (j, x :: l2).
  Proof.
    move=> [l] [r] [-> ->]. apply: subcode_cons. exists l, r.
    by split; [|lia].
  Qed.

  (*
  #[local] Hint Resolve subcode_cons' : core.
*)
  Lemma PROG_spec_Some q t q' t' : step M (q, t) = Some (q', t') ->
    (!q, PROG q) // (encode_config (q, t)) ->> (encode_config (q', t')).
  Proof.
    move: t => [[ls []] rs]; rewrite /step /encode_config /PROG /box.
    - set off := !q.
      case: (δ (q, true)) => [[[q'' a''] d]|]; last done.
      move: d => [] [-> <-].
      + bsm sss POP one with CURR (7 + off) (7 + off) (@nil bool).
        bsm sss PUSH with RIGHT a''.
        case: ls => [|[] ls].
        * bsm sss POP empty with LEFT (5 + off) (5 + off).
          bsm sss PUSH with CURR false.
          bsm sss POP empty with ZERO !q' !q'.
          exists 0. by apply: in_sss_steps_0.
        * bsm sss POP one with LEFT (5 + off) (5 + off) ls.
          bsm sss PUSH with CURR true.
          bsm sss POP empty with ZERO (6 + off) (6 + off).
          bsm sss POP empty with ZERO !q' !q'.
          exists 0. by apply: in_sss_steps_0.
        * bsm sss POP zero with LEFT (5 + off) (5 + off) ls.
          bsm sss PUSH with CURR false.
          bsm sss POP empty with ZERO !q' !q'.
          exists 0. by apply: in_sss_steps_0.
      + bsm sss POP one with CURR (7 + off) (7 + off) (@nil bool).
        bsm sss PUSH with LEFT a''.
        case: rs => [|[] rs].
        * bsm sss POP empty with RIGHT (5 + off) (5 + off).
          bsm sss PUSH with CURR false.
          bsm sss POP empty with ZERO !q' !q'.
          exists 0. by apply: in_sss_steps_0.
        * bsm sss POP one with RIGHT (5 + off) (5 + off) rs.
          bsm sss PUSH with CURR true.
          bsm sss POP empty with ZERO (6 + off) (6 + off).
          bsm sss POP empty with ZERO !q' !q'.
          exists 0. by apply: in_sss_steps_0.
        * bsm sss POP zero with RIGHT (5 + off) (5 + off) rs.
          bsm sss PUSH with CURR false.
          bsm sss POP empty with ZERO !q' !q'.
          exists 0. by apply: in_sss_steps_0.
    - set off := !q.
      case: (δ (q, false)) => [[[q'' a''] d]|]; last done.
      move: d => [] [-> <-].
      + bsm sss POP zero with CURR (7 + off) (7 + off) (@nil bool).
        bsm sss PUSH with RIGHT a''.
        case: ls => [|[] ls].
        * bsm sss POP empty with LEFT (11 + off) (11 + off).
          bsm sss PUSH with CURR' false.
          bsm sss POP empty with ZERO !q' !q'.
          exists 0. by apply: in_sss_steps_0.
        * bsm sss POP one with LEFT (11 + off) (11 + off) ls.
          bsm sss PUSH with CURR' true.
          bsm sss POP empty with ZERO (12 + off) (12 + off).
          bsm sss POP empty with ZERO !q' !q'.
          exists 0. by apply: in_sss_steps_0.
        * bsm sss POP zero with LEFT (11 + off) (11 + off) ls.
          bsm sss PUSH with CURR' false.
          bsm sss POP empty with ZERO !q' !q'.
          exists 0. by apply: in_sss_steps_0.
      + bsm sss POP zero with CURR (7 + off) (7 + off) (@nil bool).
        bsm sss PUSH with LEFT a''.
        case: rs => [|[] rs].
        * bsm sss POP empty with RIGHT (11 + off) (11 + off).
          bsm sss PUSH with CURR' false.
          bsm sss POP empty with ZERO !q' !q'.
          exists 0. by apply: in_sss_steps_0.
        * bsm sss POP one with RIGHT (11 + off) (11 + off) rs.
          bsm sss PUSH with CURR' true.
          bsm sss POP empty with ZERO (12 + off) (12 + off).
          bsm sss POP empty with ZERO !q' !q'.
          exists 0. by apply: in_sss_steps_0.
        * bsm sss POP zero with RIGHT (11 + off) (11 + off) rs.
          bsm sss PUSH with CURR' false.
          bsm sss POP empty with ZERO !q' !q'.
          exists 0. by apply: in_sss_steps_0.
  Qed.

  Lemma PROG_spec_None q t : step M (q, t) = None ->
    exists v, (!q, PROG q) // (encode_config (q, t)) ->> (0, v).
  Proof.
    move: t => [[ls []] rs]; rewrite /step /encode_config /PROG /box.
    - set off := !q.
      case: (δ (q, true)) => [[[q'' a''] d]|]; first done.
      move=> _. exists [ ls ; []%list ; rs ; []%list ]%vector.
      bsm sss POP one with CURR (7 + off) (7 + off) (@nil bool).
      bsm sss POP empty with ZERO (0) (0).
      exists 0. by apply: in_sss_steps_0.
    - set off := !q.
      case: (δ (q, false)) => [[[q'' a''] d]|]; first done.
      move=> _. exists [ls ; []%list ; rs ; []%list ]%vector.
      bsm sss POP zero with CURR (7 + off) (7 + off) (@nil bool).
      bsm sss POP empty with ZERO (0) (0).
      exists 0. by apply: in_sss_steps_0.
  Qed.

  Lemma PROG_sc (q : state M) : (!q, PROG q) <sc (1, P).
  Proof.
    apply: subcode_cons. rewrite /P /encode_state [1+1]/=.
    suff: forall n, (sval (Fin.to_nat q) * c + n, PROG q) <sc
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
    (1, P) // (encode_config (q, t)) ->> (encode_config (q', t')).
  Proof.
    move=> /PROG_spec_Some. apply: subcode_sss_compute. by apply: PROG_sc.
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
      move: E => /simulation_step_Some.
      move=> /sss_compute_trans. by apply.
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
    move: (E) => /simulation_step_Some [[|m]].
    { move=> /sss_steps_0_inv [_ H]. exfalso.
      move: t E H {IH} => [[ls a] rs]. rewrite /step.
      case: (δ (q, a)) => [[[??]d]|]; last done.
      move=> /= [_ <-].
      have ? : forall (a : bool) l, l <> a :: l. { move=> > /(f_equal (@length bool)) /=. lia. } 
      move: d ls rs => [] [|??] [|??] [] //=; congruence. }
    move=> Hn Hm Hi. have := (IH (n - m) ltac:(lia) q' t' _ Hi).
    apply: unnest. 
    { move: Hn Hm Hi.
      move=> /subcode_sss_subcode_inv /[apply] /[apply].
      apply: unnest. { by exact: bsm_sss_fun. }
      apply: unnest. { by apply: subcode_refl. }
      move=> [n'] [?]. by have ->: n' = n - m by lia. }
    move=> [k Hk]. exists (1+k). by rewrite (steps_plus 1) /= E.
  Qed.

End Construction.

Require Import Undecidability.Synthetic.Definitions.

Theorem SBTM_to_BSM :
  SBTM2_HALT ⪯ BSM_HALTING.
Proof.
  exists (fun '(existT _ M (q, t)) => 
      existT _ 4 (existT _ 1 (existT _ (@P M q) (encode_tape t)))).
  move=> [M [q [[ls a] rs]]]. split.
  - move=> [k] /simulation => /(_ q) [v Hv] /=.
    exists (0, v). split => /=; [|lia]. 
    rewrite /P.
    bsm sss POP empty with ZERO (encode_state M q) (encode_state M q).
  - move=> [] [i v] [] [?] H /= ?.
    move: H => /bsm_steps_POP_E_inv => /(_ ZERO (encode_state M q) (encode_state M q)) [].
    + by eexists [], _.
    + reflexivity.
    + move=> []. lia.
    + move=> ? [?] /inverse_simulation. by apply.
Qed.
