From Undecidability Require StringRewriting.SR.
From Undecidability Require StringRewriting.Util.Definitions.
Module SR_facts := StringRewriting.Util.Definitions.
From Undecidability Require Import TM.SBTM TM.Util.SBTM_facts.
From Undecidability Require Import StringRewriting.Reductions.SBTM_HALT_to_SR.

From Stdlib Require Import PeanoNat Lia.

From Stdlib Require Import List ssreflect ssrbool ssrfun.
Import ListNotations SBTMNotations.

Set Default Goal Selector "!".

Section Construction.
  (* input SBTM *)
  Context (M : SBTM).

  #[local] Notation "⦇" := 0.
  #[local] Notation "⦈" := 1.
  #[local] Notation "# a" := (encode_symbol a) (at level 1).
  #[local] Notation encode_state q := (encode_state M q).
  #[local] Notation encode_config q t := (encode_config M q t).
  #[local] Notation encode_rule qa := (encode_rule M qa).

  #[local] Notation srs := (srs M).

  Lemma simulation q t k :
    steps M k (q, t) = None ->
    SR.rewt (srs ++ map SR.swap srs) (encode_config q t) [⦈; ⦇].
  Proof.
    elim: k q t; first done.
    move=> k IH q t.
    rewrite (steps_plus 1 k). case E: (steps M 1 _) => [[q' t']|].
    - move: E => /simulation_step ?.
      move=> /IH. apply: SR.rewS. apply /SR_facts.rew_app_inv.
      by left.
    - move: E => /simulation_halt /SR_facts.rewt_subset + _. apply.
      apply: incl_appl. by apply: incl_refl.
  Qed.

  Lemma rew_swap {X} {R : SR.SRS X} {x y} : SR.rew (map SR.swap R) x y -> SR.rew R y x.
  Proof.
    move ER': (map _ _) => R' H.
    case: H ER' => > + ?. subst R'.
    by move=> /in_map_iff [[??]] [[]] <- <- /SR.rewB.
  Qed.

  Lemma app_left_marker u ls : u ++ [⦇] = ⦇ :: rev (map encode_symbol ls) -> u = [] /\ ls = [].
  Proof.
    move: u ls => [|c u] [|l ls].
    - done.
    - by move=> /(@app_inj_tail nat _ (_ :: _)) [].
    - by case: u.
    - move=> /(@app_inj_tail nat _ (_ :: _)) []. by case: l.
  Qed.

  Lemma left_marker_nth q t n : not (nth_error (encode_config q t) (S n) = Some ⦇).
  Proof.
    move: t => [[ls a] rs] /=. elim /rev_ind: ls n.
    - move=> [|[|n]] /=; [by case: a|done|].
      elim: rs n. { by move=> [|[|?]]. }
      move=> r rs IH [|n]; first by case: r.
      by apply: IH.
    - move=> l ls IH [|n]; rewrite map_app rev_app_distr; first by case: l.
      by apply: IH.
  Qed.

  Lemma inverse_simulation_back_step q t x q' t' :
    SR.rew (map SR.swap srs) (encode_config q t) x ->
    step M (q, t) = Some (q', t') ->
    exists q'' t'', x = encode_config q'' t'' /\ step M (q'', t'') = Some (q, t).
  Proof.
    have reassoc (n m : nat) (u v : list nat) : u ++ (n :: m :: v) = (u ++ [n]) ++ m :: v.
    { by rewrite -app_assoc. }
    move=> /rew_swap. move Ey: (encode_config q t) => y Hxy.
    case: Hxy Ey => u v > /In_srsI [].
    - move=> > _ H. exfalso. apply: (left_marker_nth q t (length u)).
      rewrite H. rewrite nth_error_app2; first by lia.
      by have ->: S (length u) - length u = 1 by lia.
    - move: t => [[??]?] > E b /encode_config_eq_app [->] [->] [-> ->].
      by rewrite /step E.
    - move: t => [[??]?] > E b /encode_config_eq_app [->] [->] [-> ->].
      by rewrite /step E.
    - move: t => [[ls ?] rs] q'' a ? a' E H _. move: H E. rewrite !(reassoc ⦇).
      move=> /encode_config_eq_app [->] [->] [/app_left_marker] [-> ->].
      move: rs => [|r rs]. { by case: a'. }
      move=> [] /encode_symbol_inj -> -> E.
      exists q'', ([], a, rs). split; first done.
      by rewrite /step E.
    - move: t => [[ls ?] rs] q'' a ? a' E b H _. move: H E.
      move=> /encode_config_eq_app [->] [->] [->].
      move: rs => [|r rs]. { by case: a'. }
      move=> [] /encode_symbol_inj -> -> E.
      exists q'', (b :: ls, a, rs). split; first by rewrite /= -!app_assoc.
      by rewrite /step E.
    - move: t => [[ls ?] rs] q'' a ? a' E H _. move: H E. rewrite !(reassoc #a').
      move=> /encode_config_eq_app [->] [->] [].
      move: ls => [|l ls]. { move=> /(@app_inj_tail nat _ []) []. by case: a'. }
      move=> /= /(@app_inj_tail nat _ (_ :: _)) [-> /encode_symbol_inj ->].
      move: rs => [|r rs]; last by case: r.
      move=> [->] E.
      exists q'', (ls, a, []). split; first done.
      by rewrite /step E.
    - move: t => [[ls ?] rs] q'' a ? a' E b H _. move: H E. rewrite !(reassoc #a').
      move=> /encode_config_eq_app [->] [->] [+ ->].
      move: ls => [|l ls]. { move=> /(@app_inj_tail nat _ []) []. by case: a'. } cbn.
      move=> /(@app_inj_tail nat _ (_ :: _)) [-> /encode_symbol_inj ->] E.
      exists q'', (ls, a, b :: rs). split; first done.
      by rewrite /step E.
  Qed.

  Lemma inverse_simulation q t :
    SR.rewt (srs ++ map SR.swap srs) (encode_config q t) [⦈; ⦇] ->
    exists k, steps M k (q, t) = None.
  Proof.
    move Eu: (encode_config q t) => u.
    move Ev: ([⦈; ⦇]) => v Huv.
    elim: Huv q t Eu Ev. { by move=> ?? [[??]?] <-. }
    move=> x y z + _ + q t ??. subst x z.
    case E: (step M (q, t)) => [[q' t']|]; first last.
    { move=> *. by exists 1. }
    move=> /SR_facts.rew_app_inv [].
    { move: (E) => /inverse_simulation_step /[apply] ->.
      move=> /(_ _ _ erefl erefl) [k Hk].
      exists (1+k). by rewrite steps_plus /= E. }
    move: (E) => /inverse_simulation_back_step /[apply] [[q'']] [t''] [-> H''].
    move=> /(_ _ _ erefl erefl) [[|k] Hk]; first done.
    exists k. move: Hk. by rewrite (steps_plus 1 k) /= H''.
  Qed.

End Construction.

Require Import Undecidability.Synthetic.Definitions.

Theorem reduction :
  SBTM_HALT ⪯ SR.TSR.
Proof.
  exists ((fun '(existT _ M (q, t)) => (srs M, encode_config M q t, [1; 0]))).
  move=> [M [q t]] /=. split.
  - by move=> [?] /simulation.
  - by move=> /inverse_simulation.
Qed.
