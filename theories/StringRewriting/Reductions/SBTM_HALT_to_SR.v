From Undecidability Require StringRewriting.SR.
From Undecidability Require Import TM.SBTM TM.Util.SBTM_facts.

From Stdlib Require Import PeanoNat Lia.

From Stdlib Require Import List ssreflect ssrbool ssrfun.
Import ListNotations SBTMNotations.

Set Default Goal Selector "!".

Section Construction.
  (* input SBTM *)
  Context (M : SBTM).
  #[local] Notation "⦇" := 0.
  #[local] Notation "⦈" := 1.
  Definition encode_symbol (a: bool) := if a then 2 else 3.
  #[local] Notation "# a" := (encode_symbol a) (at level 1).

  Definition encode_state (q: state M) := 4 + proj1_sig (Fin.to_nat q).

  Arguments encode_state : simpl never.

  Definition encode_config (q : state M) (t : tape) : SR.string nat :=
    match t with
    | (ls, a, rs) =>
        ⦇ :: (rev (map encode_symbol ls)) ++ [encode_symbol a] ++ [encode_state q] ++ (map encode_symbol rs) ++ [⦈]
    end.

  Fixpoint all_fins (n : nat) : list (Fin.t n) :=
    match n with
    | 0 => nil
    | S n => Fin.F1 :: map Fin.FS (all_fins n)
    end.

  Lemma all_fins_spec {n} i : In i (all_fins n).
  Proof. by elim: i => >; [left|right; apply: in_map]. Qed.
  
  Definition encode_rule '(q, a) :=
    match trans' M (q, a) with
    | None => [
      ([⦇; #a; encode_state q; ⦈], [⦈; ⦇]);
      ([#true; #a; encode_state q], [#a; encode_state q]);
      ([#false; #a; encode_state q], [#a; encode_state q]);
      ([#a; encode_state q; #true], [#a; encode_state q]);
      ([#a; encode_state q; #false], [#a; encode_state q])]
    | Some (q', a', go_left) => [
        ([⦇; #a; encode_state q], [⦇; #false; encode_state q'; #a']);
        ([#true; #a; encode_state q], [#true; encode_state q'; #a']);
        ([#false; #a; encode_state q], [#false; encode_state q'; #a'])]
    | Some (q', a', go_right) => [
        ([#a; encode_state q; ⦈], [#a'; #false; encode_state q'; ⦈]);
        ([#a; encode_state q; #true], [#a'; #true; encode_state q']);
        ([#a; encode_state q; #false], [#a'; #false; encode_state q'])]
    end.

  Definition srs : SR.SRS nat :=
    flat_map encode_rule (list_prod (all_fins (num_states M)) ([true; false])).

  Inductive In_srs : SR.string nat -> SR.string nat -> Prop :=
    | In_srs_f {q a} : trans' M (q, a) = None ->
        In_srs [⦇; #a; encode_state q; ⦈] [⦈; ⦇]
    | In_srs_dl {q a} : trans' M (q, a) = None ->
        forall b, In_srs [#b; #a; encode_state q] [#a; encode_state q]
    | In_srs_dr {q a} : trans' M (q, a) = None ->
        forall b, In_srs [#a; encode_state q; #b] [#a; encode_state q]
    | In_srs_l1 {q a q' a'} : trans' M (q, a) = Some (q', a', go_left) ->
        In_srs [⦇; #a; encode_state q] [⦇; #false; encode_state q'; #a']
    | In_srs_l2 {q a q' a'} : trans' M (q, a) = Some (q', a', go_left) ->
        forall b, In_srs [#b; #a; encode_state q] [#b; encode_state q'; #a']
    | In_srs_r1 {q a q' a'} : trans' M (q, a) = Some (q', a', go_right) ->
        In_srs [#a; encode_state q; ⦈] [#a'; #false; encode_state q'; ⦈]
    | In_srs_r2 {q a q' a'} : trans' M (q, a) = Some (q', a', go_right) ->
        forall b, In_srs [#a; encode_state q; #b] [#a'; #b; encode_state q'].

  Lemma In_srsE u v : In_srs u v -> In (u, v) srs.
  Proof.
    case=> q a > E => [|[]|[]||[]||[]].
    all: have ? : In a [true; false] by (case: (a) => /=; tauto).
    all: have ? := all_fins_spec q.
    all: apply /in_flat_map; exists (q, a).
    all: split; first by apply: in_prod.
    all: by rewrite /= E /=; tauto.
  Qed.

  Lemma In_srsI u v : In (u, v) srs -> In_srs u v.
  Proof.
    move=> /in_flat_map [[q a]] [_] /=.
    have ? := In_srs_l2 _ true.
    have ? := In_srs_l2 _ false.
    have ? := In_srs_r2 _ true.
    have ? := In_srs_r2 _ false.
    have ? := In_srs_dl _ true.
    have ? := In_srs_dl _ false.
    have ? := In_srs_dr _ true.
    have ? := In_srs_dr _ false.
    case E: (trans' M (q, a)) => [[[q' a'] []]|] /=.
    - move=> [|[|[|[]]]] => - [<- <-].
      all: by auto using In_srs_l1.
    - move=> [|[|[|[]]]] => - [<- <-].
      all: by auto using In_srs_r1.
    - move=> [|[|[|[|[|[]]]]]] => - [<- <-].
      all: by auto using In_srs_f.
  Qed.

  (* step simulation *)
  Lemma simulation_step q t q' t' : step M (q, t) = Some (q', t') ->
    SR.rew srs (encode_config q t) (encode_config q' t').
  Proof.
    rewrite /step. move: t => [[ls a] rs].
    move E: (trans' M (q, a)) => [[[q'' a''] d]|]; last done.
    move=> [] <- <- /=.
    move: d ls rs E => [] => [[|l ls] rs|ls [|r rs]].
    - move=> /In_srs_l1 /In_srsE /SR.rewB.
      by move=> /(_ [] (map encode_symbol rs ++ [⦈])).
    - move=> /In_srs_l2 /(_ l) /In_srsE /SR.rewB.
      move=> /(_ (⦇ :: rev (map encode_symbol ls)) (map encode_symbol rs ++ [⦈])).
      by rewrite /= -!app_assoc.
    - move=> /In_srs_r1 /In_srsE /SR.rewB.
      move=> /(_ (⦇ :: rev (map encode_symbol ls)) []).
      by rewrite /= -!app_assoc.
    - move=> /In_srs_r2 /(_ r) /In_srsE /SR.rewB.
      move=> /(_ (⦇ :: rev (map encode_symbol ls)) (map encode_symbol rs ++ [⦈])).
      by rewrite /= -!app_assoc.
  Qed.

  Lemma simulation_halt q t : step M (q, t) = None ->
    SR.rewt srs (encode_config q t) [⦈; ⦇].
  Proof.
    rewrite /step. move: t => [[ls a] rs].
    move E: (trans' M (q, a)) => [[[q'' a''] d]|]; first done.
    move=> _. elim: ls.
    { elim: rs. 
      { apply: SR.rewS; [|by apply: SR.rewR].
        by move: E => /In_srs_f /In_srsE /SR.rewB => /(_ [] []). }
      move=> r rs IH. apply: SR.rewS; [|by eassumption].
      move: E => /In_srs_dr /(_ r) /In_srsE /SR.rewB.
      by move=> /(_ [⦇] (map encode_symbol rs ++ [⦈])). }
    move=> l ls IH. apply: SR.rewS; [|by eassumption].
    move: E => /In_srs_dl /(_ l) /In_srsE /SR.rewB.
    move=> /(_ (⦇ :: rev (map encode_symbol ls)) (map encode_symbol rs ++ [⦈])).
    by rewrite /= -!app_assoc.
  Qed.

  Lemma simulation q t k :
    steps M k (q, t) = None ->
    SR.rewt srs (encode_config q t) [⦈; ⦇].
  Proof.
    elim: k q t; first done.
    move=> k IH q t.
    rewrite (steps_plus 1 k). case E: (steps M 1 _) => [[q' t']|].
    - move: E => /simulation_step ?.
      move=> /IH. apply: SR.rewS; by eassumption.
    - by move: E => /simulation_halt.
  Qed.

  Lemma encode_symbol_inj a b : #a = #b -> a = b.
  Proof. by move: a b => [] []. Qed.

  Lemma encode_config_eq_app q ls a rs u v a' q' :
    encode_config q (ls, a, rs) = u ++ [#a'; encode_state q'] ++ v ->
    q = q' /\ a = a' /\
    u = ⦇ :: rev (map encode_symbol ls) /\ v = (map encode_symbol rs) ++ [⦈].
  Proof.
    move: u => [|c u]. { by case: a'. }
    move=> /= [<-]. elim /rev_ind: ls u => /=.
    { move=> [|{}c u].
      { move=> [] /encode_symbol_inj ? /Fin.to_nat_inj ? <-. tauto. }
      move: u => [|c' u]. { by case: (a'). }
      move=> [] _ _ E. exfalso.
      have : In (encode_state q') (u ++ # a' :: encode_state q' :: v).
      { apply /in_app_iff => /=. tauto. }
      rewrite -E. elim: rs {E}. { by case. }
      by move=> [] rs IH /= []. }
    move=> l ls IH u. rewrite map_app rev_unit.
    move: u => [|{}c u].
    - move=> [] _.
      elim /rev_ind: (ls).
      + move=> []. by case: (a).
      + move=> {}c > _. rewrite map_app rev_unit. move=> []. by case: (c).
    - move=> [<-] /IH [<-] [<-] [[-> ->]]. tauto.
  Qed.

  Lemma inverse_simulation_step q t x q' t' : 
    SR.rew srs (encode_config q t) x ->
    step M (q, t) = Some (q', t') ->
    x = encode_config q' t'.
  Proof.
    have reassoc (n m : nat) (u v : list nat) : u ++ (n :: m :: v) = (u ++ [n]) ++ m :: v.
    { by rewrite -app_assoc. }
    move Ey: (encode_config q t) => y Hyx.
    move: t Hyx Ey => [[ls a] rs] [] u v > /In_srsI [].
    - move=> > + H. move: H. rewrite (reassoc ⦇).
      move=> /encode_config_eq_app [<-] [<-]. by rewrite /step => _ ->.
    - move=> > + b H. move: H. rewrite (reassoc #b).
      move=> /encode_config_eq_app [<-] [<-]. by rewrite /step => _ ->.
    - move=> > + b H. move: H.
      move=> /encode_config_eq_app [<-] [<-]. by rewrite /step => _ ->.
    - move=> q'' a'' > + H. move: H. rewrite !(reassoc ⦇).
      move=> /encode_config_eq_app [<-] [<-] [].
      case: ls => [|l ?] /=.
      + rewrite /step. by move=> -> -> -> [] <- <-.
      + move=> /(app_inj_tail _ (_ :: _) _ (#l)) []. by case: l.  
    - move=> ???? + b H. move: H. rewrite !(reassoc #b).
      move=> /encode_config_eq_app [<-] [<-] [].
      case: ls => [|l ?] /=.
      + move=> /(@app_inj_tail nat _ []) []. by case: b.
      + rewrite /step. move=> -> -> -> [] <- <- /=.
        by rewrite -app_assoc.
    - move=> > + H. move: H.
      move=> /encode_config_eq_app [<-] [<-] [->].
      case: rs => [|r ?]; last by case: r.
      case: v; last done.
      rewrite /step. move=> _ -> [] <- <- /=.
      by rewrite -app_assoc.
    - move=> ???? + b H. move: H.
      move=> /encode_config_eq_app [<-] [<-] [->].
      case: rs => [|r ?]; first by case: b.
      move=> [/encode_symbol_inj ->] ->.
      rewrite /step. move=> -> [] <- <- /=.
      by rewrite -app_assoc.
  Qed.

  Lemma inverse_simulation q t :
    SR.rewt srs (encode_config q t) [⦈; ⦇] ->
    exists k, steps M k (q, t) = None.
  Proof.
    move Eu: (encode_config q t) => u.
    move Ev: [⦈; ⦇] => v Huv.
    elim: Huv q t Eu Ev. { by move=> ?? [[??]?] <-. }
    move=> x y z + _ + q t ??. subst x z.
    case E: (step M (q, t)) => [[q' t']|]; first last.
    { move=> *. by exists 1. }
    move: (E) => /inverse_simulation_step /[apply] ->.
    move=> /(_ _ _ erefl erefl) [k] Hk.
    exists (1+k). by rewrite steps_plus /= E.
  Qed.

End Construction.

Require Import Undecidability.Synthetic.Definitions.

Theorem reduction :
  SBTM_HALT ⪯ SR.SR.
Proof.
  exists ((fun '(existT _ M (q, t)) => (srs M, encode_config M q t, [1; 0]))).
  move=> [M [q t]] /=. split.
  - by move=> [?] /simulation.
  - by apply: inverse_simulation.
Qed.
