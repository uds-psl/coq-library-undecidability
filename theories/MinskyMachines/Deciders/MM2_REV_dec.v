(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  Decision Procedure(s):
    Two-counter Machine Reversibility (MM2_REV)

  References:
  [1] Dudenhefner, Andrej. "Certified Decision Procedures for Two-Counter Machines."
      FSCD 2022. https://drops.dagstuhl.de/opus/volltexte/2022/16297/
*)

From Stdlib Require Import List ListDec PeanoNat Lia Operators_Properties.
Import ListNotations.
Require Import Undecidability.MinskyMachines.MM2.
Require Import Undecidability.MinskyMachines.Util.MM2_facts.
Import MM2Notations.

From Stdlib Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

Section Construction.
Variable M : list mm2_instr.

#[local] Notation step := (mm2_step M).
#[local] Notation l := (length M).

(* characterize reversibility via a finite number of configurations *)
Lemma finite_characterization : let t := list_prod (seq 1 l) (list_prod [0;1;2] [0;1;2]) in
  Forall (fun '(x, y) => forall z, step x z -> step y z -> x = y) (list_prod t t) ->
  mm2_reversible M.
Proof.
  move=> t. pose P := fun '(x, y) => x <> y /\ exists z, step x z /\ step y z.
  have /(Exists_dec P (list_prod t t)): forall xy, {P xy} + {~ P xy}.
  { move=> [x y]. rewrite /P.
    have [<-|?] := mm2_state_eq_dec x y.
    { right. tauto. }
    have [[z1 Hxz1]|Hx] := mm2_sig_step_dec M x.
    - have [[z2 Hyz2]|Hy] := mm2_sig_step_dec M y.
      + have [?|?] := mm2_state_eq_dec z2 z1.
        * left. subst z2. split; [done|]. by exists z1.
        * right => - [?] [? []].
          move: Hxz1 => /mm2_step_det /[apply] <-.
          by move: Hyz2 => /mm2_step_det /[apply].
      + by right => - [_ [?]] [_ /Hy].
    - by right => - [_ [?]] [/Hx]. }
  case.
  { move=> /Exists_exists [[x y]] [Hxyt] [H1Pxy [z [Hxz Hyz]]].
    by move=> /Forall_forall /(_ (x, y) Hxyt) /(_ z Hxz Hyz). }
  move=> /Forall_Exists_neg /Forall_forall HP _.
  have H''P : forall i j p1 a1 b1 p2 a2 b2 z, mm2_instr_at i p1 M -> mm2_instr_at j p2 M ->
    0 <= a1 <= 2 /\ 0 <= b1 <= 2 /\ 0 <= a2 <= 2 /\ 0 <= b2 <= 2 -> (p1, (a1, b1)) <> (p2, (a2, b2)) ->
    mm2_atom i (p1, (a1, b1)) z -> mm2_atom j (p2, (a2, b2)) z -> False.
  { move=> i j p1 a1 b1 p2 a2 b2 z /[dup] ? /mm2_instr_at_bounds Hi /[dup] ? /mm2_instr_at_bounds Hj *.
    apply: (HP ((p1, (a1, b1)), (p2, (a2, b2)))).
    - apply /in_prod; (apply /in_prod; [apply /in_seq|apply /in_prod]).
      all: move=> /=; lia.
    - split; [done|].
      eexists. by split; eexists; split; eassumption. }
  move=> x y z [i] [Hi Hxz] [j] [Hj].
  move Ezz': (z) => z' Hyz'.
  have Hij : fst x = fst y -> i = j.
  { move=> Hxy. move: Hxy Hi Hj => ->. by apply: mm2_instr_at_unique. }
  move: (Hi) (Hj) => /H''P /[apply] {}H''P.
  move: Hxz Hyz' Ezz' Hij Hi Hj H''P.
  case=> p1 => [a1 b1|a1 b1|q1 a1 b1|q1 a1 b1|q1 b1|q1 a1].
  all: case=> p2 => [a2 b2|a2 b2|q2 a2 b2|q2 a2 b2|q2 b2|q2 a2] /= [] ??? ???; subst.
  - intuition congruence.
  - intuition congruence.
  - move=> /(_ 0 0 2 0) H''P. exfalso. apply: H''P; by [|constructor|case|lia].
  - move=> /(_ 0 0 1 1) H''P. exfalso. apply: H''P; by [|constructor|case|lia].
  - intuition congruence.
  - intuition congruence.
  - intuition congruence.
  - intuition congruence.
  - move=> /(_ 0 0 1 1) H''P. exfalso. apply: H''P; by [|constructor|case|lia].
  - move=> /(_ 0 0 0 2) H''P. exfalso. apply: H''P; by [|constructor|case|lia].
  - intuition congruence.
  - intuition congruence.
  - move=> /(_ 2 0 0 0) H''P. exfalso. apply: H''P; by [|constructor|case|lia].
  - move=> /(_ 1 1 0 0) H''P. exfalso. apply: H''P; by [|constructor|case|lia].
  - have [|?] : p1 = p2 \/ p1 <> p2 by lia.
    + intuition congruence.
    + move=> /(_ 1 0 1 0) H''P. exfalso. apply: H''P; by [|constructor|case|lia].
  - move=> /(_ 1 0 0 1) H''P. exfalso. apply: H''P; by [|constructor|case|lia].
  - move=> /(_ 1 0 0 0) H''P. exfalso. apply: H''P; by [|constructor|case|lia].
  - move=> /(_ 1 0 0 0) H''P. exfalso. apply: H''P; by [|constructor|case|lia].
  - move=> /(_ 1 1 0 0) H''P. exfalso. apply: H''P; by [|constructor|case|lia].
  - move=> /(_ 0 2 0 0) H''P. exfalso. apply: H''P; by [|constructor|case|lia].
  - move=> /(_ 0 1 1 0) H''P. exfalso. apply: H''P; by [|constructor|case|lia].
  - have [|?] : p1 = p2 \/ p1 <> p2 by lia.
    + intuition congruence.
    + move=> /(_ 0 1 0 1) H''P. exfalso. apply: H''P; by [|constructor|case|lia].
  - move=> /(_ 0 1 0 0) H''P. exfalso. apply: H''P; by [|constructor|case|lia].
  - move=> /(_ 0 1 0 0) H''P. exfalso. apply: H''P; by [|constructor|case|lia].
  - intuition congruence.
  - intuition congruence.
  - move=> /(_ 0 0 1 0) H''P. exfalso. apply: H''P; by [|constructor|case|lia].
  - move=> /(_ 0 0 0 1) H''P. exfalso. apply: H''P; by [|constructor|case|lia].
  - intuition congruence.
  - intuition congruence.
  - intuition congruence.
  - intuition congruence.
  - move=> /(_ 0 0 1 0) H''P. exfalso. apply: H''P; by [|constructor|case|lia].
  - move=> /(_ 0 0 0 1) H''P. exfalso. apply: H''P; by [|constructor|case|lia].
  - intuition congruence.
  - intuition congruence.
Qed.

(* informative decision statement for reversibility for mm2 *)
Theorem decision : (mm2_reversible M) + (not (mm2_reversible M)).
Proof.
  pose t := list_prod (seq 1 l) (list_prod [0;1;2] [0;1;2]).
  pose P := fun '(x, y) => forall z, step x z -> step y z -> x = y.
  have: forall xy, {P xy} + {~ P xy}.
  { move=> [x y]. subst P.
    have [<-|?] := mm2_state_eq_dec x y.
    { left. tauto. }
    have [[z1 Hxz1]|Hx] := mm2_sig_step_dec M x.
    - have [[z2 Hyz2]|Hy] := mm2_sig_step_dec M y.
      + have [?|?] := mm2_state_eq_dec z2 z1.
        * right. subst z2. by move=> /(_ z1 Hxz1 Hyz2).
        * left => ?.
          move: Hxz1 => /mm2_step_det /[apply] <-.
          by move: Hyz2 => /mm2_step_det /[apply].
      + by left => ?? /Hy.
    - by left => ? /Hx. }
  move=> /(Forall_Exists_dec P) /(_ (list_prod t t)).
  case.
  { move=> /finite_characterization ?. by left. }
  move=> H. right.
  move: H => /Exists_exists [[x y]] [H'xy] Hxy HM. apply: Hxy.
  by apply: HM.
Qed.

End Construction.

Require Import Undecidability.Synthetic.Definitions.

(* decision procedure for the reversibility of mm2 *)
Definition decide : list mm2_instr -> bool :=
  fun M =>
    match decision M with
    | inl _ => true
    | inr _ => false
    end.

(* decision procedure correctness *)
Lemma decide_spec : decider decide MM2_REV.
Proof.
  rewrite /decider /reflects /decide => M.
  case: (decision M); [tauto | done].
Qed.
