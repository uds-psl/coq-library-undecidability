(*
  Autor(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  Decision Procedure(s):
    Two-counter Machine Reversibility (CM2_REV)
*)

Require Import List ListDec PeanoNat Lia Operators_Properties.
Import ListNotations.
Require Import Undecidability.CounterMachines.CM2.
From Undecidability.CounterMachines.Util Require Import Facts CM2_facts.
Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

Section Construction.
Variable M : Cm2.

#[local] Notation step := (CM2.step M).
#[local] Notation l := (length M).

Lemma finite_characterization : let t := list_prod (seq 0 l) (list_prod [0;1;2] [0;1;2]) in
  Forall (fun '(x, y) => step x = step y -> x = y) (list_prod t t) ->
  reversible M.
Proof.
  move=> t. pose P := fun '(x, y) => x <> y /\ step x = step y.
  have := Exists_dec P (list_prod t t).
  apply: unnest.
  { move=> [x y]. rewrite /P.
    have [<-|?] := Config_eq_dec x y.
    { right. tauto. }
    have [<-|?] := option_Config_eq_dec (step x) (step y).
    { by left. }
    right. tauto. }
  case.
  { move=> /Exists_exists [[x y]] [Hxyt] [H1Pxy H2Pxy].
    by move=> /Forall_forall /(_ (x, y) Hxyt H2Pxy) /H1Pxy. }
  move=> H _.
  have Ht : forall p1 a1 b1 p2 a2 b2,
  ~ l <= p1 -> ~ l <= p2 -> 0 <= a1 <= 2 -> 0 <= b1 <= 2 -> 0 <= a2 <= 2 -> 0 <= b2 <= 2 -> 
  In (p1, (a1, b1), (p2, (a2, b2))) (list_prod t t).
  { move=> > ??????. apply /in_prod; (apply /in_prod; [apply /in_seq|apply /in_prod]).
    all: move=> /=; lia. }
  move=> [p1 [a1 b1]] [p2 [a2 b2]] z H1 H2.
  suff ? : (not (p1 <> p2 \/ a1 <> a2 \/ b1 <> b2)).
  { congr (_, (_, _)); lia. }
  move=> H'. apply: H. apply /Exists_exists.
  have H'p1 : not (l <= p1).
  { move=> /nth_error_None Hp1. move: H1. by rewrite /step /= Hp1. }
  have H'p2 : not (l <= p2).
  { move=> /nth_error_None Hp2. move: H2. by rewrite /step /= Hp2. }
  move: H1. rewrite -H2. clear H2.
  rewrite /step /=.
  case Hp1: (nth_error M p1) => [i|]; first last.
  { move: Hp1 => /nth_error_None. lia. }
  case Hp2: (nth_error M p2) => [j|]; first last.
  { move: Hp2 => /nth_error_None. lia. }
  move: H'p1 H'p2 => /Ht {}Ht /Ht {}Ht. 
  move: i j Hp1 Hp2 => [c1|c1 q1] [c2|c2 q2].
  - move=> + + [? ? ?]. subst p2. move=> -> [?]. subst c2.
    lia.
  - case: c2 H'; [move: b2=> [|b2]|move: a2=> [|a2]].
    + move=> ? + + [? ? ?]. subst p2. by move=> ->.
    + move=> ? Hp1 Hp2 [? ? ?]. subst q2.
      exists ((p1, (0, 0)), (p2, (0 + (if c1 then 0 else 1), 1 + (if c1 then 1 else 0)))). split.
      { apply: Ht; case: (c1); lia. }
      split; first done.
      rewrite /step Hp1 Hp2 /=. congr (Some (_, (_, _))); lia.
    + move=> ? + + [? ? ?]. subst p2. by move=> ->.
    + move=> ? Hp1 Hp2 [? ? ?]. subst q2.
      exists ((p1, (0, 0)), (p2, (1 + (if c1 then 0 else 1), 0 + (if c1 then 1 else 0)))). split.
      { apply: Ht; case: (c1); lia. }
      split; first done.
      rewrite /step Hp1 Hp2 /=. congr (Some (_, (_, _))); lia.
  - case: c1 H'; [move: b1=> [|b1]|move: a1=> [|a1]].
    + move=> ? + + [? ? ?]. subst p2. by move=> ->.
    + move=> ? Hp1 Hp2 [? ? ?]. subst q1.
      exists ((p1, (0 + (if c2 then 0 else 1), 1 + (if c2 then 1 else 0))), (p2, (0, 0))). split.
      { apply: Ht; case: (c2); lia. }
      split; first done.
      rewrite /step Hp1 Hp2 /=. congr (Some (_, (_, _))); lia.
    + move=> ? + + [? ? ?]. subst p2. by move=> ->.
    + move=> ? Hp1 Hp2 [? ? ?]. subst q1.
      exists ((p1, (1 + (if c2 then 0 else 1), 0 + (if c2 then 1 else 0))), (p2, (0, 0))). split.
      { apply: Ht; case: (c2); lia. }
      split; first done.
      rewrite /step Hp1 Hp2 /=. congr (Some (_, (_, _))); lia.
  - move: c1 a1 b1 c2 a2 b2 H' => [] => [a1 [|b1]|[|a1] b1].
    all: move=> [] => [a2 [|b2]|[|a2] b2] ?.
    all: move=> Hp1 Hp2 [] *; subst.
    + lia.
    + exists ((p1, (0, 0)), (p2, (0, 1))).
      split; [apply: Ht; lia|split; first done].
      rewrite /step Hp1 Hp2 /=. congr (Some (_, (_, _))); lia.
    + by move: Hp1 Hp2 => ->.
    + exists ((p1, (0, 0)), (p2, (1, 0))).
      split; [apply: Ht; lia|split; first done].
      rewrite /step Hp1 Hp2 /=. congr (Some (_, (_, _))); lia.
    + exists ((p1, (0, 1)), (p2, (0, 0))).
      split; [apply: Ht; lia|split; first done].
      rewrite /step Hp1 Hp2 /=. congr (Some (_, (_, _))); lia.
    + exists ((p1, (0, 1)), (p2, (0, 1))).
      split; [apply: Ht; lia|split; first by (case; lia)].
      rewrite /step Hp1 Hp2 /=. congr (Some (_, (_, _))); lia.
    + exists ((p1, (0, 1)), (p2, (0, 0))).
      split; [apply: Ht; lia|split; first done].
      rewrite /step Hp1 Hp2 /=. congr (Some (_, (_, _))); lia.
    + exists ((p1, (0, 1)), (p2, (1, 0))).
      split; [apply: Ht; lia|split; first done].
      rewrite /step Hp1 Hp2 /=. congr (Some (_, (_, _))); lia.
    + by move: Hp1 Hp2 => ->.
    + exists ((p1, (0, 0)), (p2, (0, 1))).
      split; [apply: Ht; lia|split; first done].
      rewrite /step Hp1 Hp2 /=. congr (Some (_, (_, _))); lia.
    + lia.
    + exists ((p1, (0, 0)), (p2, (1, 0))).
      split; [apply: Ht; lia|split; first done].
      rewrite /step Hp1 Hp2 /=. congr (Some (_, (_, _))); lia.
    + exists ((p1, (1, 0)), (p2, (0, 0))).
      split; [apply: Ht; lia|split; first done].
      rewrite /step Hp1 Hp2 /=. congr (Some (_, (_, _))); lia.
    + exists ((p1, (1, 0)), (p2, (0, 1))).
      split; [apply: Ht; lia|split; first done].
      rewrite /step Hp1 Hp2 /=. congr (Some (_, (_, _))); lia.
    + exists ((p1, (1, 0)), (p2, (0, 0))).
      split; [apply: Ht; lia|split; first done].
      rewrite /step Hp1 Hp2 /=. congr (Some (_, (_, _))); lia.
    + exists ((p1, (1, 0)), (p2, (1, 0))).
      split; [apply: Ht; lia|split; first by (case; lia)].
      rewrite /step Hp1 Hp2 /=. congr (Some (_, (_, _))); lia.
Qed.

(* informative decision statement for reversibility for Cm2 *)
Theorem decision : (reversible M) + (not (reversible M)).
Proof.
  pose t := list_prod (seq 0 l) (list_prod [0;1;2] [0;1;2]).
  have := Forall_Exists_dec (fun '(x, y) => step x = step y -> x = y) _ (list_prod t t).
  apply: unnest.
  { move=> [x y].
    have [<-|?] := Config_eq_dec x y.
    { left. tauto. }
    have := option_Config_eq_dec (step x) (step y).
    move=> [<-|?]; [right|left]; tauto. }
  case.
  { move=> /finite_characterization ?. by left. }
  move=> H. right.
  move: H => /Exists_exists [[x y]] [H'xy] Hxy HM. apply: Hxy.
  move=> Hxy.
  case Hxz: (step x) => [z|]. { apply: (HM x y z); [done|by rewrite -Hxy]. }
  move: Hxz => /step_None /nth_error_None.
  move: x H'xy {Hxy} => [p [a b]] /in_prod_iff [+ _].
  move=> /in_prod_iff [/in_seq + _] /=. lia.
Qed.

End Construction.

Require Import Undecidability.Synthetic.Definitions.

(* decision procedure for the reversibility of Cm2 *)
Definition decide : Cm2 -> bool :=
  fun M =>
    match decision M with
    | inl _ => true
    | inr _ => false
    end.

(* decision procedure correctness *)
Lemma decide_spec : decider decide CM2_REV.
Proof.
  rewrite /decider /reflects /decide => M.
  case: (decision M); [tauto | done].
Qed.
