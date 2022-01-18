(*
  Autor(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  Decision Procedure(s):
    Two-counter Machine Uniform Mortality (CM2_UMORTAL)
*)

Require Import List PeanoNat Lia Operators_Properties ConstructiveEpsilon.
Import ListNotations.
Require Import Undecidability.CounterMachines.CM2.
Require Undecidability.CounterMachines.Deciders.CM2_UBOUNDED_dec.
From Undecidability.CounterMachines.Util Require Import Facts CM2_facts.
Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".
Set Default Proof Using "Type".

Section Construction.

Variable M : Cm2.

#[local] Notation steps := (CM2.steps M).
#[local] Notation mortal := (CM2.mortal M).
#[local] Notation bounded := (bounded M).

(* uniform bound *)
Variable K : nat.
Variable HK : forall x, bounded K x.

Lemma pos_K : K = 1 + (K - 1).
Proof using HK.
  suff: K <> 0 by lia.
  move=> H'K.
  have := HK (0, (0, 0)). rewrite H'K.
  move=> [[|L]].
  - by move=> [_] /(_ (0, (0, 0)) (reaches_refl _)).
  - move=> ? /=. lia.
Qed.

Lemma uniform_decision : (uniformly_mortal M) + (not (uniformly_mortal M)).
Proof using HK.
  have := Forall_dec (fun 'x => mortal K x) _
    (list_prod (seq 0 (length M)) (list_prod (seq 0 (K+1)) (seq 0 (K+1)))).
  case.
  { move=> x. rewrite /(mortal K). by case: (steps K x) => [y|]; [right|left]. }
  - move=> H'M. left. exists K => - [p [a b]].
    have [?|?] : length M <= p \/ p < length M by lia.
    { rewrite /(mortal K) pos_K /steps iter_plus /= /step /=.
      have -> : nth_error M p = None by apply /nth_error_None.
      by rewrite oiter_None. }
    apply /mortal_K_bound.
    move: H'M => /Forall_forall. apply.
    apply /in_prod. { apply /in_seq. lia. }
    apply /in_prod; apply /in_seq; lia.
  - move=> H. right => - [K' H'M]. apply: H. apply /Forall_forall.
    move=> [p [a b]] /in_prod_iff [/in_seq ?] /in_prod_iff [/in_seq ?] /in_seq ?.
    by apply: (bounded_mortal_bound (HK _) (H'M _)).
Qed.
End Construction.

(* informative decision statement for uniform boundedness for Cm2 *)
Theorem decision (M: Cm2) : (uniformly_mortal M) + (not (uniformly_mortal M)).
Proof.
  case: (CM2_UBOUNDED_dec.decision M).
  - move=> /constructive_indefinite_ground_description.
    move=> /(_ id id ltac:(done) (CM2_UBOUNDED_dec.fixed_decision M)).
    by move=> [K /uniform_decision].
  - move=> H. right. move=> [k Hk]. apply: H. exists k => x.
    apply: mortal_bounded. by apply: Hk.
Qed.

Require Import Undecidability.Synthetic.Definitions.

(* decision procedure for uniform mortality for Cm2 *)
Definition decide : Cm2 -> bool :=
  fun M =>
    match decision M with
    | inl _ => true
    | inr _ => false
    end.

(* decision procedure correctness *)
Lemma decide_spec : decider decide CM2_UMORTAL.
Proof.
  rewrite /decider /reflects /decide => M.
  case: (decision M); intuition done.
Qed.
