(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  Decision Procedure(s):
    Two-counter Machine Uniform Mortality (MM2_UMORTAL)

  References:
  [1] Dudenhefner, Andrej. "Certified Decision Procedures for Two-Counter Machines."
      FSCD 2022. https://drops.dagstuhl.de/opus/volltexte/2022/16297/
*)

From Stdlib Require Import List PeanoNat Lia Relation_Operators Operators_Properties ConstructiveEpsilon.
Import ListNotations.

Require Import Undecidability.MinskyMachines.MM2.
Require Import Undecidability.MinskyMachines.Deciders.MM2_UBOUNDED_dec.
Require Import Undecidability.MinskyMachines.Util.MM2_facts.

From Stdlib Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

Section Construction.

Variable M : list mm2_instr.

#[local] Notation steps := (steps M).
#[local] Notation mortal := (MM2.mm2_mortal M).
#[local] Notation bounded := (MM2.mm2_bounded M).

(* uniform bound *)
Variable K : nat.
Variable HK : forall x, bounded K x.

Lemma pos_K : K = 1 + (K - 1).
Proof using HK.
  suff: K <> 0 by lia.
  move=> H'K.
  have := HK (0, (0, 0)). rewrite H'K.
  move=> [[|L]].
  - move=> [_]. apply. apply: rt_refl.
  - move=> ? /=. lia.
Qed.

Lemma mortal_steps_iff k x : mortal k x <-> steps (S k) x = None.
Proof.
  elim: k x.
  { move=> x /=. split.
    - case: (mm2_sig_step_dec M x) => [[y Hxy]|]; last done.
      move=> /(_ [y]) /= H. suff : 1 <= 0 by lia.
      by apply: H.
    - case: (mm2_sig_step_dec M x) => [[y Hxy]|Hx]; first done.
      move=> _ [|??]; first done.
      by move=> [/Hx]. }
  move=> k IH x /=. split.
  - case: (mm2_sig_step_dec M x) => [[y Hxy]|]; last done.
    move=> Hx. apply /IH.
    move=> L HyL. move: (Hx (y::L)) => /= H.
    suff: S (length L) <= S k by lia.
    by apply: H.
  - case: (mm2_sig_step_dec M x) => [[y Hxy]|Hx].
    + move=> /IH Hy [|??] /=; [lia|].
      move: Hxy => /mm2_step_det + [] => /[apply] <-.
      move=> /Hy. lia.
    + move=> _ [|??] /=; [lia|].
      by move=> [/Hx].
Qed.

Lemma boundedE {K' x} : bounded K' x ->
  (In (steps K' x) (path M K' x)) + (steps K' x = None).
Proof.
  move=> HK'.
  case Hy: (steps K' x) => [y|]; last by right.
  have [|] := In_dec option_mm2_state_eq_dec (Some y) (path M K' x).
  { rewrite -Hy => ?. by left. }
  rewrite -Hy. move=> /path_noloopI /NoDup_not_bounded.
  by move=> /(_ y Hy HK').
Qed.

Lemma mortal_K_bound k p a b :
  mortal k (p, (Nat.min (S k) a, Nat.min (S k) b)) -> mortal k (p, (a, b)).
Proof.
  move=> /mortal_steps_iff H. apply /mortal_steps_iff.
  have [/Nat.min_r <-|?] : a <= S k \/ S k < a by lia.
  - have [/Nat.min_r <-|?] : b <= S k \/ S k < b by lia.
    + done.
    + have ->: b = (Nat.min (S k) b) + (b - (S k)) by lia.
      rewrite shift_steps_b; [lia|].
      by rewrite H.
  - have ->: a = (Nat.min (S k) a) + (a - (S k)) by lia.
    rewrite shift_steps_a; [lia|].
    have [/Nat.min_r <-|?] : b <= S k \/ S k < b by lia.
    + by rewrite H.
    + have ->: b = (Nat.min (S k) b) + (b - (S k)) by lia.
      rewrite shift_steps_b; [lia|].
      by rewrite H.
Qed.

Lemma bounded_mortal_bound {k x} : bounded (S K) x -> mortal k x -> mortal K x.
Proof.
  move=> /boundedE + /mortal_steps_iff Hk.
  case.
  - move=> /path_loopE /(_ (S k)).
    rewrite Hk => /In_None_pathE ?.
    by apply /mortal_steps_iff.
  - move=> ?. by apply /mortal_steps_iff.
Qed.

Lemma pointwise_decision x : {mortal K x} + {not (mortal K x)}.
Proof.
  case H'Kx: (steps (S K) x) => [y|].
  - right => /mortal_steps_iff. by rewrite H'Kx.
  - left. by apply /mortal_steps_iff.
Qed.

Lemma uniform_decision : (mm2_uniformly_mortal M) + (not (mm2_uniformly_mortal M)).
Proof using HK.
  have := Forall_dec (fun 'x => mortal K x) _
    (list_prod (seq 1 (length M)) (list_prod (seq 0 (K+2)) (seq 0 (K+2)))).
  case.
  { move=> x. by apply: pointwise_decision. }
  - move=> H'M. left. exists K => - [p [a b]].
    have [?|?] : (p = 0 \/ length M < p) \/ 0 < p <= length M by lia.
    { move=> [|??] /=; first by lia.
      move=> [[?]] [/mm2_instr_at_bounds] /=. lia. }
    apply /mortal_K_bound.
    move: H'M => /Forall_forall. apply.
    apply /in_prod. { apply /in_seq. lia. }
    apply /in_prod; apply /in_seq; lia.
  - move=> H. right => - [K' H'M]. apply: H. apply /Forall_forall.
    move=> [p [a b]] /in_prod_iff [/in_seq ?] /in_prod_iff [/in_seq ?] /in_seq ?.
    apply: (bounded_mortal_bound _ (H'M _)).
    apply: (bounded_monotone _ _ (HK _)). lia.
Qed.
End Construction.

(* informative decision statement for uniform boundedness for mm2 *)
Theorem decision (M: list mm2_instr) : (mm2_uniformly_mortal M) + (not (mm2_uniformly_mortal M)).
Proof.
  case: (MM2_UBOUNDED_dec.decision M).
  - move=> /constructive_indefinite_ground_description.
    move=> /(_ id id (fun=> erefl) (MM2_UBOUNDED_dec.fixed_decision M)).
    by move=> [K /uniform_decision].
  - move=> H. right. move=> [k Hk]. apply: H. exists (S k) => x.
    apply: mortal_bounded. by apply /mortal_steps_iff.
Qed.

Require Import Undecidability.Synthetic.Definitions.

(* decision procedure for uniform mortality for mm2 *)
Definition decide : list mm2_instr -> bool :=
  fun M =>
    match decision M with
    | inl _ => true
    | inr _ => false
    end.

(* decision procedure correctness *)
Lemma decide_spec : decider decide MM2_UMORTAL.
Proof.
  rewrite /decider /reflects /decide => M.
  case: (decision M); intuition done.
Qed.
