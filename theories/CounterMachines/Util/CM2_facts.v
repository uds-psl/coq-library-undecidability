Require Import List ListDec Lia PeanoNat Relation_Operators.
Import ListNotations.

Require Import Undecidability.CounterMachines.Util.Facts.
Require Import Undecidability.CounterMachines.CM2.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".
Set Default Proof Using "Type".

Definition path M k x := map (fun n => steps M n x) (seq 0 k).

Lemma Config_eta (x : Config) : x = (state x, (value1 x, value2 x)).
Proof. by move: x => [? [? ?]]. Qed.

Lemma Config_eq_dec (x y : Config) : {x = y} + {x <> y}.
Proof. by do ? decide equality. Qed.

Lemma option_Config_eq_dec (x y : option Config) : {x = y} + {x <> y}.
Proof. by do ? decide equality. Qed.

Definition reaches_plus (M: Cm2) (x y: Config) := exists k, 0 < k /\ steps M k x = Some y.
Definition non_terminating (M: Cm2) (x: Config) := forall k, steps M k x <> None.

Section Facts.
Context {M : Cm2}.

#[local] Notation step := (CM2.step M).
#[local] Notation steps := (CM2.steps M).
#[local] Notation reaches := (CM2.reaches M).
#[local] Notation reaches_plus := (reaches_plus M).
#[local] Notation terminating := (CM2.terminating M).
#[local] Notation non_terminating := (non_terminating M).
#[local] Notation mortal := (CM2.mortal M).
#[local] Notation bounded := (CM2.bounded M).
#[local] Notation path := (path M).

Lemma step_neq x : step x <> Some x.
Proof.
  rewrite /step. case: (nth_error M (state x)); last done.
  move: x => [p [a b]] /=.
  case.
  - move=> ? []. lia.
  - move: a b => [|a] [|b] [] ? []; lia.
Qed. 

Lemma steps_k_monotone {k x} k' : steps k x = None -> k <= k' -> steps k' x = None.
Proof.
  move=> + ?. have ->: k' = (k' - k) + k by lia.
  elim: (k' - k); first done.
  by move=> ? IH /IH /= ->.
Qed.

Lemma reaches_refl x : reaches x x.
Proof. by exists 0. Qed.

Lemma step_reaches {x y} : step x = Some y -> reaches x y.
Proof. move=> ?. by exists 1. Qed.

Lemma step_reaches_plus {x y} : step x = Some y -> reaches_plus x y.
Proof. move=> ?. exists 1. split; [lia|done]. Qed.

Lemma steps_plus {k x k' y} :
  steps k x = Some y -> steps (k + k') x = steps k' y.
Proof. rewrite /steps iter_plus. by move=> ->. Qed.

Lemma steps_sub {i j x y z} :
  i <= j ->
  steps i x = Some y ->
  steps j x = Some z ->
  steps (j-i) y = Some z.
Proof.
  move=> ? Hi. rewrite [in steps j x](ltac:(lia) : j = i + (j - i)).
  by rewrite /steps iter_plus -/(steps _ _) Hi.
Qed.

Lemma step_None x : step x = None <-> nth_error M (state x) = None.
Proof.
  rewrite /step. case: (nth_error M (state x)) => [i|]; last done.
  case: i; first done.
  by move: (value1 x) (value2 x) => [|?] [|?] [].
Qed.

Lemma step_None' x : step x = None <-> length M <= state x.
Proof. rewrite step_None. by apply: nth_error_None. Qed.

Lemma reaches_plus_reaches {x y z} : reaches_plus x y -> reaches y z -> reaches_plus x z.
Proof.
  move=> [k [? Hk]] [k' Hk']. exists (k+k'). split; first by lia.
  move: Hk. by rewrite /steps iter_plus => ->.
Qed.

Lemma reaches_reaches_plus {x y z} : reaches x y -> reaches_plus y z -> reaches_plus x z.
Proof.
  move=> [k Hk] [k' [? Hk']]. exists (k+k'). split; first by lia.
  move: Hk. by rewrite /steps iter_plus => ->.
Qed.

Lemma reaches_plus_incl {x y} : reaches_plus x y -> reaches x y.
Proof. move=> [k [? Hk]]. by exists k. Qed.

Lemma reaches_neq_incl {x y} : reaches x y -> x <> y -> reaches_plus x y.
Proof.
  move=> [[|k]]; first by move=> [->].
  move=> ? _. exists (S k). split; [lia|done].
Qed.

Lemma reaches_terminating {x y} : reaches x y -> terminating y -> terminating x.
Proof.
  move=> [k Hk] [k' Hk']. exists (k+k').
  move: Hk. by rewrite /steps iter_plus => ->.
Qed.

Lemma reaches_non_terminating {x y} : reaches x y -> non_terminating y -> non_terminating x.
Proof.
  move=> [k Hk] Hy k'.
  have [|->] : k' <= k \/ k' = k + (k' - k) by lia.
  - by move: Hk => + /steps_k_monotone H /H => ->.
  - rewrite (steps_plus Hk). by apply: Hy.
Qed.

Lemma reaches_non_terminating' {x y} : reaches x y -> non_terminating x -> non_terminating y.
Proof.
  move=> [k' Hk'] Hx k Hk.
  apply: (Hx (k' + k)).
  by rewrite (steps_plus Hk').
Qed.

Lemma reaches_plus_state_bound {x y} : reaches_plus x y -> state x < length M.
Proof.
  move=> [k [? Hk]].
  suff: not (length M <= state x) by lia.
  move=> /nth_error_None Hx.
  move: Hk. have ->: k = S (k - 1) by lia.
  by rewrite /= obind_oiter /step Hx oiter_None.
Qed.

Lemma reaches_plus_trans {x y z} : reaches_plus x y -> reaches_plus y z -> reaches_plus x z.
Proof. by move=> /reaches_plus_incl /reaches_reaches_plus H /H. Qed.

Lemma reaches_trans {x y z} : reaches x y -> reaches y z -> reaches x z.
Proof. move=> [k Hk] [k' Hk']. exists (k+k'). by rewrite (steps_plus Hk). Qed.

Lemma reaches_plus_invariant_loop (P : Config -> Prop) :
  (forall x, P x -> exists y, reaches_plus x y /\ P y) ->
  forall x, P x -> non_terminating x.
Proof.
  move=> H x Hx k. elim: k x Hx; first done.
  move=> k IH x /H [y] [[k' [? Hk']]] /IH Hk.
  move=> /(steps_k_monotone (k' + k)) /(_ ltac:(lia)).
  by rewrite (steps_plus Hk').
Qed.

Corollary reaches_plus_self_loop x : reaches_plus x x -> non_terminating x.
Proof.
  move=> ?. apply: (reaches_plus_invariant_loop (fun y => y = x)); last done.
  move=> y ->. by exists x. 
Qed.

Lemma steps_loop_mod {K x k} : steps (S K) x = Some x ->
  steps k x = steps (k mod (S K)) x.
Proof.
  rewrite [in steps k x](Nat.div_mod_eq k (S K)).
  move: (k mod (S K)) => k' Hx. elim: (k / S K).
  - congr steps. lia.
  - move=> n IH. have ->: S K * S n + k' = S K + (S K * n + k') by lia.
    by move: Hx => /steps_plus ->.
Qed.

Lemma step_values_bound x y : step x = Some y ->
  value1 y + value2 y <= 1 + value1 x + value2 x /\
  value1 x + value2 x <= 1 + value1 y + value2 y /\
  value1 x <= 1 + value1 y /\ value1 y <= 1 + value1 x /\
  value2 x <= 1 + value2 y /\ value2 y <= 1 + value2 x.
Proof.
  rewrite /step.
  case: (nth_error M (state x)); last done.
  case.
  - move=> [] [<-] /=; lia.
  - move=> [] ? [<-].
    + case Hx: (value2 x) => [|?] /=; lia.
    + case Hx: (value1 x) => [|?] /=; lia.
Qed.

Lemma steps_values_bound k x y : steps k x = Some y ->
  value1 y + value2 y <= k + value1 x + value2 x /\
  value1 x + value2 x <= k + value1 y + value2 y /\
  value1 x <= k + value1 y /\ value1 y <= k + value1 x /\
  value2 x <= k + value2 y /\ value2 y <= k + value2 x.
Proof.
  elim: k x. { move=> ? [<-]. lia. }
  move=> k IH x. rewrite /= obind_oiter.
  case Hxz: (step x) => [z|]; last by rewrite oiter_None.
  move=> /IH.
  move: Hxz => /step_values_bound. lia.
Qed.

Lemma bounded_monotone {k k' x} : k <= k' -> bounded k x -> bounded k' x.
Proof. move=> ? [L [? ?]]. exists L. split; [lia|done]. Qed.

#[local] Arguments Nat.min !n !m /.

Lemma shift_steps k p a b :
  steps k (p, (a, b)) =
  match steps k (p, (Nat.min k a, Nat.min k b)) with
  | Some (p', (a', b')) => Some (p', (a' + (a - k), b' + (b - k)))
  | None => None
  end.
Proof.
  set x := (p, (a, b)).
  have ->: p = state x by done.
  have ->: a = value1 x by done.
  have ->: b = value2 x by done.
  elim: k (x); clear x p a b.
  { move=> [p [a b]] /=. congr (Some (_, (_, _))); lia. }
  move=> k IH [p [a b]].
  rewrite /steps /= ?obind_oiter /step -/step /=.
  case: (nth_error M p); last by rewrite ?oiter_None.
  case.
  - move=> c. rewrite -?/(steps _ _).
    rewrite [in LHS]IH [in RHS]IH /=.
    set oy1 := (steps k _).
    set oy2 := (steps k _).
    have <- : oy1 = oy2.
    { congr (steps k (_, (_, _))); move: (a) (b) (c) => [|?] [|?] [|] /=; lia. }
    case: (oy1) => [[? [? ?]]|]; last done.
    congr (Some (_, (_, _))); move: (a) (b) (c) => [|?] [|?] [|]; lia.
  - move=> c q. rewrite -?/(steps _ _).
    rewrite [in LHS]IH [in RHS]IH /=.
    set oy1 := (steps k _).
    set oy2 := (steps k _).
    have <- : oy1 = oy2.
    { congr (steps k (_, (_, _))); move: (a) (b) (c) => [|?] [|?] [|] /=; lia. }
    case: (oy1) => [[? [? ?]]|]; last done.
    congr (Some (_, (_, _))); move: (k) (a) (b) (c) => [|?] [|?] [|?] [|] /=; lia.
Qed.

Lemma mortal_K_bound K p a b :
  mortal K (p, (a, b)) <-> mortal K (p, (Nat.min K a, Nat.min K b)).
Proof.
  rewrite /mortal (shift_steps K p a b).
  by case: (steps K (p, (Nat.min K a, Nat.min K b))) => [[? [? ?]]|].
Qed.

(* path notion *)

Lemma path_length {k x} : length (path k x) = k.
Proof. by rewrite /path map_length seq_length. Qed.

Lemma In_pathE K x oy : In oy (path K x) -> exists k, k < K /\ steps k x = oy.
Proof.
  move=> /in_map_iff [k] [<-] /in_seq ?.
  exists k. split; [lia|done].
Qed.

Lemma In_pathI k x K : k < K -> In (steps k x) (path K x).
Proof.
  move=> ?. apply /in_map_iff. exists k. split; first done.
  apply /in_seq. lia.
Qed.

Lemma path_S {k x} y : step x = Some y -> path (S k) x = (Some x) :: (path k y).
Proof.
  move=> Hxy. rewrite /path /= -seq_shift map_map.
  congr cons. apply: map_ext => - ?.
  by rewrite /= obind_oiter Hxy.
Qed.

Lemma path_plus {k k' x} y : steps k x = Some y ->
  path (k+k') x = path k x ++ path k' y.
Proof.
  move=> Hxy. rewrite /path seq_app map_app /=.
  congr app.
  have ->: seq k k' = map (fun i => k+i) (seq 0 k').
  { elim: k'; first done.
    move=> k' IH. have ->: S k' = k' + 1 by lia.
    by rewrite ?seq_app IH map_app. }
  rewrite map_map. apply: map_ext => - ?.
  by move: Hxy => /steps_plus ->.
Qed.

Lemma path_S_last {k x} : path (S k) x = (path k x) ++ [steps k x].
Proof. by rewrite /path seq_S map_app. Qed.

Lemma path_loopE K x : In (steps K x) (path K x) -> 
  forall k, In (steps k x) (path K x).
Proof.
  elim: K x; first done.
  move=> K IH x. rewrite [steps _ _]/= obind_oiter.
  case Hxz: (step x) => [z|].
  - move=> H. rewrite (path_S z Hxz) /= in H. case: H.
    + move=> Hzx k. have /steps_loop_mod -> : steps (S K) x = Some x.
      { by rewrite /steps /= obind_oiter Hxz. }
      by apply /In_pathI /(Nat.mod_upper_bound k (S K)).
    + rewrite (path_S z Hxz).
      move=> /IH {}IH [|k]; first by left.
      rewrite /= obind_oiter Hxz. right. by apply: IH.
  - rewrite oiter_None. move=> /in_map_iff [k] [Hk] /in_seq HK.
    move=> k'. have [|Hkk'] : k' < k \/ k <= k' by lia.
    + move=> ?. apply: In_pathI. lia.
    + move: (Hk) => /(steps_k_monotone k') /(_ Hkk') ->.
      rewrite -Hk. apply: In_pathI. lia.
Qed.

Lemma path_loopE' K x : In (steps K x) (path K x) -> 
  forall y, reaches x y -> In (Some y) (path K x).
Proof.
  move=> /path_loopE H y [k] H'. move: (H k).
  by congr In.
Qed.

Lemma loop_bounded K x : In (steps K x) (path K x) -> bounded K x.
Proof.
  move=> /path_loopE' H. 
  exists (map (fun oy => if oy is Some y then y else x) (path K x)).
  split. { by rewrite map_length path_length. }
  move=> y /H {}H. apply /in_map_iff. by exists (Some y).
Qed.

Lemma path_noloopI k x :
  ~ In (steps k x) (path k x) -> NoDup (path (k + 1) x).
Proof.
  elim: k x.
  { move=> ??. constructor; [done| constructor]. }
  move=> k IH x.
  rewrite path_S_last /steps in_app_iff /= -/(steps k x).
  move=> /Decidable.not_or.
  have [|/IH ?] := In_dec option_Config_eq_dec (steps k x) (path k x).
  - move=> /path_loopE /(_ (S k)). tauto.
  - move=> [?] ?.
    apply /(NoDup_Add (a := steps (S k) x) (l := path (k + 1) x)).
    + rewrite path_S_last.
      have := Add_app (steps (k + 1) x) (path (k + 1) x) [].
      congr Add.
      * congr steps. lia.
      * by rewrite app_nil_r.
    + constructor; first done.
      have ->: k + 1 = S k by lia.
      rewrite path_S_last in_app_iff /=. tauto.
Qed.

Lemma mortal_bounded {K x} : steps K x = None -> bounded K x.
Proof.
  move=> HK.
  exists (map (fun oy => if oy is Some y then y else x) (path K x)).
  split. { by rewrite map_length path_length. }
  move=> y [k]. have [?|?] : k < K \/ K <= k by lia.
  - move=> Hk. apply /in_map_iff. exists (Some y).
    split; first done.
    rewrite -Hk. by apply: In_pathI.
  - by move: HK => /(steps_k_monotone k) /(_ ltac:(lia)) ->.
Qed.

Lemma In_None_pathE k x :
  In None (path k x) -> steps k x = None.
Proof.
  move=> /In_pathE [k' [?]] /(steps_k_monotone k). apply. lia.
Qed.

Lemma NoDup_not_bounded {K x y} : 
  steps K x = Some y -> NoDup (path (K + 1) x) -> not (bounded K x).
Proof.
  move=> Hxy HK [L [? HL]].
  apply: (pigeonhole (path (K+1) x) (map Some L)).
  - move=> [z|] /in_map_iff [k] [Hk] /in_seq ?.
    { apply /in_map_iff. exists z. split; first done.
      apply: HL. by exists k. }
    by move: Hk Hxy => /(steps_k_monotone K) /(_ ltac:(lia)) ->.
  - rewrite map_length path_length. lia.
  - done.
Qed.

Lemma boundedE {K x} : bounded K x ->
  (In (steps K x) (path K x)) + (steps K x = None).
Proof.
  move=> HK.
  case Hy: (steps K x) => [y|]; last by right.
  have [?|] := In_dec option_Config_eq_dec (Some y) (path K x).
  { by left. }
  rewrite -Hy. move=> /path_noloopI /NoDup_not_bounded.
  by move=> /(_ y Hy HK).
Qed.

Lemma reaches_bounded {K k x y} : steps k x = Some y -> bounded K y -> bounded (k+K) x.
Proof.
  move=> Hxy /boundedE [HK|HK].
  - apply: loop_bounded.
    move: Hxy (Hxy) => /path_plus -> /steps_plus ->.
    apply /in_app_iff. by right.
  - apply: mortal_bounded.
    by move: Hxy => /steps_plus ->.
Qed.

Lemma bounded_mortal_bound {K k x} : bounded K x -> mortal k x -> mortal K x.
Proof.
  rewrite /mortal => /boundedE + Hk.
  case; last done.
  move=> /path_loopE /(_ k).
  by rewrite Hk => /In_None_pathE.
Qed.

End Facts.
