Require Import List Arith Lia.
Import ListNotations.

Require Import Undecidability.CounterMachines.CM1.
Require Import Undecidability.CounterMachines.Util.Nat_facts.

From Coq Require Import ssreflect ssrbool ssrfun.

(* halting conditions *)
Lemma haltingP {M : Cm1} {x: Config}: 
  halting M x <-> (length M <= state x \/ value x = 0).
Proof.
  move: x => [p c] /=.
  constructor; first last.
    case; rewrite /halting /=; last by move=> ->.
    move: c => [|c]; first done. by move=> /nth_error_None ->.
  have [* | /nth_error_Some] : length M <= p \/ p < length M by lia. 
    by left.
  rewrite /halting /=.
  move: c => [|c]; first by (move=> *; right).
  case: (nth_error M p); last done.
  move=> [q n] _. move Hr: (S c mod (n + 1)) => r. 
  move: r Hr => [? [_ ?] | r _ [?]]; last by lia.
  exfalso. apply: mod_frac_neq; by eassumption.
Qed.

(* halting is monotone *)
Lemma halting_monotone {M : Cm1} {x: Config} {n m: nat} : n <= m ->
  halting M (Nat.iter n (step M) x) -> halting M (Nat.iter m (step M) x).
Proof.
  move=> ? ?. have -> : m = n + (m-n) by lia.
  rewrite iter_plus. elim: (m-n); first done.
  move=> * /=. by congruence.
Qed.

Lemma step_value_monotone (M : Cm1) (x: Config) :
  value x <= value (step M x).
Proof.
  move: x => [p [|c]] /=; first by lia.
  case: (nth_error M p) => /=; last by lia.
  move=> [j n]. move Hr: (S c mod (n + 1)) => [|r] /=; last by lia.
  have := mod_frac_lt Hr. move=> /=. by lia.
Qed.

Lemma run_value_monotone (M : Cm1) (x: Config) (n: nat) : 
  value x <= value (Nat.iter n (step M) x).
Proof.
  elim: n=> /=; first by lia.
  move=> n IH. have := step_value_monotone M (Nat.iter n (step M) x).
  by lia.
Qed.

Lemma value_monotone {M : Cm1} {x: Config} {n m: nat} : 
  n <= m -> value (Nat.iter n (step M) x) <= value (Nat.iter m (step M) x).
Proof.
  move=> ?. have ->: (m = n + (m - n)) by lia.
  rewrite iter_plus. by apply: run_value_monotone.
Qed.

Lemma inc_value_mod {M : Cm1} {p: Config} : value p < value (step M p) -> 
  exists t, nth_error M (state p) = Some t /\ ((value p) mod ((snd t)+1) = 0).
Proof.
  rewrite /step. move: p => [i [|c]] /=; first by lia.
  case: (nth_error M i) => /=; last by lia.
  move=> [j n]. move Hr: (S c mod (n + 1)) => [|r] /=; last by lia.
  move=> _. by exists (j, n).
Qed.

Lemma step_progress (M : Cm1) (x: Config) : 
  state x < length M -> 1 <= value x ->
    step M x = {| state := 1 + state x; value := value x |} \/
    value x < value (step M x).
Proof.
  move=> ? ?. rewrite /step. have ->: value x = S (value x - 1) by lia.
  move Ho: (nth_error M (state x)) => o. case: o Ho; first last.
    move /nth_error_None. by lia.
  move=> [j n] _. case H: (S (value x - 1) mod (n + 1)); last by left.
  right => /=. by apply: mod_frac_lt.
Qed.

Definition config_weight (M: Cm1) : Config -> nat :=
  fun '{| state := p; value := v |} => p + length M * v.

(* the weight of a configuration strictly increases until the counter machine halts *)
Lemma config_weight_step_monotone {M: Cm1} {x: Config} :
  not (halting M x) -> config_weight M x < config_weight M (step M x).
Proof.
  move=> Hx. suff: not (config_weight M (step M x) <= config_weight M x) by lia.
  move: x Hx => [p v].
  rewrite /config_weight /=. case: v => [|v].
    move=> + /ltac:(exfalso). by apply.
  move Ho: (nth_error M p) => o. case: o Ho; first last.
    move=> Hp + /ltac:(exfalso). apply. move=> /=. by rewrite Hp.
  move=> [j n] Hp ?. case Hr: (S v mod (n + 1)); last by lia.
  have := mod_frac_lt Hr.
  have : p < length M.
    apply /nth_error_Some. by rewrite Hp.
  by nia.
Qed.

Lemma config_weight_run_monotone {M: Cm1} {x: Config} {n: nat} :
  not (halting M (Nat.iter n (step M) x)) -> config_weight M x < config_weight M (Nat.iter (1+n) (step M) x).
Proof.
  elim: n.
    by move /config_weight_step_monotone.
  move=> n IH HSn.
  have /IH : not (halting M (Nat.iter n (step M) x)).
    move=> Hn. apply: HSn. move: Hn. apply: halting_monotone. by lia.
  have := config_weight_step_monotone HSn.
  move=> /=. by lia.
Qed.

(* a non-terminating run of a counter machine has no duplicates *)
Theorem acyclicity {M: Cm1} {n: nat} {x: Config} : 
  not (halting M (Nat.iter n (step M) x)) -> 
  NoDup (map (fun i => Nat.iter i (step M) x) (seq 0 (2+n))).
Proof.
  elim: n.
    move=> /= Hx.
    apply: NoDup_cons; first by case.
    by apply: NoDup_cons; [ case | apply: NoDup_nil ].
  move=> n IH HSn.
  have /IH : not (halting M (Nat.iter n (step M) x)).
    move=> Hn. apply: HSn. move: Hn. apply: halting_monotone. by lia.
  have ->: seq 0 (2 + S n) = seq 0 (2 + n) ++ [2 + n].
    have ->: 2 + S n = (2 + n) + 1 by lia. by rewrite [seq 0 (2 + n + 1)] seq_app.
  rewrite map_app.
  set f := (fun i : nat => Nat.iter i (step M) x).
  have : Add (f (2+n)) (map f (seq 0 (2 + n)) ++ []) (map f (seq 0 (2 + n)) ++ map f [2 + n]) by apply: Add_app.
  rewrite app_nil_r. move /(@NoDup_Add Config) => H Hfn.
  apply /H. constructor; first done.
  rewrite in_map_iff. move=> [i]. rewrite in_seq /f. move=> [+ ?].
  have ->: 2 + n = i + (1 + (1+n - i)) by lia.
  rewrite iter_plus. set x' := Nat.iter i (step M) x.
  move=> Hx'. 
  suff: config_weight M x' < config_weight M (Nat.iter (1 + (1+n - i)) (step M) x').
    rewrite -Hx'. by lia.
  apply: config_weight_run_monotone. subst x'.
  rewrite -iter_plus. by have ->: i + (1 + n - i) = S n by lia.
Qed. 
