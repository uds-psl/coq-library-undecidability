(*
  Autor(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  Decision Procedure(s):
    Reversible Two-counter Machine Halting (CM2_REV_HALT)
*)

Require Import List PeanoNat Lia Operators_Properties.
Import ListNotations.
Require Import Undecidability.CounterMachines.CM2.
From Undecidability.CounterMachines.Util Require Import Facts CM2_facts.
Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".
Set Default Proof Using "Type".

Section Construction.
Variable M : Cm2.
Variable HM : reversible M.

(* partial two counter machine step function without jumps *)
Definition step' (x: Config) : option Config :=
  match nth_error M (state x) with
  | None => None (* halting configuration *)
  | Some (inc b) => (* increase counter, goto next state*)
    Some (1 + (state x), ((if b then 0 else 1) + (value1 x), (if b then 1 else 0) + (value2 x)))
  | Some (dec b y) => (* halt on jump *)
    if b then
      if value2 x is 0 then Some (1 + (state x), (value1 x, 0)) else None
    else
      if value1 x is 0 then Some (1 + (state x), (0, value2 x)) else None
  end.

Definition steps' n x : option Config :=
  Nat.iter n (obind step') (Some x).

#[local] Notation step := (CM2.step M).
#[local] Notation steps := (CM2.steps M).
#[local] Notation terminating := (CM2.terminating M).
#[local] Notation non_terminating := (CM2_facts.non_terminating M).
#[local] Notation reaches := (CM2.reaches M).
#[local] Notation reaches_plus := (CM2_facts.reaches_plus M).

Definition reaches' x y := exists k, steps' k x = Some y.

(* step includes step' *)
Lemma step'_incl x y : step' x = Some y -> step x = Some y.
Proof.
  rewrite /step' /step. case: (nth_error M (state x)); last done.
  case; first done.
  move=> [] q; [by case: (value2 x)|by case: (value1 x)].
Qed.

(* steps includes steps' *)
Lemma steps'_incl k x y : steps' k x = Some y -> steps k x = Some y.
Proof.
  elim: k y; first done.
  move=> k /=. case: (steps' k x) => [y|]; last done.
  move=> /(_ y erefl) -> /=. by apply: step'_incl.
Qed.

Corollary reaches'_incl {x y} : reaches' x y -> reaches x y.
Proof. move=> [k /steps'_incl ?]. by exists k. Qed.

Opaque nth_error.
Arguments nth_error_In {_ _ _ _}.

(* key lemma on the way to ensure that equivalent configurations behave identically
   every steps' computation without jumps increases the starting configuration
   (a > 0 -> value1 x > 0), (b > 0 -> value2 x > 0) in the same way *)
Lemma steps'E k x y : steps' k x = Some y ->
  exists n m, value1 y = value1 x + n /\ value2 y = value2 x + m /\ 
    forall a b, (a > 0 -> value1 x > 0) -> (b > 0 -> value2 x > 0) ->
      steps' k (state x, (a, b)) = Some (state y, (a + n, b + m)).
Proof.
  elim: k x y.
  { move=> x y [<-]. exists 0, 0. do 2 (split; first by lia).
    move=> a b ?? /=. by rewrite ?Nat.add_0_r. }
  move=> k IH x y /=.
  case Hx': (steps' k x) => [x'|]; last done.
  move: Hx' => /IH [n] [m] [Hax'] [Hbx'] {}IH /=.
  rewrite /(step' x'). case Hi: (nth_error M (state x')) => [i|]; last done.
  move: i Hi => [].
  - move=> c Hi [<-] /=. exists ((if c then 0 else 1) + n), ((if c then 1 else 0) + m).
    split; first by lia. split; first by lia.
    move=> a b Ha Hb. rewrite IH; [done|done|].
    rewrite /= /step' Hi /=. congr Some. congr pair. congr pair; lia.
  - move=> [] q Hi.
    + case H'bx': (value2 x') => [|bx']; last done.
      move=> [<-] /=. exists n, 0.
      split; first by lia. split; first by lia.
      move=> a b ??. rewrite IH; [done|done|].
      rewrite /step' /= Hi. have ->: b + m = 0 by lia. 
      congr Some. congr pair. congr pair; lia.
    + case H'ax': (value1 x') => [|ax']; last done.
      move=> [<-] /=. exists 0, m.
      split; first by lia. split; first by lia.
      move=> a b ??. rewrite IH; [done|done|].
      rewrite /step' /= Hi. have ->: a + n = 0 by lia.
      congr Some. congr pair. congr pair; lia.
Qed.

Corollary reaches'E x y : reaches' x y ->
  exists n m, value1 y = value1 x + n /\ value2 y = value2 x + m /\ 
    forall a b, (a > 0 -> value1 x > 0) -> (b > 0 -> value2 x > 0) ->
      reaches' (state x, (a, b)) (state y, (a + n, b + m)).
Proof.
  move=> [k] /steps'E [n] [m] [?] [?] H.
  exists n, m. split; [done|split; [done|]].
  move=> ????. exists k. by apply: H.
Qed.

Lemma step'_inc_state x y :
  step' x = Some y -> state y = 1 + (state x).
Proof.
  rewrite /step'. case: (nth_error M (state x)); last done.
  move=> [].
  - by move=> c [/(f_equal state)] /= <-.
  - move: (value1 x) (value2 x) => [|?] [|?] [] _ //.
    all: by move=> [/(f_equal state)] /= <-.
Qed.

Lemma target_index p c q : nth_error M p = Some (dec c q) -> q = 0 \/ length M < q.
Proof using HM.
  move=> Hp. suff: not (q = S (q - 1) /\ (q - 1 < length M)) by lia.
  move=> [Hq /nth_error_Some].
  case Hi: (nth_error M (q - 1)) => [i|]; last done.
  move=> _.
  move: i c Hp Hi => [].
  - move=> [] [] Hp Hi.
    + have := HM (p, (2, 2)) (q - 1, (2, 0)) (q, (2, 1)).
      rewrite /step /= Hp Hi -Hq. by move=> /(_ erefl erefl) [].
    + have := HM (p, (2, 2)) (q - 1, (1, 1)) (q, (1, 2)).
      rewrite /step /= Hp Hi -Hq. by move=> /(_ erefl erefl) [].
    + have := HM (p, (2, 2)) (q - 1, (1, 1)) (q, (2, 1)).
      rewrite /step /= Hp Hi -Hq. by move=> /(_ erefl erefl) [].
    + have := HM (p, (2, 2)) (q - 1, (0, 2)) (q, (1, 2)).
      rewrite /step /= Hp Hi -Hq. by move=> /(_ erefl erefl) [].
  - move=> t ? [] Hp Hi.
    + have := HM (p, (0, 1)) (q - 1, (0, 0)) (q, (0, 0)).
      rewrite /step /= Hp Hi -Hq.
      by move: t {Hi} => [] /(_ erefl erefl) [].
    + have := HM (p, (1, 0)) (q - 1, (0, 0)) (q, (0, 0)).
      rewrite /step /= Hp Hi -Hq.
      by move: t {Hi} => [] /(_ erefl erefl) [].
Qed.

Corollary reaches'I x : 
  { y | reaches' x y /\ 
    (if step y is Some z then state z = 0 \/ length M <= state z else True) }.
Proof using HM.
  move Hn: (length M - state x) => n. elim: n x Hn.
  { move=> x ?. exists x. split; first by exists 0.
    rewrite /step. by have /nth_error_None -> : (length M <= state x) by lia. }
  move=> n IH x ?. case Hy: (step' x) => [y|].
  - move: (Hy) => /step'_inc_state ?.
    have /IH : (length M - state y = n) by lia.
    move=> [z] [Hyz ?]. exists z. split; last done.
    move: Hyz => [k Hk]. exists (1+k).
    by rewrite /steps' iter_plus /= Hy.
  - exists x. split; first by exists 0.
    move: Hy. rewrite /step' /step.
    case Hi: (nth_error M (state x)) => [i|]; last done.
    case: i Hi; first done.
    move=> [] q.
    + move: (value2 x) => [|b]; first done.
      move=> /target_index /=. lia.
    + move: (value1 x) => [|a]; first done.
      move=> /target_index /=. lia.
Qed.

(* step with counters of same positivity *)
Lemma step_parallel {x y} x' :
  step x = Some y ->
  (state x = state x' /\ (value1 x > 0 <-> value1 x' > 0) /\ (value2 x > 0 <-> value2 x' > 0)) ->
  exists y', step x' = Some y' /\ 
  state y = state y' /\ 
  value1 x + value1 y' = value1 x' + value1 y /\
  value2 x + value2 y' = value2 x' + value2 y.
Proof.
  move=> + [Hx']. rewrite /step -Hx'. case: (nth_error M (state x)); last done.
  move=> [].
  { move=> c [<-] ?. eexists. split; [reflexivity|move=> /=; lia]. }
  move=> [] p.
  - case: (value2 x) => [|?] [<-] ?.
    + have ->: value2 x' = 0 by lia.
      eexists. split; [reflexivity|move=> /=; lia].
    + have ->: value2 x' = S ((value2 x') - 1) by lia.
      eexists. split; [reflexivity|move=> /=; lia].
  - case: (value1 x) => [|?] [<-] ?.
    + have ->: value1 x' = 0 by lia.
      eexists. split; [reflexivity|move=> /=; lia].
    + have ->: value1 x' = S ((value1 x') - 1) by lia.
      eexists. split; [reflexivity|move=> /=; lia].
Qed.

(* if (1, 1) f->>t-> (0, 1 + m), then (a, b) t->> (0, a * m + b) *)
Lemma dec_a_0 x m : reaches' (0, (1, 1)) x -> 
  step x = Some (0, (0, 1 + m)) ->
  forall a b, reaches (0, (a, b)) (0, (0, a * m + b)).
Proof.
  move=> H1x H2x. elim.
  - move=> b. by exists 0.
  - move=> a IH b. move: H1x => /reaches'E [n'] [m'] /= [Hax] [Hbx].
    move=> /(_ (S a) b ltac:(lia) ltac:(lia)).
    move=> /reaches'_incl /reaches_trans. apply.
    have ->: m + a * m + b = a * m + (m + b) by lia.
    apply: (reaches_trans _ (IH (m + b))).
    exists 1. move: H2x. rewrite /= /step. case: (nth_error M (state x)); last done.
    move=> [].
    + move=> c []. lia.
    + move=> [] q.
      * move: (value2 x) Hbx => [|bx]; first by lia.
        rewrite Hax. move=> ? []. by lia.
      * move: (value1 x) Hax => [|ax]; first by lia.
        move=> ? [? ? ?] /=. congr (Some (_, (_, _))); lia.
Qed.

(* if (1, 1) f->>t-> (1 + n, 0), then (a, b) t->> (b * n + a, 0) *)
Lemma dec_b_0 x n : reaches' (0, (1, 1)) x -> 
  step x = Some (0, (1 + n, 0)) ->
  forall a b, reaches (0, (a, b)) (0, (b * n + a, 0)).
Proof.
  move=> H1x H2x a b. elim: b a.
  - move=> a. by exists 0.
  - move=> b IH a. move: H1x => /reaches'E [n'] [m'] /= [Hax] [Hbx].
    move=> /(_ a (S b) ltac:(lia) ltac:(lia)).
    move=> /reaches'_incl /reaches_trans. apply.
    have ->: n + b * n + a = b * n + (n + a) by lia.
    apply: (reaches_trans _ (IH (n + a))).
    exists 1. move: H2x. rewrite /= /step. case: (nth_error M (state x)); last done.
    move=> [].
    + move=> c [] /=. lia.
    + move=> [] q.
      * move: (value2 x) Hbx => [|bx]; first by lia.
        move=> ? [? ? ?] /=. congr (Some (_, (_, _))); lia.
      * move: (value1 x) Hax => [|ax]; first by lia.
        rewrite Hbx. move=> ? []. by lia.
Qed.

(* if (1, 1) ->> (S a, S b), then (a', b') does not terminate *)
Lemma dec_loop x n m : reaches' (0, (1, 1)) x -> 
  step x = Some (0, (1 + n, 1 + m)) ->
  forall a b, non_terminating (0, (a, b)).
Proof.
  move=> [k Hk] Hx a b k' /(steps_k_monotone (k' * S k)) /(_ ltac:(lia)).
  elim: k' a b; first done.
  move=> k' IH a b. have ->: S k' * S k = (k + 1) + (k' * S k) by lia.
  have : steps (k + 1) (0, (a, b)) = Some (0, (n + a, b + m)).
  {
    move: Hk => /steps'E [n'] [m'] /= [Hax] [Hbx].
    move=> /(_ a b ltac:(lia) ltac:(lia)).
    move=> /steps'_incl /steps_plus ->.
    move: Hx. rewrite /= /step. case: (nth_error M (state x)); last done.
    move=> [].
    - move=> c [] /= -> ??. congr (Some (_, (_, _))); lia.
    - move=> [] q.
      + move: (value2 x) Hbx => [|bx] Hbx; first done.
        move=> [->] ?? /=.
        have ->: b + m' = S (b + m) by lia.
        congr (Some (_, (_, _))); lia.
      + move: (value1 x) Hax => [|ax] Hax; first done.
        move=> [->] ?? /=.
        have ->: a + n' = S (n + a) by lia.
        congr (Some (_, (_, _))); lia.
    }
    move=> /steps_plus ->. by apply: IH.
Qed.

Lemma reaches'_None_terminating x y :
  reaches' x y -> step y = None ->
  forall a b, (a > 0 -> value1 x > 0) -> (b > 0 -> value2 x > 0) -> 
    terminating (state x, (a, b)).
Proof.
  move=> Hx /step_None Hy a b ? ?.
  move: Hx => /reaches'E [n] [m] /= [?] [?].
  move=> /(_ a b ltac:(lia) ltac:(lia)) /reaches'_incl.
  move=> /reaches_terminating. apply.
  exists 1. by apply /step_None.
Qed.

Lemma reaches'_Some_terminating x y z :
  reaches' x y -> step y = Some z -> length M <= state z ->
  forall a b, (value1 x > 0 <-> a > 0) -> (value2 x > 0 <-> b > 0) -> 
    terminating (state x, (a, b)).
Proof.
  move=> Hx Hy Hz a b ? ?.
  move: Hx => /reaches'E [n] [m] /= [?] [?].
  move=> /(_ a b ltac:(lia) ltac:(lia)) /reaches'_incl.
  move: Hy => /(step_parallel (state y, (a + n, b + m))) /= /(_ ltac:(lia)).
  move=> [[pz [az bz]]] /= [?] [?] ?. subst pz.
  move=> /reaches_terminating. apply.
  apply: reaches_terminating; first by (exists 1; eassumption).
  exists 1. by apply /step_None /nth_error_None.
Qed.

Lemma terminating_orI p a b x y : 
  reaches' (p, (S a, S b)) x ->
  step x = Some y ->
  length M <= state y ->
  (forall a', terminating (p, (S a', 0))) + (forall b', terminating (p, (0, S b'))).
Proof.
  rewrite /(step x). case Hi: (nth_error M (state x)) => [i|]; last done.
  move: i Hi => [].
  { (* inc instruction *)
    move=> c Hx H'x [/(f_equal state) /= H'y] ?. left=> a'.
    move: H'x => /reaches'E [n] [m] /= [?] [?].
    move=> /(_ (S a') 0 ltac:(lia) ltac:(lia)).
    move=> /reaches'_incl /reaches_terminating. apply.
    exists 2 => /=. rewrite /step /= Hx /=.
    by have /nth_error_None -> : length M <= S (state x) by lia. }
  (* dec instruction *)
  move=> [] q Hx.
  - move=> +++ /ltac:(right).
    move=> /reaches'E [n] [m] /= [->] [->] Hk.
    move=> [/(f_equal state)] /= <- ?.
    move=> b'. move: Hk => /(_ 0 (S b') ltac:(lia) ltac:(lia)).
    move=> /reaches'_incl /reaches_terminating. apply.
    exists 2. rewrite /= /step /= Hx /=.
    by have /nth_error_None -> : length M <= q by lia.
  - move=> +++ /ltac:(left).
    move=> /reaches'E [n] [m] /= [->] [->] Hk.
    move=> [/(f_equal state)] /= <- ?.
    move=> a'. move: Hk => /(_ (S a') 0 ltac:(lia) ltac:(lia)).
    move=> /reaches'_incl /reaches_terminating. apply.
    exists 2. rewrite /= /step /= Hx /=.
    by have /nth_error_None -> : length M <= q by lia.
Qed.

Lemma transition_loop a b: 
  (forall a' b', (a > 0 <-> a' > 0) -> (b > 0 <-> b' > 0) -> 
     exists a'' b'', reaches_plus (0, (a', b')) (0, (a'', b'')) /\
       (a' > 0 <-> a'' > 0) /\ (b' > 0 <-> b'' > 0)) ->
  non_terminating (0, (a, b)).
Proof.
  move=> H. apply: (reaches_plus_invariant_loop 
    (fun '(p', (a', b')) => p' = 0 /\ (a > 0 <-> a' > 0) /\ (b > 0 <-> b' > 0))); last by lia.
  move=> [px [ax bx]] [->] H'.
  move: (H') => [/H] {}H /H [ax'] [bx'] [? ?].
  exists (0, (ax', bx')). split; [done|lia].
Qed.

(* not (1, 1) f->>t-> (0, 0) *)
Lemma not_transition_1_1_to_0_0 x : reaches' (0, (1, 1)) x -> step x <> Some (0, (0, 0)).
Proof.
  move=> /reaches'E [n] [m] /= [H1x] [H2x] _.
  rewrite /step. case: (nth_error M (state x)); last done.
  move=> [].
  - move=> ? [] ?. lia.
  - move=> [] ?; rewrite ?H1x ?H2x; case; lia.
Qed.

Lemma dec_stepI {x y} : step x = Some y -> state y = 0 -> 
  (value1 y < value1 x -> In (dec false 0) M) /\
  (value2 y < value2 x -> In (dec true 0) M).
Proof.
  rewrite /step. case Hi: (nth_error M (state x)) => [i|]; last done.
  case: i Hi.
  - by move=> [] _ [<-].
  - move=> [] ? /nth_error_In Hi [<-].
    + case: (value2 x) => [|b]; first done.
      move=> /= ?. subst. split; [lia|done].
    + case: (value1 x) => [|a]; first done.
      move=> /= ?. subst. split; [done|lia].
Qed.

Lemma rev_dec_unique : In (dec false 0) M -> In (dec true 0) M -> False.
Proof using HM.
  move=> /(@In_nth_error Instruction) [p Hp] /(@In_nth_error Instruction) [q Hq].
  suff: (p, (1, 0)) = (q, (0, 1)) by case.
  have := (HM (p, (1, 0)) (q, (0, 1)) (0, (0, 0))).
  rewrite /step Hp Hq. by apply.
Qed.

(* uniform transition from equivalence class (0, 0) *)
Lemma transition_0_0 :
  (* terminating equivalence class (0, 0) *)
  (terminating (0, (0, 0))) +
  (* non-terminating equivalence class (0, 0) *)
  (non_terminating (0, (0, 0))) +
  (* uniform transition to equivalence class (S a, 0) *)
  (exists a', reaches (0, (0, 0)) (0, (S a', 0))) +
  (* uniform transition to equivalence class (0, S b) *)
  (exists b', reaches (0, (0, 0)) (0, (0, S b'))) +
  (* uniform transition to equivalence class (S a, S b) *)
  (exists a' b', reaches (0, (0, 0)) (0, (S a', S b'))).
Proof using HM.
  have [y [/reaches'_incl Hk]] := reaches'I (0, (0, 0)).
  case Hz: (step y) => [[pz [az bz]]|]; first last.
  { (* termination *)
    move=> _. do 4 left.
    move: Hk => /reaches_terminating. apply.
    by exists 1. }
  have H0z : reaches_plus (0, (0, 0)) (pz, (az, bz)).
  { apply: reaches_reaches_plus; [by eassumption|exists 1].
    split; [lia|done]. }
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* termination *)
    move=> /nth_error_None H'z. do 4 left.
    move: H0z => /reaches_plus_incl /reaches_terminating. apply.
    exists 1. by apply /step_None. }
  move=> /= ?. subst pz. move: az bz H0z {Hz} => [|az] [|bz] H0z.
  - (* non-termination *)
    do 3 left. right. by apply: reaches_plus_self_loop.
  - (* transition to (0, S b) *)
    do 1 left. right. exists bz. by apply /reaches_plus_incl.
  - (* transition to (S a, 0) *)
    do 2 left. right. exists az. by apply /reaches_plus_incl.
  - (* transition to (S a, S b) *)
    right. exists az, bz. by apply /reaches_plus_incl.
Qed.

(* uniform transition from equivalence class (S a, 0) *)
Lemma transition_Sa_0 :
  (* terminating equivalence class (S a, 0) *)
  (forall a, terminating (0, (S a, 0))) +
  (* non-terminating equivalence class (S a, 0) *)
  (forall a, non_terminating (0, (S a, 0))) +
  (* uniform transition to equivalence class (0, 0) *)
  (forall a, reaches (0, (S a, 0)) (0, (0, 0))) +
  (* uniform transition to equivalence class (0, S b) *)
  (forall a, exists b', reaches (0, (S a, 0)) (0, (0, S b'))) +
  (* uniform transition to equivalence class (S a, S b) *)
  (forall a, exists a' b', reaches (0, (S a, 0)) (0, (S a', S b'))).
Proof using HM.
  have [x' [Hx']] := reaches'I (0, (1, 0)).
  case H'x': (step x') => [y'|]; first last.
  { (* case: (1, 0) f->> HALT; uniform termination *)
    move=> _. do 4 left. move=> a. move: Hx' => /reaches'_None_terminating.
    apply=> /=; by [assumption|lia]. }
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* case: (1, 0) f->>t-> HALT; uniform termination *)
    move: Hx' H'x' => /reaches'_Some_terminating H /H {}H /H {}H.
    do 4 left. move=> a. apply: H => /=; lia. }
  move: y' H'x' => [py' [ay' [|by']]] + /= Hy'; subst py'.
  { (* case: (1, 0) f->>t-> (_, 0) *)
    move: ay' => [|ay'] H'x'.
    - (* case: (1, 0) f->>t-> (0, 0) uniform transition to (0, 0) *)
      do 2 left. right. move=> a. elim: (S a); first by exists 0.
      move=> {}a IH. move: Hx' => /reaches'E.
      move=> [n'] [m'] /= [Hax] [Hbx] /(_ (S a) 0 ltac:(lia) ltac:(lia)).
      move=> /reaches'_incl Hk. apply: (reaches_trans Hk).
      move: H'x' => /(step_parallel (state x', (S a + n', m'))) /= /(_ ltac:(lia)).
      move=> [[pz [az bz]]] /= [/step_reaches] H [?] ?.
      apply: (reaches_trans H). subst pz.
      move: IH. congr reaches. congr (_, (_, _)); lia.
    - (* non-termination *)
      do 3 left. right. move=> a. apply: transition_loop => a' b' ??.
      move: Hx' H'x' => /reaches'E [n] [m] /= [?] [?].
      move=> /(_ a' b' ltac:(lia) ltac:(lia)) /reaches'_incl Hk'.
      move=> /(step_parallel (state x', (a' + n, b' + m))) /=.
      move=> /(_ ltac:(lia)) [[pz [az bz]]] [/step_reaches_plus Hz] /= [? ?].
      subst pz. exists az, bz. split; last by lia.
      apply: reaches_reaches_plus; by eassumption. }
  move: ay' => [|ay'] H'x'; first last.
  { (* case: (1, 0) f->>t-> (S a, S b) uniform transition to (S a, S b) *)
    right. move=> a.
    move: Hx' => /reaches'E [n] [m] /= [Hax'] [Hbx'].
    move=> /(_ (S a) 0 ltac:(lia) ltac:(lia)) /reaches'_incl.
    move: H'x' => /(step_parallel (state x', (S a + n, m))) /=.
    move=> /(_ ltac:(lia)) [[pz' [az' bz']]] /= [/step_reaches Hz'] [? ?] Hx'.
    exists (az' - 1), (bz' - 1). apply /(reaches_trans Hx').
    move: Hz'. congr reaches. congr (_, (_, _)); lia. }
  (* case: (1, 0) f->>t-> (0, S b) *)
  have := reaches'I (0, (1, 1)).
  move=> [x] [Hx]. case H'x: (step x) => [y|]; first last.
  { (* case: (1, 1) f->> HALT; uniform termination *)
    move=> _. do 4 left. move=> a. move: Hx => /reaches'_None_terminating.
    apply => /=; by [assumption|lia]. }
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* case: (1, 1) f->>t-> HALT; uniform termination *)
    move=> Hy. move: (Hx) (H'x) (Hy) => /terminating_orI => H /H {}H /H {H} [?|HS]; first by (do 4 left).
    do 4 left. move=> [|a].
    { apply: (reaches_terminating _ (HS by')).
      by apply: (reaches_trans (reaches'_incl Hx') (step_reaches H'x')). }
    move: Hx' => /reaches'E [n] [m] /= [?] [?].
    move=> /(_ (S (S a)) 0 ltac:(lia) ltac:(lia)).
    move=> /reaches'_incl /reaches_terminating. apply.
    move: H'x' => /(step_parallel (state x', (S (S a) + n, m))) /=.
    move=> /(_ ltac:(lia)) [[pz' [az' bz']]] /= [Hz'] [?] ?.
    move: Hz' => /step_reaches /reaches_terminating. apply.
    subst pz'. move: Hx => /reaches'E [n'] [m'] /= [?] [?].
    move=> /(_ az' bz' ltac:(lia) ltac:(lia)).
    move=> /reaches'_incl /reaches_terminating. apply.
    move: H'x => /(step_parallel (state x, (az' + n', bz' + m'))) /=.
    move=> /(_ ltac:(lia)) [z] [Hz] [?] ?.
    move: Hz => /step_reaches /reaches_terminating. apply.
    exists 1. apply /step_None /nth_error_None. lia. }
  (* case (1, 1) f->>t-> (a, b) at index 0 *)
  move=> H0y. move Ha'y: (value1 y) => a'y. move Hb'y: (value2 y) => b'y.
  move: b'y Hb'y => [|b'y] H2y.
  { (* case: (1, 1) f->>t-> (_, 0) impossible *)
    exfalso. apply: rev_dec_unique.
    + apply: (proj1 (dec_stepI H'x' ltac:(done))).
      move: Hx' => /reaches'E [n] [m] /= [?] [?]. lia.
    + apply: (proj2 (dec_stepI H'x H0y)).
      move: Hx => /reaches'E [n] [m] /= [?] [?]. lia. }
  move: a'y Ha'y => [|a'y] H1y.
  - (* case: (1, 1) f->>t-> (0, S b') uniform transition to (0, Sb') *)
    do 1 left. right. move=> a.
    move: Hx' => /reaches'E [n] [m] /= [?] [?].
    move=> /(_ (S a) 0 ltac:(lia) ltac:(lia)) /reaches'_incl Hk'.
    move: H'x' => /(step_parallel (state x', (S a + n, m))) /=.
    move=> /(_ ltac:(lia)) [y'] [/step_reaches Hy'] [H0y'] ?.
    move: Hx H'x => /dec_a_0 H. rewrite (Config_eta y) H0y H1y H2y.
    move=> /H {H} => /(_ a (S by')) Hk''.
    exists (a * b'y + by').
    apply /(reaches_trans Hk') /(reaches_trans Hy').
    rewrite (Config_eta y').
    move: Hk''. congr reaches; congr (_, (_, _)); lia.
  - (* case: (1, 1) f->>t-> (S a', S b') loop *)
    do 3 left. right. move=> a. apply: dec_loop; [eassumption|].
    by rewrite H'x (Config_eta y) H0y H1y H2y.
Qed.

(* uniform transition from equivalence class (0, S b) *)
Lemma transition_0_Sb :
  (* terminating equivalence class *)
  (forall b, terminating (0, (0, S b))) +
  (* non-terminating equivalence class*)
  (forall b, non_terminating (0, (0, S b))) +
  (* uniform transition to equivalence class (0, 0) *)
  (forall b, reaches (0, (0, S b)) (0, (0, 0))) +
  (* uniform transition to equivalence class (S a, 0) *)
  (forall b, exists a', reaches (0, (0, S b)) (0, (S a', 0))) +
  (* uniform transition to equivalence class (S a, S b) *)
  (forall b, exists a' b', reaches (0, (0, S b)) (0, (S a', S b'))).
Proof using HM.
  have [x' [Hx']] := reaches'I (0, (0, 1)).
  case H'x': (step x') => [y'|]; first last.
  { (* case: (0, 1) f->> HALT; uniform termination *)
    move=> _. do 4 left. move=> b. move: Hx' => /reaches'_None_terminating.
    apply=> /=; by [assumption|lia]. }
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* case: (0, 1) f->>t-> HALT; uniform termination *)
    move: Hx' H'x' => /reaches'_Some_terminating H /H {}H /H {}H.
    do 4 left. move=> b. apply: H => /=; lia. }
  move: y' H'x' => [py' [[|ay'] by']] + /= Hy'; subst py'.
  { (* case: (0, 1) f->>t-> (0, _) *)
    move: by' => [|by'] H'x'.
    - (* case: (0, 1) f->>t-> (0, 0) uniform transition to (0, 0) *)
      do 2 left. right. move=> b. elim: (S b); first by exists 0. 
      move=> {}b IH. move: Hx' => /reaches'E.
      move=> [n'] [m'] /= [Hax] [Hbx] /(_ 0 (S b) ltac:(lia) ltac:(lia)).
      move=> /reaches'_incl Hk. apply: (reaches_trans Hk).
      move: H'x' => /(step_parallel (state x', (n', S b + m'))) /= /(_ ltac:(lia)).
      move=> [[pz [az bz]]] /= [/step_reaches] H [?] ?.
      apply: (reaches_trans H). subst pz.
      move: IH. congr reaches. congr (_, (_, _)); lia.
    - (* non-termination *)
      do 3 left. right. move=> b. apply: transition_loop => a' b' ??.
      move: Hx' H'x' => /reaches'E [n] [m] /= [?] [?].
      move=> /(_ a' b' ltac:(lia) ltac:(lia)) /reaches'_incl Hk'.
      move=> /(step_parallel (state x', (a' + n, b' + m))) /=.
      move=> /(_ ltac:(lia)) [[pz [az bz]]] [/step_reaches_plus Hz] /= [? ?].
      subst pz. exists az, bz. split; last by lia.
      apply: reaches_reaches_plus; by eassumption. }
  move: by' => [|by'] H'x'; first last.
  { (* case: (0, 1) f->>t-> (S a, S b) uniform transition to (S a, S b) *)
    right. move=> b.
    move: Hx' => /reaches'E [n] [m] /= [Hax'] [Hbx'].
    move=> /(_ 0 (S b) ltac:(lia) ltac:(lia)) /reaches'_incl.
    move: H'x' => /(step_parallel (state x', (n, S b + m))) /=.
    move=> /(_ ltac:(lia)) [[pz' [az' bz']]] /= [/step_reaches Hz'] [? ?] Hx'.
    exists (az' - 1), (bz' - 1). apply /(reaches_trans Hx').
    move: Hz'. congr reaches. congr (_, (_, _)); lia. }
  (* case: (0, 1) f->>t-> (S a, 0) *)
  have := reaches'I (0, (1, 1)).
  move=> [x] [Hx]. case H'x: (step x) => [y|]; first last.
  { (* case: (1, 1) f->> HALT; uniform termination *)
    move=> _. do 4 left. move=> b. move: Hx => /reaches'_None_terminating.
    apply => /=; by [assumption|lia]. }
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* case: (1, 1) f->>t-> HALT; uniform termination *)
    move=> Hy. move: (Hx) (H'x) (Hy) => /terminating_orI => H /H {}H /H {H} [HS|?]; last by (do 4 left).
    do 4 left. move=> [|b].
    { apply: (reaches_terminating _ (HS ay')).
      by apply: (reaches_trans (reaches'_incl Hx') (step_reaches H'x')). }
    move: Hx' => /reaches'E [n] [m] /= [?] [?].
    move=> /(_ 0 (S (S b)) ltac:(lia) ltac:(lia)).
    move=> /reaches'_incl /reaches_terminating. apply.
    move: H'x' => /(step_parallel (state x', (n, S (S b) + m))) /=.
    move=> /(_ ltac:(lia)) [[pz' [az' bz']]] /= [Hz'] [?] ?.
    move: Hz' => /step_reaches /reaches_terminating. apply.
    subst pz'. move: Hx => /reaches'E [n'] [m'] /= [?] [?].
    move=> /(_ az' bz' ltac:(lia) ltac:(lia)).
    move=> /reaches'_incl /reaches_terminating. apply.
    move: H'x => /(step_parallel (state x, (az' + n', bz' + m'))) /=.
    move=> /(_ ltac:(lia)) [z] [Hz] [?] ?.
    move: Hz => /step_reaches /reaches_terminating. apply.
    exists 1. apply /step_None /nth_error_None. lia. }
  (* case (1, 1) f->>t-> (a, b) at index 0 *)
  move=> H0y. move Ha'y: (value1 y) => a'y. move Hb'y: (value2 y) => b'y.
  move: a'y Ha'y => [|a'y] H1y.
  { (* case: (1, 1) f->>t-> (0, _) impossible *)
    exfalso. apply: rev_dec_unique.
    + apply: (proj1 (dec_stepI H'x H0y)).
      move: Hx => /reaches'E [n] [m] /= [?] [?]. lia.
    + apply: (proj2 (dec_stepI H'x' ltac:(done))).
      move: Hx' => /reaches'E [n] [m] /= [?] [?]. lia. }
  move: b'y Hb'y => [|b'y] H2y.
  - (* case: (1, 1) f->>t-> (S a', 0) uniform transition to (S a', 0') *)
    do 1 left. right. move=> b.
    move: Hx' => /reaches'E [n] [m] /= [?] [?].
    move=> /(_ 0 (S b) ltac:(lia) ltac:(lia)) /reaches'_incl Hk'.
    move: H'x' => /(step_parallel (state x', (n, S b + m))) /=.
    move=> /(_ ltac:(lia)) [y'] [/step_reaches Hy'] [H0y'] ?.
    move: Hx H'x => /dec_b_0 H. rewrite (Config_eta y) H0y H1y H2y.
    move=> /H {H} => /(_ (S ay') b) Hk''.
    exists (b * a'y + ay').
    apply /(reaches_trans Hk') /(reaches_trans Hy').
    rewrite (Config_eta y').
    move: Hk''. congr reaches; congr (_, (_, _)); lia.
  - (* case: (1, 1) f->>t-> (S a', S b') loop *)
    do 3 left. right. move=> b. apply: dec_loop; [eassumption|].
    by rewrite H'x (Config_eta y) H0y H1y H2y.
Qed.

(* uniform transition from equivalence class (S a, S b) *)
Lemma transition_Sa_Sb :
  (* terminating equivalence class (S a, 0) *)
  (forall a b, terminating (0, (S a, S b))) +
  (* non-terminating equivalence class (S a, 0) *)
  (forall a b, non_terminating (0, (S a, S b))) +
  (* uniform transition to equivalence class (0, 0) *)
  (forall a b, reaches (0, (S a, S b)) (0, (0, 0))) +
  (* uniform transition to equivalence class (S a, 0) *)
  (forall a b, exists a', reaches (0, (S a, S b)) (0, (S a', 0))) +
  (* uniform transition to equivalence class (0, S b) *)
  (forall a b, exists b', reaches (0, (S a, S b)) (0, (0, S b'))).
Proof using HM.
  have := reaches'I (0, (1, 1)).
  move=> [x] [Hk]. case H'x: (step x) => [y|]; first last.
  { (* case: (1, 1) f->> HALT; uniform termination *)
    move=> _. do 4 left. move=> a b.
    move: H'x Hk => /reaches'_None_terminating H /H /=. apply; lia. }
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* case: (1, 0) f->>t-> HALT; uniform termination *)
    move: H'x Hk => /reaches'_Some_terminating H /H {}H /H {}H.
    do 4 left. move=> a b. apply: H => /=; lia. }
  move: y H'x => [py' [[|ay'] [|by']]] H'x /= Hy'; subst py'.
  - (* case: (1, 1) f->>t-> (0, 0) impossible *)
    by move: Hk => /not_transition_1_1_to_0_0.
  - (* case: (1, 1) f->>t-> (0, S b) uniform transition to (0, S b) *)
    right. move=> a b.
    move: Hk H'x => /dec_a_0 H /H /(_ (S a) (S b)) Hk'.
    exists (S a * by' + S b - 1).
    move: Hk'. congr reaches. congr (_, (_, _)); lia.
  - (* case: (1, 1) f->>t-> (S a, 0) uniform transition to (S a, 0) *)
    do 1 left. right. move=> a b.
    move: Hk H'x => /dec_b_0 H /H /(_ (S a) (S b)) Hk'.
    exists (S b * ay' + S a - 1).
    move: Hk'. congr reaches. congr (_, (_, _)); lia.
  - (* case: (1, 1) f->>t-> (S a, S b) non-termination *)
    do 3 left. right. move=> a b. apply: dec_loop; by eassumption.
Qed.


(* equivalence classes (0, 0), (S a, 0), (0, S b), (S a, S b) *)
Definition RZ '(a, b) '(a', b') : Prop := (a > 0 <-> a' > 0) /\ (b > 0 <-> b' > 0).

Definition representatives := [(0, 0); (1, 0); (0, 1); (1, 1)].

Lemma get_representative : forall ab, {v | In v representatives /\ RZ v ab}.
Proof.
  move=> [[|a] [|b]]; rewrite /representatives /RZ.
  - exists (0, 0) => /=. split; [tauto|lia].
  - exists (0, 1) => /=. split; [tauto|lia].
  - exists (1, 0) => /=. split; [tauto|lia].
  - exists (1, 1) => /=. split; [tauto|lia].
Qed.

Lemma uniform_transition ab :
  In ab representatives -> 
  (* uniform termination *)
  (forall a'b', RZ ab a'b' -> terminating (0, a'b')) +
  (* uniform non-termination *)
  (forall a'b', RZ ab a'b' -> non_terminating (0, a'b')) +
  (* uniform transition *)
  {v | In v representatives /\
    (forall a'b', RZ ab a'b' -> exists w, RZ v w /\ reaches_plus (0, a'b') (0, w)) }.
Proof using HM.
  rewrite /representatives /=.
  have HE := @eq_or_inf (nat * nat) ltac:(by do ? decide equality).
  case /HE; [|case /HE; [|case /HE; [|case /HE; last done]]] => <-.
  - have [[[[|]|]|]|] := transition_0_0.
    + move=> ?. left. left=> - [a' b'] /= ?.
      have ->: a' = 0 by lia. have ->: b' = 0 by lia. done.
    + move=> ?. left. right=> - [a' b'] /= ?. have ->: a' = 0 by lia. have ->: b' = 0 by lia. done.
    + move=> H. right. exists (1, 0). split; first by tauto.
      move: H => [a'' Hk] [a' b'] /= ?.
      have ->: a' = 0 by lia. have ->: b' = 0 by lia.
      exists (S a'', 0). split; [lia|by apply: (reaches_neq_incl Hk)].
    + move=> H. right. exists (0, 1). split; first by tauto.
      move: H => [b'' Hk] [a' b'] /= ?.
      have ->: a' = 0 by lia. have ->: b' = 0 by lia.
      exists (0, S b''). split; [lia|by apply: (reaches_neq_incl Hk)].
    + move=> H. right. exists (1, 1). split; first by tauto.
      move: H => [a'' [b'' Hk]] [a' b'] /= ?.
      have ->: a' = 0 by lia. have ->: b' = 0 by lia.
      exists (S a'', S b''). split; [lia|by apply: (reaches_neq_incl Hk)].
  - have [[[[|]|]|]|] := transition_Sa_0.
    + move=> ?. left. left=> - [a' b'] /= ?.
      have ->: a' = S (a' - 1) by lia. have ->: b' = 0 by lia. done.
    + move=> ?. left. right=> - [a' b'] /= ?.
      have ->: a' = S (a' - 1) by lia. have ->: b' = 0 by lia. done.
    + move=> H. right. exists (0, 0). split; first by tauto.
      move=> [a' b'] /= ?. have ->: a' = S (a' - 1) by lia. have ->: b' = 0 by lia.
      have Hk := H (a'-1). exists (0, 0). split; [lia|by apply: (reaches_neq_incl Hk)].
    + move=> H. right. exists (0, 1). split; first by tauto.
      move=> [a' b'] /= ?. have ->: a' = S (a' - 1) by lia. have ->: b' = 0 by lia.
      have [b'' Hk] := H (a'-1). exists (0, S b''). split; [lia|by apply: (reaches_neq_incl Hk)].
    + move=> H. right. exists (1, 1). split; first by tauto.
      move=> [a' b'] /= ?. have ->: a' = S (a' - 1) by lia. have ->: b' = 0 by lia.
      have [a'' [b'' Hk]] := H (a'-1).
      exists (S a'', S b''). split; [lia|by apply: (reaches_neq_incl Hk)].
  - have [[[[|]|]|]|] := transition_0_Sb.
    + move=> ?. left. left=> - [a' b'] /= ?.
      have ->: a' = 0 by lia. have ->: b' = S (b' - 1) by lia. done.
    + move=> ?. left. right=> - [a' b'] /= ?.
      have ->: a' = 0 by lia. have ->: b' = S (b' - 1) by lia. done.
    + move=> H. right. exists (0, 0). split; first by tauto.
      move=> [a' b'] /= ?. have ->: a' = 0 by lia. have ->: b' = S (b' - 1) by lia.
      have Hk := H (b'-1). exists (0, 0). split; [lia|by apply: (reaches_neq_incl Hk)].
    + move=> H. right. exists (1, 0). split; first by tauto.
      move=> [a' b'] /= ?. have ->: a' = 0 by lia. have ->: b' = S (b' - 1) by lia.
      have [a'' Hk] := H (b'-1). exists (S a'', 0). split; [lia|by apply: (reaches_neq_incl Hk)].
    + move=> H. right. exists (1, 1). split; first by tauto.
      move=> [a' b'] /= ?. have ->: a' = 0 by lia. have ->: b' = S (b' - 1) by lia.
      have [a'' [b'' Hk]] := H (b'-1).
      exists (S a'', S b''). split; [lia|by apply: (reaches_neq_incl Hk)].
  - have [[[[|]|]|]|] := transition_Sa_Sb.
    + move=> ?. left. left=> - [a' b'] /= ?.
      have ->: a' = S (a' - 1) by lia. have ->: b' = S (b' - 1) by lia. done.
    + move=> ?. left. right=> - [a' b'] /= ?.
      have ->: a' = S (a' - 1) by lia. have ->: b' = S (b' - 1) by lia. done.
    + move=> H. right. exists (0, 0). split; first by tauto.
      move=> [a' b'] /= ?. have ->: a' = S (a' - 1) by lia. have ->: b' = S (b' - 1) by lia.
      have Hk := H (a'-1) (b'-1). exists (0, 0). split; [lia|by apply: (reaches_neq_incl Hk)].
    + move=> H. right. exists (1, 0). split; first by tauto.
      move=> [a' b'] /= ?. have ->: a' = S (a' - 1) by lia. have ->: b' = S (b' - 1) by lia.
      have [a'' Hk] := H (a'-1) (b'-1).
      exists (S a'', 0). split; [lia|by apply: (reaches_neq_incl Hk)].
    + move=> H. right. exists (0, 1). split; first by tauto.
      move=> [a' b'] /= ?. have ->: a' = S (a' - 1) by lia. have ->: b' = S (b' - 1) by lia.
      have [b'' Hk] := H (a'-1) (b'-1).
      exists (0, S b''). split; [lia|by apply: (reaches_neq_incl Hk)].
Qed.

Opaque representatives.

Lemma RZ_loop v : 
  (forall ab, RZ v ab ->
    exists a'b', RZ v a'b' /\ reaches_plus (0, ab) (0, a'b')) ->
  forall ab, RZ v ab -> non_terminating (0, ab).
Proof.
  move=> Hv ab Hab k. elim: k ab Hab; first done.
  move=> k IH ab /Hv [a'b'] [/IH] Hk [k' [? Hk']].
  move=> /(steps_k_monotone (k' + k)) /(_ ltac:(lia)).
  move: Hk' => /steps_plus ->. by apply: Hk.
Qed.

Lemma uniform_representative_decision v :
  In v representatives -> 
  (* uniform termination *)
  (forall ab, RZ v ab -> terminating (0, ab)) +
  (* uniform non-termination *)
  (forall ab, RZ v ab -> non_terminating (0, ab)).
Proof using HM.
  move: v.
  have: { L & incl L representatives & 
    (forall v, In v representatives -> 
    (forall ab, RZ v ab -> terminating (0, ab)) + (forall ab, RZ v ab -> non_terminating (0, ab)) +
    { w | In w L /\
      (forall ab, RZ v ab -> exists a'b', RZ w a'b' /\ reaches_plus (0, ab) (0, a'b')) } ) }.
  { exists representatives; first done. by apply: uniform_transition. }
  case. elim.
  { move=> _ H v /H /= [[|]|]; [tauto|tauto|]. by move=> [?] []. }
  move=> v0 L IH /(@incl_cons_inv (nat*nat)) [Hv0 HL] HRZ. apply: IH; first done.
  move=> v /HRZ. move=> [[|]|]; [tauto|tauto|].
  have HE := @eq_or_inf (nat * nat) ltac:(by do ? decide equality).
  move=> [w] /= [/HE [|]]; first last.
  { move=> ??. right. by exists w. }
  move=> <-. move: Hv0 => /HRZ [[|]|].
  - (* termination *)
    move=> Hv0 Hv. left. left=> ab /Hv [a'b'] [/Hv0].
    by move=> /reaches_terminating H /reaches_plus_incl /H.
  - (* non-termination *)
    move=> Hv0 Hv. left. right=> ab /Hv [a'b'] [/Hv0].
    by move=> /reaches_non_terminating H /reaches_plus_incl /H.
  - (* chaining *)
    move=> [w'] /= [/HE [|]].
    + (* non-termination *)
      move=> <- /RZ_loop Hv0 Hv. left. right=> ab /Hv [a'b'] [/Hv0].
      by move=> /reaches_non_terminating H /reaches_plus_incl /H.
    + move=> ? Hv0 Hv. right. exists w'. split; first done.
      move=> ab /Hv [a'b'] [/Hv0] [a''b''] [? HSk'] HSk.
      exists a''b''. split; first done.
      by apply: (reaches_plus_trans HSk HSk').
Qed.

Lemma uniform_decision_0 a b : (terminating (0, (a, b))) + (non_terminating (0, (a, b))).
Proof using HM.
  have [v []] := get_representative (a, b).
  move=> /uniform_representative_decision [] => H /H; tauto.
Qed.

(* informative decision statement for reversible halting for Cm2 *)
Theorem decision (c: Config) : (terminating c) + (non_terminating c).
Proof using HM.
  have [y [/reaches'_incl Hk]] := reaches'I c.
  case Hz: (step y) => [[pz [az bz]]|] /=; first last.
  { (* termination *)
    move=> _. left. apply: (reaches_terminating Hk).
    by exists 1. }
  have Hcz : reaches c (pz, (az, bz)).
  { apply: reaches_trans; [|exists 1]; by eassumption. }
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* termination *)
    move=> /nth_error_None Hpz. left.
    move: Hcz => /reaches_terminating. apply.
    exists 1. by apply /step_None. }
  move=> ?. subst pz. case: (uniform_decision_0 az bz).
  - (* termination *)
    move=> /reaches_terminating H'z. left. by apply: H'z.
  - (* non-termination *)
    move=> /reaches_non_terminating H'z. right. by apply: H'z.
Qed.

End Construction.

Require Import Undecidability.Synthetic.Definitions.

(* decision procedure for the halting problem for reversible Cm2 *)
Definition decide : { M: Cm2 | reversible M } * Config -> bool :=
  fun '(exist _ M HM, c) =>
    match decision M HM c with
    | inl _ => true
    | inr _ => false
    end.

(* decision procedure correctness *)
Lemma decide_spec : decider decide CM2_REV_HALT.
Proof.
  rewrite /decider /reflects /decide => - [[M HM] c].
  case: (decision M HM c).
  - tauto.
  - move=> H. split; [by move=> [k /H] | done].
Qed.
