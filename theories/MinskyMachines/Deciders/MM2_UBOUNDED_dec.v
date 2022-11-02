(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  Decision Procedure(s):
    Two-counter Machine Uniform Boundedness (MM2_UBOUNDED)

  References:
  [1] Dudenhefner, Andrej. "Certified Decision Procedures for Two-Counter Machines."
      FSCD 2022. https://drops.dagstuhl.de/opus/volltexte/2022/16297/
*)

Require Import List ListDec PeanoNat Lia Relation_Operators Operators_Properties Permutation.
Import ListNotations.
Require Import Undecidability.MinskyMachines.MM2.
Require Import Undecidability.MinskyMachines.Util.MM2_facts.
Import MM2Notations.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

(* local facts *)
Module Facts.

(* transforms a goal (A -> B) -> C into goals A and B -> C *)
Lemma unnest : forall (A B C : Type), A -> (B -> C) -> (A -> B) -> C.
Proof. auto. Qed.

Lemma prod_nat_nat_eq_dec (x y : nat * nat) : {x = y} + {x <> y}.
Proof. by do ? decide equality. Qed.

Lemma Exists_sig {X : Type} P (HP : (forall x, {P x} + {~ P x})) (L : list X) :
  Exists P L -> { x | In x L /\ P x}.
Proof.
  elim: L. { by move=> /Exists_nil. }
  move=> x L IH /Exists_cons H.
  have [/IH|?] := Exists_dec P L HP.
  - move=> [y [? ?]]. exists y. by split; [right|].
  - exists x. by split; [left|tauto].
Qed.

Lemma NoDup_map_ext {X Y : Type} (f : X -> Y) (l : list X) :
  (forall x1, In x1 l -> forall x2, In x2 l -> f x1 = f x2 -> x1 = x2) -> NoDup l -> NoDup (map f l).
Proof.
  elim: l. { move=> *. by constructor. }
  move=> x l IH /= H /NoDup_cons_iff [Hxl] /IH {}IH. constructor.
  - move=> /in_map_iff [x'] [/H] ? Hx'l. have ? : x' = x by tauto.
    subst x'. exact: (Hxl Hx'l).
  - apply: IH. move=> x1 Hx1l x2 Hx2l /H. tauto.
Qed.

(* variant of the pigeonhole principle *)
Lemma pigeonhole {X : Type} (L L' : list X) :
  incl L L' -> length L' < length L -> not (NoDup L).
Proof.
  move=> ?? HL. suff: length L = length L' by lia.
  apply /Permutation_length /NoDup_Permutation_bis; by [|lia].
Qed.

Lemma nth_error_seq {i start len} :
  i < len -> nth_error (seq start len) i = Some (start + i).
Proof.
  elim: len i start; first by lia.
  move=> len IH [|i] start.
  { move=> ?. congr Some. lia. }
  move=> ?. rewrite /= IH; first by lia.
  congr Some. lia.
Qed.

Section DiscreteList.

Context {X : Type} (X_eq_dec : forall (x y : X), {x = y} + {x <> y}).

Lemma not_NoDup_consE {x} {l: list X} : (not (NoDup (x :: l))) -> In x l \/ not (NoDup l).
Proof using X_eq_dec.
  have [?|?] := In_dec X_eq_dec x l.
  { move=> ?. by left. }
  move=> Hxl. right => Hl. apply: Hxl.
  by constructor.
Qed.

Lemma not_NoDupE {l : list X} : not (NoDup l) -> 
  exists '(i, j), i < j < length l /\ nth_error l i = nth_error l j.
Proof using X_eq_dec.
  elim: l. { move=> H. exfalso. apply: H. by constructor. }
  move=> x l IH.
  move=> /not_NoDup_consE [|].
  - move=> /(@In_nth_error X) [j] Hj.
    have ? : not (length l <= j).
    { move=> /nth_error_None. by rewrite Hj. }
    exists (0, S j) => /=. split; [lia|done].
  - move=> /IH [[i j]] [? ?].
    exists (S i, S j) => /=. split; [lia|done].
Qed.

Lemma not_inclE (L L' : list X) : (not (incl L L')) -> { x | In x L /\ not (In x L')}.
Proof using X_eq_dec.
  elim: L. { move=> H. exfalso. by apply: H. }
  move=> x L IH /=.
  have [|?] := In_dec X_eq_dec x L'.
  - move=> ? HxLL'. have /IH [y [? ?]] : ~ incl L L'.
    { move=> H. apply: HxLL'. by move=> y /= [<-|/H]. }
    exists y. tauto.
  - move=> _. exists x. tauto.
Qed.

(* explicit duplicates in a mapped sequence *)
Lemma dup_seq (f : nat -> X) start len :
  not (NoDup (map f (seq start len))) ->
  exists '(i, j), f i = f j /\ (start <= i /\ i < j /\ j < start+len).
Proof using X_eq_dec.
  move=> /not_NoDupE [[i j]]. rewrite map_length seq_length.
  move=> [? H]. exists (start+i, start+j). split; last lia.
  move: H. rewrite ?nth_error_map ?nth_error_seq; [lia|lia|].
  by move=> [].
Qed.

End DiscreteList.

End Facts.

Import Facts.

Section Construction.
Variable M : list mm2_instr.

#[local] Notation bounded := (MM2.mm2_bounded M).
#[local] Notation step := (MM2.mm2_step M).
#[local] Notation reaches := (clos_refl_trans _ step).
#[local] Notation trace := (MM2.mm2_trace M).

#[local] Arguments Nat.min !n !m /.

Lemma option_mm2_state_eq_dec (x y: option mm2_state) : {x = y} + {x <> y}.
Proof. by do ? decide equality. Qed.

Lemma bounded_monotone {k k' x} : k <= k' -> bounded k x -> bounded k' x.
Proof. move=> ? [L [? ?]]. exists L. split; [lia|done]. Qed.

Fixpoint steps k x :=
  match k with
  | 0 => Some x
  | S k =>
    match mm2_sig_step_dec M x with
    | inleft (exist _ y _) => steps k y
    | inright _ => None
    end
  end.

Lemma steps_plus' {k x k'} :
  steps (k + k') x = obind (steps k') (steps k x).
Proof.
  elim: k x. { done. }
  move=> k IH x /=.
  case: (mm2_sig_step_dec M x) => [[y]|]; last done.
  move=> _. by apply: IH.
Qed.

Lemma steps_k_monotone {k x} k' : steps k x = None -> k <= k' -> steps k' x = None.
Proof.
  move=> Hk ?. have ->: k' = k + (k' - k) by lia.
  by rewrite steps_plus' Hk.
Qed.

Lemma steps_sub {i j x y z} :
  steps i x = Some y ->
  steps j x = Some z ->
  i <= j ->
  steps (j-i) y = Some z.
Proof.
  move=> Hi + ?. rewrite [in steps j x](ltac:(lia) : j = i + (j - i)).
  by rewrite steps_plus' Hi.
Qed.

Lemma steps_reaches {k x y} : steps k x = Some y -> reaches x y.
Proof.
  elim: k x. { move=> ? [<-]. by apply: rt_refl. }
  move=> k IH x /=.
  case: (mm2_sig_step_dec M x) => [[z]|]; last done.
  move=> ? /IH. apply: rt_trans. by apply: rt_step.
Qed.

Lemma reaches_steps {x y} : reaches x y -> exists k, steps k x = Some y.
Proof.
  move=> /clos_rt_rt1n_iff. elim.
  - move=> >. by exists 0.
  - move=> {}x {}y z Hxy _ [k Hk]. exists (S k) => /=.
    case: (mm2_sig_step_dec M x) => [[y' Hxy']|].
    + by move: Hxy Hxy' => /mm2_step_det /[apply] <-.
    + move=> H. by move: Hxy => /H.
Qed.

Lemma step_values_bound x y : steps 1 x = Some y ->
  value1 y + value2 y <= 1 + value1 x + value2 x /\
  value1 x + value2 x <= 1 + value1 y + value2 y /\
  value1 x <= 1 + value1 y /\ value1 y <= 1 + value1 x /\
  value2 x <= 1 + value2 y /\ value2 y <= 1 + value2 x.
Proof.
  move=> /=.
  case: (mm2_sig_step_dec M x) => [[?]|]; last done.
  by move=> /mm2_step_values_bound ? [<-].
Qed.

Lemma steps_values_bound k x y : steps k x = Some y ->
  value1 y + value2 y <= k + value1 x + value2 x /\
  value1 x + value2 x <= k + value1 y + value2 y /\
  value1 x <= k + value1 y /\ value1 y <= k + value1 x /\
  value2 x <= k + value2 y /\ value2 y <= k + value2 x.
Proof.
  elim: k x. { move=> ? [<-]. lia. }
  move=> k IH x.
  rewrite (steps_plus' (k := 1) (k' := k)).
  case Hxz: (steps 1 x) => [z|]; last done.
  move=> /IH.
  move: Hxz => /step_values_bound. lia.
Qed.

Definition path k x := map (fun n => steps n x) (seq 0 k).

Lemma path_length {k x} : length (path k x) = k.
Proof. by rewrite /path map_length seq_length. Qed.

Lemma In_pathE K x oy : In oy (path K x) -> exists k, k < K /\ steps k x = oy.
Proof.
  move=> /in_map_iff [k] [<-] /in_seq ?.
  exists k. split; [lia|done].
Qed.

Lemma In_None_pathE k x :
  In None (path k x) -> steps k x = None.
Proof.
  move=> /In_pathE [k' [?]] /(steps_k_monotone k). apply. lia.
Qed.

Lemma In_pathI k x K : k < K -> In (steps k x) (path K x).
Proof.
  move=> ?. apply /in_map_iff. exists k. split; first done.
  apply /in_seq. lia.
Qed.

Lemma path_S {k x} y : steps 1 x = Some y -> path (S k) x = (Some x) :: (path k y).
Proof.
  move=> Hxy. rewrite /path /= -seq_shift map_map.
  congr cons. apply: map_ext => - ? /=.
  move: Hxy => /=.
  case: (mm2_sig_step_dec M x) => [[?]|]; last done.
  by move=> _ [->].
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
  by rewrite steps_plus' Hxy.
Qed.

Lemma path_S_last {k x} : path (S k) x = (path k x) ++ [steps k x].
Proof. by rewrite /path seq_S map_app. Qed.

Lemma steps_loop_mod {K x k} : steps (S K) x = Some x ->
  steps k x = steps (k mod (S K)) x.
Proof.
  rewrite [in steps k x](Nat.div_mod_eq k (S K)).
  move: (k mod (S K)) => k' Hx. elim: (k / S K).
  - congr steps. lia.
  - move=> n IH. have ->: S K * S n + k' = S K + (S K * n + k') by lia.
    by rewrite steps_plus' Hx.
Qed.

Lemma path_loopE K x : In (steps K x) (path K x) -> 
  forall k, In (steps k x) (path K x).
Proof.
  elim: K x; first done.
  move=> K IH x. rewrite (steps_plus' (k := 1) (k' := K)).
  case Hxz: (steps 1 x) => [z|].
  - move=> H. rewrite (path_S z Hxz) /= in H. case: H.
    + move=> Hzx k. have /steps_loop_mod -> : steps (S K) x = Some x.
      { by rewrite (steps_plus' (k := 1) (k' := K)) Hxz. }
      by apply /In_pathI /(Nat.mod_upper_bound k (S K)).
    + rewrite (path_S z Hxz).
      move=> /IH {}IH [|k]; first by left.
      rewrite (steps_plus' (k := 1) (k' := k)) Hxz. right. by apply: IH.
  - move=> /in_map_iff [k] [Hk] /in_seq HK.
    move=> k'. have [|Hkk'] : k' < k \/ k <= k' by lia.
    + move=> ?. apply: In_pathI. lia.
    + move: (Hk) => /(steps_k_monotone k') /(_ Hkk') ->.
      rewrite /= in Hk. rewrite -Hk. apply: In_pathI. lia.
Qed.

Lemma path_loopE' K x : In (steps K x) (path K x) -> 
  forall y, reaches x y -> In (Some y) (path K x).
Proof.
  move=> /path_loopE H y /reaches_steps [k] H'. move: (H k).
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
  have [|/IH ?] := In_dec option_mm2_state_eq_dec (steps k x) (path k x).
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
  move=> y /reaches_steps [k]. have [?|?] : k < K \/ K <= k by lia.
  - move=> Hk. apply /in_map_iff. exists (Some y).
    split; first done.
    rewrite -Hk. by apply: In_pathI.
  - by move: HK => /(steps_k_monotone k) /(_ ltac:(lia)) ->.
Qed.

Lemma NoDup_not_bounded {K x y} : 
  steps K x = Some y -> NoDup (path (K + 1) x) -> not (bounded K x).
Proof.
  move=> Hxy HK [L [? HL]].
  apply: (pigeonhole (path (K+1) x) (map Some L)).
  - move=> [z|] /in_map_iff [k] [Hk] /in_seq ?.
    { apply /in_map_iff. exists z. split; first done.
      apply: HL. by apply: (steps_reaches Hk). }
    by move: Hk Hxy => /(steps_k_monotone K) /(_ ltac:(lia)) ->.
  - rewrite map_length path_length. lia.
  - done.
Qed.

Lemma pointwise_decision K x : {bounded K x} + {not (bounded K x)}.
Proof.
  case HK: (steps K x) => [y|].
  - have [Hy|Hy] := In_dec option_mm2_state_eq_dec (Some y) (path K x).
    + left. apply: loop_bounded. by rewrite HK.
    + right. apply: (NoDup_not_bounded HK).
      apply: path_noloopI. by rewrite HK.
  - left. by apply: mortal_bounded.
Qed.

Lemma shift_steps_a k K p a b :
  k <= K ->
  steps k (p, (K + a, b)) =
  match steps k (p, (K, b)) with
  | Some (p', (a', b')) => Some (p', (a' + a, b'))
  | None => None
  end.
Proof.
  elim: k K p a b. { done. }
  move=> k IH [|K] p a b ? /=; [lia|].
  case: (mm2_sig_step_dec M (p, (S (K + a), b))) => [[[p1 [a1 b1]]]|].
  - move=> /(mm2_step_parallel (p, (S K, b))) /= /(_ ltac:(lia)).
    move=> [[p2 [a2 b2]]] /= [+] [?] ?.
    move=> /[dup] /mm2_step_values_bound /= ?.
    case: (mm2_sig_step_dec M (p, _)) => [[?]|] /=; first last.
    { by move=> /[apply]. }
    move=> /mm2_step_det /[apply] ->. subst p1.
    have [-> ->]: a1 = K + (a1 - K) /\ a2 = K + (a2 - K) by lia.
    have ->: b2 = b1 by lia.
    rewrite IH; [lia|]. rewrite IH; [lia|].
    case: (steps k (p2, (K, b1))); last done.
    move=> [? [? ?]] /=. congr (Some (_, (_, _))); lia.
  - move=> /mm2_stop_index_iff /= ?.
    case: (mm2_sig_step_dec M (p, (S K, b))) => [[?]|]; last done.
    move=> [?] [/mm2_instr_at_bounds] /=. lia.
Qed.

Lemma shift_steps_b k K p a b :
  k <= K ->
  steps k (p, (a, K + b)) =
  match steps k (p, (a, K)) with
  | Some (p', (a', b')) => Some (p', (a', b' + b))
  | None => None
  end.
Proof.
  elim: k K p a b. { done. }
  move=> k IH [|K] p a b ? /=; [lia|].
  case: (mm2_sig_step_dec M (p, (a, S (K + b)))) => [[[p1 [a1 b1]]]|].
  - move=> /(mm2_step_parallel (p, (a, S K))) /= /(_ ltac:(lia)).
    move=> [[p2 [a2 b2]]] /= [+] [?] ?.
    move=> /[dup] /mm2_step_values_bound /= ?.
    case: (mm2_sig_step_dec M (p, _)) => [[?]|] /=; first last.
    { by move=> /[apply]. }
    move=> /mm2_step_det /[apply] ->. subst p1.
    have [-> ->]: b1 = K + (b1 - K) /\ b2 = K + (b2 - K) by lia.
    have ->: a2 = a1 by lia.
    rewrite IH; [lia|]. rewrite IH; [lia|].
    case: (steps k (p2, (a1, K))); last done.
    move=> [? [? ?]] /=. congr (Some (_, (_, _))); lia.
  - move=> /mm2_stop_index_iff /= ?.
    case: (mm2_sig_step_dec M (p, (a, S K))) => [[?]|]; last done.
    move=> [?] [/mm2_instr_at_bounds] /=. lia.
Qed.

Lemma shift_path_a K p a b :
  path (K+1) (p, (K+a, b)) =
  map (fun oy => if oy is Some (p', (a', b')) then Some (p', (a'+a, b')) else None) (path (K+1) (p, (K, b))).
Proof. 
  rewrite /path map_map. apply: map_ext_in => k /in_seq ?.
  apply: shift_steps_a. lia.
Qed.

Lemma shift_path_b K p a b :
  path (K+1) (p, (a, K+b)) =
  map (fun oy => if oy is Some (p', (a', b')) then Some (p', (a', b'+b)) else None) (path (K+1) (p, (a, K))).
Proof. 
  rewrite /path map_map. apply: map_ext_in => k /in_seq ?.
  apply: shift_steps_b. lia.
Qed.

Lemma path_NoDup_a_bound K p a b : K <= a -> NoDup (path (K+1) (p, (a, b))) -> NoDup (path (K+1) (p, (K, b))).
Proof.
  move=> ?. have ->: a = K+(a-K) by lia.
  rewrite shift_path_a. by apply: NoDup_map_inv.
Qed.

Lemma path_NoDup_b_bound K p a b : K <= b -> NoDup (path (K+1) (p, (a, b))) -> NoDup (path (K+1) (p, (a, K))).
Proof.
  move=> ?. have ->: b = K+(b-K) by lia.
  rewrite shift_path_b. by apply: NoDup_map_inv.
Qed.

#[local] Notation l := (length M).

Lemma fixed_decision K :
  {forall x : mm2_state, bounded K x} + {~ (forall x : mm2_state, bounded K x)}.
Proof.
  (* need to check configurations up to values K *)
  have := Forall_dec (fun 'x => bounded K x) (pointwise_decision K)
    (list_prod (seq 1 l) (list_prod (seq 0 (K+1)) (seq 0 (K+1)))).
  case; first last.
  { move=> H. right => HK. apply /H /Forall_forall. move=> ??. by apply: HK. }
  wlog: K /(0 < K).
  { move: K => [|K] H HK.
    - right. move=> /(_ (0, (0, 0))) [[|? L] [/= ? /(_ (0, (0, 0))) HL]].
      + apply: HL. by apply: rt_refl.
      + lia.
    - apply: H; [lia|done]. }
  move=> ? HK. left => x.
  have [|/path_noloopI] := In_dec option_mm2_state_eq_dec (steps K x) (path K x).
  { by apply: loop_bounded. }
  case Hz: (steps K x) => [z|]; first last.
  { move=> _. by apply: mortal_bounded. }
  (* not bounded *)
  move=> Hx. exfalso.
  move: x Hx Hz => [p [a b]] Hx Hz.
  have Hp : 0 < p <= l.
  { move: Hz. have -> : K = 1 + (K - 1) by lia.
    rewrite steps_plus' /=.
    case: (mm2_sig_step_dec M (p, (a, b))) => [[?]|]; last done.
    by move=> [?] [/mm2_instr_at_bounds] /=. }
  move: Hx Hz.
  (* it suffices to consider configurations up to values K  *)
  wlog: a b z /(a <= K /\ b <= K); first last.
  { move=> ? Hx Hz. suff: bounded K (p, (a, b)).
    { by apply: (NoDup_not_bounded Hz). }
    move: HK => /Forall_forall.
    apply. apply: in_prod; [|apply: in_prod]; apply /in_seq; lia. }
  move=> H'K.
  wlog: a b z /(a <= K).
  { move=> H. have [/H|->] : a <= K \/ a = K + (a - K) by lia.
    { by apply. }
    move=> /path_NoDup_a_bound => /(_ ltac:(lia)) /H {H}.
    rewrite shift_steps_a; first done.
    case: (steps K (p, (K, b))) => [y|]; last done.
    move=> H _. by apply: (H y). }
  move=> ?. have [?|->] : b <= K \/ b = K + (b - K) by lia.
  { move=> /H'K H /H. by apply. }
  move=> /path_NoDup_b_bound => /(_ ltac:(lia)) /H'K.
  rewrite shift_steps_b; first done.
  case: (steps K (p, (a, K))) => [y|]; last done.
  move=> H _. by apply: (H y).
Qed.

(* from an arbitrary config arrive at config with at least one large value *)
Lemma uniform_decision_aux1 x : let n := l*(l+1) in
  (bounded (l*n*n+1) x) +
  { y | (exists k, k <= l*n*n /\ steps k x = Some y) /\ (n <= value1 y \/ n <= value2 y) }.
Proof.
  move=> n.
  have [|/path_noloopI Hx] :=
    In_dec option_mm2_state_eq_dec (steps (l*n*n) x) (path (l*n*n) x).
  { move=> /loop_bounded H. left. apply: (bounded_monotone _ H). lia. }
  case Hxy: (steps (l*n*n+1) x) => [y|]; first last.
  { left. by apply: mortal_bounded. }
  right.
  have [/pigeonhole|] := incl_dec option_mm2_state_eq_dec (path (l*n*n+1) x)
    (map Some (list_prod (seq 1 l) (list_prod (seq 0 n) (seq 0 n)))).
  { move=> H. exfalso. apply: (H _ Hx).
    rewrite path_length map_length ?prod_length ?seq_length. lia. }
  move=> /(not_inclE option_mm2_state_eq_dec) [[z|]].
  - move=> H. exists z.
    move: H => [/in_map_iff] [k] [Hk] /in_seq ? H.
    split. { exists k. split; [lia|done]. }
    suff : not (value1 z < n /\ value2 z < n) by lia.
    move=> H'. apply: H. apply /in_map_iff. exists z. split; first done.
    have := steps_sub Hk Hxy ltac:(lia).
    have -> /=: l * n * n + 1 - k = S (Nat.pred (l * n * n + 1 - k)) by lia.
    case: (mm2_sig_step_dec M z) => [[?]|]; [|done].
    move: z {Hk} H' => [? [? ?]] /= ? [?] /= [/mm2_instr_at_bounds ? _] _.
    apply /in_prod; [|apply /in_prod]; apply /in_seq; lia.
  - move=> [/in_map_iff] H. exfalso.
    move: H => [k] [+ /in_seq ?].
    move=> /(steps_k_monotone (l*n*n+1)) /(_ ltac:(lia)).
    by rewrite Hxy.
Qed.

Lemma k_step_iter k p a1 b1 a2 b2 :
  (k <= a1 \/ a1 = a2) -> (k <= b1 \/ b1 = b2) -> 
  steps k (p, (a1, b1)) = Some (p, (a2, b2)) ->
  let ca := if Nat.eq_dec a1 a2 then 0 else 1 in
  let cb := if Nat.eq_dec b1 b2 then 0 else 1 in
  forall i n a b, i <= n ->
    steps (i*k) (p, (a1+ca*(a+n*a1),b1+cb*(b+n*b1))) =
      Some (p, (a1+ca*(a+(n-i)*a1+i*a2),b1+cb*(b+(n-i)*b1+i*b2))).
Proof.
  move=> Ha Hb Hk ca cb. elim.
  { move=> ????. congr (Some (_, (_, _))); lia. }
  move=> i IH [|n] a b; first by lia.
  move=> /(iffRL (Nat.succ_le_mono _ _)) /IH {}IH.
  rewrite /= steps_plus'.
  have := IH (a2+a) (b2+b). congr eq; first last.
  { congr (Some (_, (_, _))); lia. }
  have -> : steps (i * k) (p, (a1 + ca * (a2 + a + n * a1), b1 + cb * (b2 + b + n * b1))) =
    obind (steps (i * k)) (Some (p, (a1 + ca * (a2 + a + n * a1), b1 + cb * (b2 + b + n * b1)))) by done.
  congr obind.
  rewrite /ca /cb.
  move: (Nat.eq_dec a1 a2) (Nat.eq_dec b1 b2) => [?|?] [?|?] /=.
  - rewrite ?Nat.add_0_r Hk.
    congr (Some (_, (_, _))); lia.
  - rewrite shift_steps_b; first lia.
    rewrite ?Nat.add_0_r Hk.
    congr (Some (_, (_, _))); lia.
  - rewrite shift_steps_a; first lia.
    rewrite ?Nat.add_0_r Hk.
    congr (Some (_, (_, _))); lia.
  - rewrite shift_steps_a; first lia.
    rewrite shift_steps_b; first lia.
    rewrite ?Nat.add_0_r Hk.
    congr (Some (_, (_, _))); lia.
Qed.

Lemma not_uniformly_boundedI k p a1 b1 a2 b2 :
  (k <= a1 \/ a1 = a2) -> (k <= b1 \/ b1 = b2) -> 
  (a1 <> a2 \/ b1 <> b2) ->
  steps k (p, (a1, b1)) = Some (p, (a2, b2)) ->
  not (mm2_uniformly_bounded M).
Proof.
  move=> /k_step_iter H /H {}H Hab /H /= + [K].
  move=> /(_ _ K 0 0) /=.
  move Ha: (a1 + _ * _) => a.
  move Hb: (b1 + _ * _) => b.
  move=> {}H /(_ (p, (a, b))) [L [? HL]].
  have : incl (map (fun i => steps (i * k) (p, (a, b))) (seq 0 (K+1))) (map Some L).
  { move=> z /in_map_iff [i] [<- /in_seq ?]. rewrite H; first by lia.
    apply: in_map. apply: HL. apply: (steps_reaches (k := (i*k))). rewrite H; [lia|done]. }
  move=> /pigeonhole. apply.
  { rewrite ?map_length seq_length. lia. }
  under map_ext_in.
  { move=> i /in_seq ?. rewrite H; first by lia. over. }
  apply: NoDup_map_ext; last by apply: seq_NoDup.
  move=> i1 /in_seq ? i2 /in_seq ? [].
  move: (Nat.eq_dec a1 a2) (Nat.eq_dec b1 b2) => [?|?] [?|?] /=; nia.
Qed.

(* from a config with the a really large value arrive at config with two large values *)
Lemma uniform_decision_aux2 x : ({l*(l+1) <= value1 x} + {l*(l+1) <= value2 x}) ->
  (bounded (l*l+1) x) + (not (mm2_uniformly_bounded M)) +
    { y | (exists k, k <= l*l /\ steps k x = Some y) /\ (l <= value1 y /\ l <= value2 y) }.
Proof.
  move=> Hlx.
  have [|/path_noloopI Hx] :=
    In_dec option_mm2_state_eq_dec (steps (l*l) x) (path (l*l) x).
  { move=> /loop_bounded H. left. left. apply: (bounded_monotone _ H). lia. }
  case Hxy: (steps (l*l+1) x) => [y|]; first last.
  { left. left. by apply: mortal_bounded. }
  pose P := fun oz : option mm2_state => if oz is Some z then 
    (if Hlx then l <= value2 z else l <= value1 z) else True.
  have HP : forall x, {P x} + {not (P x)}.
  { move=> [? /= |]; last by left. clear P.
    case: Hlx => ?; by apply: Compare_dec.le_dec. }
  have [|H'x] := Exists_dec P (path (l * l + 1) x) HP.
  { move=> /(Exists_sig P HP) [[z|]] [Hz /= H'z].
    - right. exists z. move: Hz => /In_pathE [k [? Hk]]. split.
      + exists k. split; [lia|done].
      + move: Hk => /steps_values_bound. clear P HP.
        case: Hlx H'z => /=; lia.
    - exfalso. by move: Hz Hxy => /In_None_pathE ->. }
  (* all value1 or value2 are smaller than l, not uniformly bounded *)
  left. right. subst P.
  have /pigeonhole : incl
    (map (fun oz => if oz is Some (p, (a, b)) then (if Hlx then (p, b) else (p, a)) else (0, 0)) (path (l * l + 1) x))
    (list_prod (seq 1 l) (seq 0 l)).
  { move=> [p c] /in_map_iff [[[p' [a' b']]|]]; first last.
    { move=> [_ /In_pathE].
      move=> [?] [?] /(steps_k_monotone (l * l + 1)) /(_ ltac:(lia)).
      by rewrite Hxy. }
    move=> [+ H].
    have ? : 0 < p' <= l. 
    { move: H => /in_map_iff [k'] [Hk' /in_seq ?].
      have := steps_sub Hk' Hxy ltac:(lia).
      have -> /=: l * l + 1 - k' = S (l * l + 1 - k' - 1) by lia.
      case: (mm2_sig_step_dec M (p', (a', b'))) => [[?]|]; [|done].
      by move=> [?] [/mm2_instr_at_bounds]. }
    case: Hlx H'x HP => /= ? H'x HP.
    - move=> [? ?]. subst p c.
      move: H'x H => /Forall_Exists_neg /Forall_forall H /H{H} /= ?.
      apply /in_prod; apply /in_seq; lia.
    - move=> [? ?]. subst p c.
      move: H'x H => /Forall_Exists_neg /Forall_forall H /H{H} /= ?.
      apply /in_prod; apply /in_seq; lia. }
  apply: unnest. { rewrite map_length ?prod_length ?seq_length path_length. lia. }
  rewrite /path map_map. move=> /(dup_seq prod_nat_nat_eq_dec) [[i j]].
  move=> [+ ?].
  case Hi: (steps i x) => [[p [a1 b1]]|]; first last.
  { move: Hi => /(steps_k_monotone (l*l+1)) /(_ ltac:(lia)). by rewrite Hxy. }
  case Hj: (steps j x) => [[p' [a2 b2]]|]; first last.
  { move: Hj => /(steps_k_monotone (l*l+1)) /(_ ltac:(lia)). by rewrite Hxy. }
  clear H'x.
  have ? : not (p = p' /\ a1 = a2 /\ b1 = b2).
  { move=> [? [? ?]]. subst p' a2 b2.
    move: Hx. rewrite /path.
    have -> : l*l+1 = i + (S (j-i-1)) + (S (l*l -j)) by lia.
    rewrite seq_app seq_app /= ?map_app /= (NoDup_count_occ option_mm2_state_eq_dec).
    move=> /(_ (Some (p, (a1, b1)))). have ->: i + S (j - i - 1) = j by lia.
    rewrite Hi Hj ?count_occ_app /=. case: (option_mm2_state_eq_dec _ _); [lia|done]. }
  case: Hlx HP => /= ? HP.
  - move=> [? ?]. subst p' b2.
    have ? : a1 <> a2 by lia.
    (* x ->>i (p, (a1, b1)) ->>(j-i) (p, (a2, b2)); a1 >= j-i or b1 >= j-i *)
    have ? : j-i <= a1.
    { move: Hi => /steps_values_bound /=. lia. }
    move: Hi Hj => /steps_sub H /H{H} /(_ ltac:(lia)).
    move /not_uniformly_boundedI. apply; lia.
  - move=> [? ?]. subst p' a2.
    have ? : b1 <> b2 by lia.
    have ? : j-i <= b1.
    { move: Hi => /steps_values_bound /=. lia. }
    move: Hi Hj => /steps_sub H /H{H} /(_ ltac:(lia)).
    move /not_uniformly_boundedI. apply; lia.
Qed.

(* from a config with two large values decide boundedness *)
Lemma uniform_decision_aux3 x : l <= value1 x -> l <= value2 x -> (bounded (l+1) x) + (not (mm2_uniformly_bounded M)).
Proof.
  move=> ??.
  have [|/path_noloopI Hx] :=
    In_dec option_mm2_state_eq_dec (steps (l) x) (path (l) x).
  { move=> /loop_bounded H. left. apply: (bounded_monotone _ H). lia. }
  case Hxy: (steps (l+1) x) => [y|]; first last.
  { left. by apply: mortal_bounded. }
  right. (* not uniformly bounded *)
  have /pigeonhole : incl
    (map (fun oz => if oz is Some (p, (a, b)) then p else 0) (path (l + 1) x))
    (seq 1 l).
  { move=> p /in_map_iff [[[p' [a' b']]|]]; first last.
    { move=> [_ /In_pathE].
      move=> [?] [?] /(steps_k_monotone (l + 1)) /(_ ltac:(lia)).
      by rewrite Hxy. }
    move=> [->] H. apply /in_seq.
    move: H => /in_map_iff [k'] [Hk' /in_seq ?].
    have := steps_sub Hk' Hxy ltac:(lia).
    have -> /=: l + 1 - k' = S (l + 1 - k' - 1) by lia.
    case: (mm2_sig_step_dec M (p, (a', b'))) => [[?]|]; [|done].
    move=> [?] [/mm2_instr_at_bounds] /=. lia. }
  apply: unnest. { rewrite map_length ?seq_length path_length. lia. }
  rewrite /path map_map. move=> /(dup_seq Nat.eq_dec) [[i j]].
  move=> [+ ?].
  case Hi: (steps i x) => [[p [a1 b1]]|]; first last.
  { move: Hi => /(steps_k_monotone (l+1)) /(_ ltac:(lia)). by rewrite Hxy. }
  case Hj: (steps j x) => [[p' [a2 b2]]|]; first last.
  { move: Hj => /(steps_k_monotone (l+1)) /(_ ltac:(lia)). by rewrite Hxy. }
  move=> ?. subst p'.
  have ? : a1 <> a2 \/ b1 <> b2.
  { suff : not (a1 = a2 /\ b1 = b2) by lia. move=> [??]. subst a2 b2.
    move: Hx. rewrite /path.
    have -> : l+1 = i + (S (j-i-1)) + (S (l -j)) by lia.
    rewrite seq_app seq_app /= ?map_app /= (NoDup_count_occ option_mm2_state_eq_dec).
    move=> /(_ (Some (p, (a1, b1)))). have ->: i + S (j - i - 1) = j by lia.
    rewrite Hi Hj ?count_occ_app /=. case: (option_mm2_state_eq_dec _ _); [lia|done]. }
  have ?: j - i <= a1 /\ j - i <= b1.
  { move: Hi => /steps_values_bound /=. lia. }
  have := steps_sub Hi Hj ltac:(lia).
  move=> /not_uniformly_boundedI. apply; lia.
Qed.

Lemma uniformly_bounded_empty : mm2_uniformly_bounded [].
Proof.
  exists 1. move=> x. exists [x]. split; first done.
  move=> y /clos_rt_rt1n_iff [].
  - by left.
  - by move=> ?? [?] [] [[|??]] [?] [].
Qed.

Lemma reaches_bounded {K k x y} : steps k x = Some y -> bounded K y -> bounded (k+K) x.
Proof.
  elim: k x. { by move=> x /= [<-]. }
  move=> k IH x /=.
  case: (mm2_sig_step_dec M x) => [[z /mm2_step_det Hxz]|]; last done.
  move=> /IH /[apply] => - [L] [H1L H2L]. exists (x::L) => /=.
  split; [lia|].
  move=> z' /clos_rt_rt1n_iff Hxz'. case: Hxz' Hxz.
  - move=> *. by left.
  - move=> > + /clos_rt_rt1n_iff + Hxz => /Hxz <- /H2L ?. by right.
Qed.

(* a uniformly bounded machine M is uniformly bounded by (|M|+1)^5 *)
Lemma bound_on_uniform_bound : mm2_uniformly_bounded M ->
  forall x, bounded ((l+1)*(l+1)*(l+1)*(l+1)*(l+1)) x.
Proof.
  move=> HM x.
  set K := ((l+1)*(l+1)*(l+1)*(l+1)*(l+1)).
    (* x ->> y with at least one large counter *)
    have [|[y [[k1 [Hk1 Hxy]] ?]]] := uniform_decision_aux1 x.
    { apply: bounded_monotone. lia. }
    have -> : K = k1 + (K - k1) by lia.
    apply: (reaches_bounded Hxy).
    have : {l * (l + 1) <= value1 y} + {l * (l + 1) <= value2 y}.
    { case H: (l * (l + 1) - value1 y) => [|?]; [left|right]; lia. }
    move=> /uniform_decision_aux2 [[|]|[z]].
    - apply: bounded_monotone. lia.
    - by move=> /(_ HM).
    - move=> [[k2 [? Hyz]]] [/uniform_decision_aux3 H /H{H}].
      move=> [/bounded_monotone Hz|].
      + have -> : K - k1 = k2 + (K - k1 - k2) by lia.
        apply: (reaches_bounded Hyz). apply: Hz. lia.
      + by move=> /(_ HM).
Qed.

(* informative decision statement for uniform boundedness for mm2 *)
Theorem decision : (mm2_uniformly_bounded M) + (not (mm2_uniformly_bounded M)).
Proof.
  wlog ? : /(l > 0).
  { move: (M) => [|? ?] /=.
    - move=> _. left. by apply: uniformly_bounded_empty.
    - apply. lia. }
  pose K := (l+1)*(l+1)*(l+1)*(l+1)*(l+1).
  (* test uniform boundedness by K ~ l^5 *)
  have [?|HK] := fixed_decision K. { left. by exists K. }
  (* not uniformly bounded *)
  right. move=> /bound_on_uniform_bound => HM.
  apply: HK => x. by apply: HM.
Qed.

End Construction.

Require Import Undecidability.Synthetic.Definitions.

(* decision procedure for uniform boundedness for mm2 *)
Definition decide : list mm2_instr -> bool :=
  fun M =>
    match decision M with
    | inl _ => true
    | inr _ => false
    end.

(* decision procedure correctness *)
Lemma decide_spec : decider decide MM2_UBOUNDED.
Proof.
  rewrite /decider /reflects /decide => M.
  case: (decision M); intuition done.
Qed.
