(*
  Autor(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  Decision Procedure(s):
    Two-counter Machine Uniform Boundedness (CM2_UBOUNDED)
*)

Require Import List ListDec PeanoNat Lia Relation_Operators Operators_Properties.
Import ListNotations.
Require Import Undecidability.CounterMachines.CM2.
From Undecidability.CounterMachines.Util Require Import Facts CM2_facts.
Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

Section Construction.
Variable M : Cm2.

#[local] Notation steps := (CM2.steps M).
#[local] Notation bounded := (CM2.bounded M).
#[local] Notation step := (CM2.step M).
#[local] Notation reaches := (CM2.reaches M).
#[local] Notation path := (CM2_facts.path M).

Lemma pointwise_decision K x : {bounded K x} + {not (bounded K x)}.
Proof.
  case HK: (steps K x) => [y|].
  - have [Hy|Hy] := In_dec option_Config_eq_dec (Some y) (path K x).
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
  move=> ?. rewrite [LHS]shift_steps [in RHS]shift_steps.
  have ->: Nat.min k (K + a) = k by lia.
  have ->: Nat.min k K = k by lia.
  case: (steps k _) => [[? [? ?]]|]; last done.
  congr (Some (_, (_, _))); lia.
Qed.

Lemma shift_steps_b k K p a b :
  k <= K ->
  steps k (p, (a, K + b)) =
  match steps k (p, (a, K)) with
  | Some (p', (a', b')) => Some (p', (a', b' + b))
  | None => None
  end.
Proof.
  move=> ?. rewrite [LHS]shift_steps [in RHS]shift_steps.
  have ->: Nat.min k (K + b) = k by lia.
  have ->: Nat.min k K = k by lia.
  case: (steps k _) => [[? [? ?]]|]; last done.
  congr (Some (_, (_, _))); lia.
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

Lemma fixed_decision K :
  {forall x : Config, bounded K x} + {~ (forall x : Config, bounded K x)}.
Proof.
  (* need to check configurations up to values K *)
  have := Forall_dec (fun 'x => bounded K x) (pointwise_decision K)
    (list_prod (seq 0 (length M)) (list_prod (seq 0 (K+1)) (seq 0 (K+1)))).
  case; first last.
  { move=> H. right => HK. apply /H /Forall_forall. move=> ??. by apply: HK. }
  wlog: K /(0 < K).
  { move: K => [|K] H HK.
    - right. move=> /(_ (0, (0, 0))) [[|? L] [/= ? /(_ (0, (0, 0))) HL]].
      + apply: HL. by exists 0.
      + lia.
    - apply: H; [lia|done]. }
  move=> ? HK. left => x.
  have [|/path_noloopI] := In_dec option_Config_eq_dec (steps K x) (path K x).
  { by apply: loop_bounded. }
  case Hz: (steps K x) => [z|]; first last.
  { move=> _. by apply: mortal_bounded. }
  (* not bounded *)
  move=> Hx. exfalso.
  move: x Hx Hz => [p [a b]] Hx Hz.
  have Hp : not (length M <= p).
  { move=> /nth_error_None HM. move: Hz. have -> : K = S (K - 1) by lia.
    by rewrite /steps /= obind_oiter /step /= HM oiter_None. }
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

Notation l := (length M).

(* from an arbitrary config arrive at config with at least one large value *)
Lemma uniform_decision_aux1 x : let n := l*(l+1) in
  (bounded (l*n*n+1) x) +
  { y | (exists k, k <= l*n*n /\ steps k x = Some y) /\ (n <= value1 y \/ n <= value2 y) }.
Proof.
  move=> n.
  have [|/path_noloopI Hx] :=
    In_dec option_Config_eq_dec (steps (l*n*n) x) (path (l*n*n) x).
  { move=> /loop_bounded H. left. apply: (bounded_monotone _ H). lia. }
  case Hxy: (steps (l*n*n+1) x) => [y|]; first last.
  { left. by apply: mortal_bounded. }
  right.
  have [/pigeonhole|] := incl_dec option_Config_eq_dec (path (l*n*n+1) x)
    (map Some (list_prod (seq 0 l) (list_prod (seq 0 n) (seq 0 n)))).
  { move=> H. exfalso. apply: (H _ Hx).
    rewrite path_length map_length ?prod_length ?seq_length. lia. }
  move=> /(not_inclE option_Config_eq_dec) [[z|]].
  - move=> H. exists z.
    move: H => [/in_map_iff] [k] [Hk] /in_seq ? H.
    have H'z : not (l <= state z).
    { move=> /nth_error_None Hz.
      have : steps (S k) x = None by rewrite /= Hk /= /step Hz.
      move=> /(steps_k_monotone (l*n*n+1)) /(_ ltac:(lia)).
      by rewrite Hxy. }
    split. { exists k. split; [lia|done]. }
    suff : not (value1 z < n /\ value2 z < n) by lia.
    move=> H'. apply: H. apply /in_map_iff. exists z. split; first done.
    move: z {Hk} H'z H' => [? [? ?]] /= ??.
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
  rewrite /= /steps iter_plus -/(steps _ _).
  have := IH (a2+a) (b2+b). congr eq; first last.
  { congr (Some (_, (_, _))); lia. }
  congr Nat.iter.
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

(* probably too much? *)
Lemma not_uniformly_boundedI k p a1 b1 a2 b2 :
  (k <= a1 \/ a1 = a2) -> (k <= b1 \/ b1 = b2) -> 
  (a1 <> a2 \/ b1 <> b2) ->
  steps k (p, (a1, b1)) = Some (p, (a2, b2)) ->
  not (uniformly_bounded M).
Proof.
  move=> /k_step_iter H /H {}H Hab /H /= + [K].
  move=> /(_ _ K 0 0) /=.
  move Ha: (a1 + _ * _) => a.
  move Hb: (b1 + _ * _) => b.
  move=> {}H /(_ (p, (a, b))) [L [? HL]].
  have : incl (map (fun i => steps (i * k) (p, (a, b))) (seq 0 (K+1))) (map Some L).
  { move=> z /in_map_iff [i] [<- /in_seq ?]. rewrite H; first by lia.
    apply: in_map. apply: HL. exists (i*k). rewrite H; [lia|done]. }
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
  (bounded (l*l+1) x) + (not (uniformly_bounded M)) +
    { y | (exists k, k <= l*l /\ steps k x = Some y) /\ (l <= value1 y /\ l <= value2 y) }.
Proof.
  move=> Hlx.
  have [|/path_noloopI Hx] :=
    In_dec option_Config_eq_dec (steps (l*l) x) (path (l*l) x).
  { move=> /loop_bounded H. left. left. apply: (bounded_monotone _ H). lia. }
  case Hxy: (steps (l*l+1) x) => [y|]; first last.
  { left. left. by apply: mortal_bounded. }
  pose P oz := if oz is Some z then 
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
    (list_prod (seq 0 l) (seq 0 l)).
  { move=> [p c] /in_map_iff [[[p' [a' b']]|]]; first last.
    { move=> [_ /In_pathE].
      move=> [?] [?] /(steps_k_monotone (l * l + 1)) /(_ ltac:(lia)).
      by rewrite Hxy. }
    move=> [+ H]. have ? : not (l <= p').
    { move=> /nth_error_None Hp. move: H => /in_map_iff [k] [Hk /in_seq ?].
      have : steps (S k) x = None by rewrite /= Hk /step /= Hp.
      move=> /(steps_k_monotone (l*l+1)) /(_ ltac:(lia)).
      by rewrite Hxy. }
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
    rewrite seq_app seq_app /= ?map_app /= (NoDup_count_occ option_Config_eq_dec).
    move=> /(_ (Some (p, (a1, b1)))). have ->: i + S (j - i - 1) = j by lia.
    rewrite Hi Hj ?count_occ_app /=. case: (option_Config_eq_dec _ _); [lia|done]. }
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
Lemma uniform_decision_aux3 x : l <= value1 x -> l <= value2 x -> (bounded (l+1) x) + (not (uniformly_bounded M)).
Proof.
  move=> ??.
  have [|/path_noloopI Hx] :=
    In_dec option_Config_eq_dec (steps (l) x) (path (l) x).
  { move=> /loop_bounded H. left. apply: (bounded_monotone _ H). lia. }
  case Hxy: (steps (l+1) x) => [y|]; first last.
  { left. by apply: mortal_bounded. }
  right. (* not uniformly bounded *)
  have /pigeonhole : incl
    (map (fun oz => if oz is Some (p, (a, b)) then p else 0) (path (l + 1) x))
    (seq 0 l).
  { move=> p /in_map_iff [[[p' [a' b']]|]]; first last.
    { move=> [_ /In_pathE].
      move=> [?] [?] /(steps_k_monotone (l + 1)) /(_ ltac:(lia)).
      by rewrite Hxy. }
    move=> [->] H. apply /in_seq. suff : not (l <= p) by lia.
    move=> /nth_error_None Hp. move: H => /in_map_iff [k] [Hk /in_seq ?].
    have : steps (S k) x = None by rewrite /= Hk /step /= Hp.
    move=> /(steps_k_monotone (l+1)) /(_ ltac:(lia)).
    by rewrite Hxy. }
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
    rewrite seq_app seq_app /= ?map_app /= (NoDup_count_occ option_Config_eq_dec).
    move=> /(_ (Some (p, (a1, b1)))). have ->: i + S (j - i - 1) = j by lia.
    rewrite Hi Hj ?count_occ_app /=. case: (option_Config_eq_dec _ _); [lia|done]. }
  have ?: j - i <= a1 /\ j - i <= b1.
  { move: Hi => /steps_values_bound /=. lia. }
  move: Hi Hj => /steps_sub H /H{H} /(_ ltac:(lia)).
  move=> /not_uniformly_boundedI. apply; lia.
Qed.

Lemma uniformly_bounded_empty : uniformly_bounded [].
Proof.
  exists 1. move=> x. exists [x]. split; first done.
  move=> y [[|k]].
  - move=> [<-]. by left.
  - rewrite /= obind_oiter /CM2.step.
    by case: (state x); rewrite /= oiter_None.
Qed.

(* a uniformly bounded machine M is uniformly bounded by (|M|+1)^5 *)
Lemma bound_on_uniform_bound : uniformly_bounded M ->
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

(* informative decision statement for uniform boundedness for Cm2 *)
Theorem decision : (uniformly_bounded M) + (not (uniformly_bounded M)).
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

(* decision procedure for uniform boundedness for Cm2 *)
Definition decide : Cm2 -> bool :=
  fun M =>
    match decision M with
    | inl _ => true
    | inr _ => false
    end.

(* decision procedure correctness *)
Lemma decide_spec : decider decide CM2_UBOUNDED.
Proof.
  rewrite /decider /reflects /decide => M.
  case: (decision M); intuition done.
Qed.
