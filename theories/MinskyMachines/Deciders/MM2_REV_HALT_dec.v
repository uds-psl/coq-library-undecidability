(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  Decision Procedure(s):
    Reversible Two-counter Machine Halting (MM2_REV_HALT)

  References:
  [1] Dudenhefner, Andrej. "Certified Decision Procedures for Two-Counter Machines."
      FSCD 2022. https://drops.dagstuhl.de/opus/volltexte/2022/16297/
*)

Require Import List PeanoNat Lia Relation_Operators Operators_Properties Transitive_Closure.
Import ListNotations.
Require Import Undecidability.MinskyMachines.MM2.
Require Import Undecidability.MinskyMachines.Util.MM2_facts.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

Import MM2Notations.

(* local facts *)
Module Facts.

Lemma eq_or_inf {X: Type} : (forall (x y: X), {x = y} + {x <> y}) ->
  forall (x y: X) P, (x = y) \/ P -> (x = y) + P.
Proof.
  move=> H x y P. case: (H x y).
  - move=> ??. by left.
  - move=> ??. right. tauto.
Qed.

Lemma iter_plus {X} (f : X -> X) (x : X) n m : Nat.iter (n + m) f x = Nat.iter m f (Nat.iter n f x).
Proof.
  elim: m; first by rewrite Nat.add_0_r.
  move=> m /= <-. by have ->: n + S m = S n + m by lia.
Qed.

Lemma clos_trans_flip {A R} {x y : A} :
  clos_trans A R x y -> clos_trans A (fun y' x' => R x' y') y x.
Proof.
  elim; by eauto using clos_trans with nocore.
Qed.

Lemma clos_rt_clos_t {X R x y }:
  clos_trans _ R x y -> clos_refl_trans X R x y.
Proof.
  elim; eauto using clos_refl_trans with nocore.
Qed.

End Facts.

Import Facts.

Section Construction.
Variable M : list mm2_instr.
Variable HM : mm2_reversible M.

(* partial two counter machine step function without jumps *)
Definition step' (x: mm2_state) : option mm2_state :=
  match (index x) with
  | 0 => None
  | S p => 
    match nth_error M p with
    | None => None (* halting configuration *)
    | Some mm2_inc_a => Some (1 + (index x), (1 + (value1 x), (value2 x)))
    | Some mm2_inc_b => Some (1 + (index x), ((value1 x), 1 + (value2 x)))
    | Some (mm2_dec_a _) => (* halt on jump *)
        if value1 x is 0 then Some (1 + (index x), (0, value2 x)) else None
    | Some (mm2_dec_b _) => (* halt on jump *)
        if value2 x is 0 then Some (1 + (index x), (value1 x, 0)) else None
    end
  end.

Definition steps' n x : option mm2_state :=
  Nat.iter n (obind step') (Some x).

#[local] Notation step := (mm2_step M).
#[local] Notation terminating := (mm2_terminates M).
#[local] Notation non_terminating x := (not (terminating x)).
#[local] Notation reaches := (clos_refl_trans _ step).
#[local] Notation reaches_plus := (clos_trans _ step).

#[local] Arguments Acc_clos_trans {A R x}.
#[local] Arguments rt_trans {A R x y z}.
#[local] Arguments nth_error_In {A l n x}.
#[local] Arguments clos_rt_t {A R x y z}.
#[local] Arguments rt_step {A R x y}.
#[local] Arguments t_step {A R x y}.

Definition reaches' x y := exists k, steps' k x = Some y.

(* step includes step' *)
Lemma step'_incl x y : step' x = Some y -> step x y.
Proof.
  rewrite /step' (mm2_state_eta x) /=.
  case: (index x) => [|p]; first done.
  case Hp: (nth_error M p) => [i|]; last done.
  move: Hp => /nth_error_Some_mm2_instr_at_iff.
  case: i => > Hi.
  - move=> [<-]. eexists. by split; [eassumption|constructor].
  - move=> [<-]. eexists. by split; [eassumption|constructor].
  - case: (value1 x) => [|a]; last done.
    move=> [<-]. eexists. by split; [eassumption|constructor].
  - case: (value2 x) => [|b]; last done.
    move=> [<-]. eexists. by split; [eassumption|constructor].
Qed.

(* steps includes steps' *)
Lemma steps'_incl k x y : steps' k x = Some y -> reaches x y.
Proof.
  elim: k y. { move=> y /= [<-]. by apply: rt_refl. }
  move=> k /=. case: (steps' k x) => [y|]; last done.
  move=> /(_ y erefl) /= Hxy ? /step'_incl ?.
  by apply: rt_trans; [|apply: rt_step]; eassumption.
Qed.

Opaque nth_error.

(* key lemma on the way to ensure that equivalent configurations behave identically
   every steps' computation without jumps increases the starting configuration
   (a > 0 -> value1 x > 0), (b > 0 -> value2 x > 0) in the same way *)
Lemma steps'E k x y : steps' k x = Some y ->
  exists n m, value1 y = value1 x + n /\ value2 y = value2 x + m /\ 
    forall a b, (a > 0 -> value1 x > 0) -> (b > 0 -> value2 x > 0) ->
      steps' k (index x, (a, b)) = Some (index y, (a + n, b + m)).
Proof.
  elim: k x y.
  { move=> x y [<-]. exists 0, 0. do 2 (split; first by lia).
    move=> a b ?? /=. by rewrite ?Nat.add_0_r. }
  move=> k IH x y /=.
  case Hx': (steps' k x) => [x'|]; last done.
  move: Hx' => /IH [n] [m] [Hax'] [Hbx'] {}IH /=.
  rewrite /(step' x').
  move: (index x') IH => [|xp] IH; [done|].
  case Hi: (nth_error M xp) => [i|]; last done.
  move: i Hi => [].
  - move=> Hi [<-] /=. exists (1 + n), m.
    split; first by lia. split; first by lia.
    move=> a b Ha Hb. rewrite IH; [done|done|].
    rewrite /= /step' /= Hi. congr Some. congr pair. congr pair; lia.
  - move=> Hi [<-] /=. exists n, (1 + m).
    split; first by lia. split; first by lia.
    move=> a b Ha Hb. rewrite IH; [done|done|].
    rewrite /= /step' /= Hi. congr Some. congr pair. congr pair; lia.
  - move=> q Hi.
    case H'ax': (value1 x') => [|ax']; last done.
    move=> [<-] /=. exists 0, m.
    split; first by lia. split; first by lia.
    move=> a b ??. rewrite IH; [done|done|].
    rewrite /step' /= Hi. have ->: a + n = 0 by lia.
    congr Some. congr pair. congr pair; lia.
  - move=> q Hi.
    case H'bx': (value2 x') => [|bx']; last done.
    move=> [<-] /=. exists n, 0.
    split; first by lia. split; first by lia.
    move=> a b ??. rewrite IH; [done|done|].
    rewrite /step' /= Hi. have ->: b + m = 0 by lia. 
    congr Some. congr pair. congr pair; lia.
Qed.

Corollary reaches'E x y : reaches' x y ->
  exists n m, value1 y = value1 x + n /\ value2 y = value2 x + m /\ 
    forall a b, (a > 0 -> value1 x > 0) -> (b > 0 -> value2 x > 0) ->
      reaches' (index x, (a, b)) (index y, (a + n, b + m)).
Proof.
  move=> [k] /steps'E [n] [m] [?] [?] H.
  exists n, m. split; [done|split; [done|]].
  move=> ????. exists k. by apply: H.
Qed.

Lemma step'_inc_index x y :
  step' x = Some y -> index y = 1 + (index x).
Proof.
  rewrite /step'. move: (index x) => [|p]; first done.
  case: (nth_error M p); last done.
  move=> [].
  - by move=> [<-].
  - by move=> [<-].
  - move: (value1 x) => [|?]; [|done].
    by move=> _ [<-].
  - move: (value2 x) => [|?]; [|done].
    by move=> _ [<-].
Qed.

Lemma target_index_a p q : nth_error M p = Some (mm2_dec_a q) -> q = 1 \/ (forall a b, mm2_stop M (q, (a, b))).
Proof using HM.
  move: q => [|[|q]].
  - move=> _. right => ??. apply /mm2_stop_index_iff. by left.
  - move=> _. by left.
  - move=> /nth_error_Some_mm2_instr_at_iff Hq. right.
    move=> a b z [?] [/mm2_instr_at_bounds /= ? _].
    case Hi: (nth_error M q) => [i|]; first last.
    { move: Hi => /nth_error_None. lia. }
    move: Hi => /nth_error_Some_mm2_instr_at_iff. case: i => > Hi.
    + suff: (S p, (2, 0)) = (S q, (0, 0)) by done.
      apply: (HM).
      * eexists. by split; [eassumption|constructor].
      * eexists. by split; [eassumption|constructor].
    + suff: (S p, (1, 1)) = (S q, (0, 0)) by done.
      apply: (HM).
      * eexists. by split; [eassumption|constructor].
      * eexists. by split; [eassumption|constructor].
    + suff: (S p, (1, 0)) = (S q, (0, 0)) by done.
      apply: (HM).
      * eexists. by split; [eassumption|constructor].
      * eexists. by split; [eassumption|constructor].
    + suff: (S p, (1, 0)) = (S q, (0, 0)) by done.
      apply: (HM).
      * eexists. by split; [eassumption|constructor].
      * eexists. by split; [eassumption|constructor].
Qed.

Lemma target_index_b p q : nth_error M p = Some (mm2_dec_b q) -> q = 1 \/ (forall a b, mm2_stop M (q, (a, b))).
Proof using HM.
  move: q => [|[|q]].
  - move=> _. right => ??. apply /mm2_stop_index_iff. by left.
  - move=> _. by left.
  - move=> /nth_error_Some_mm2_instr_at_iff Hq. right.
    move=> a b z [?] [/mm2_instr_at_bounds /= ? _].
    case Hi: (nth_error M q) => [i|]; first last.
    { move: Hi => /nth_error_None. lia. }
    move: Hi => /nth_error_Some_mm2_instr_at_iff. case: i => > Hi.
    + suff: (S p, (1, 1)) = (S q, (0, 0)) by done.
      apply: (HM).
      * eexists. by split; [eassumption|constructor].
      * eexists. by split; [eassumption|constructor].
    + suff: (S p, (0, 2)) = (S q, (0, 0)) by done.
      apply: (HM).
      * eexists. by split; [eassumption|constructor].
      * eexists. by split; [eassumption|constructor].
    + suff: (S p, (0, 1)) = (S q, (0, 0)) by done.
      apply: (HM).
      * eexists. by split; [eassumption|constructor].
      * eexists. by split; [eassumption|constructor].
    + suff: (S p, (0, 1)) = (S q, (0, 0)) by done.
      apply: (HM).
      * eexists. by split; [eassumption|constructor].
      * eexists. by split; [eassumption|constructor].
Qed.

Corollary reaches'_incl {x y} : reaches' x y -> reaches x y.
Proof.
  by move=> [k /steps'_incl].
Qed.

Corollary reaches'I x :
  { y | reaches' x y /\
    (forall z, step y z -> index z = 1 \/ mm2_stop M z) }.
Proof using HM.
  move Hn: ((S (length M)) - index x) => n. elim: n x Hn.
  { move=> x ?. exists x. split; first by exists 0.
    move=> ? [?] [/mm2_instr_at_bounds]. lia. }
  move=> n IH x ?. case Hy: (step' x) => [y|].
  - move: (Hy) => /step'_inc_index ?.
    have /IH : ((S (length M) - index y = n)) by lia.
    move=> [z] [Hyz ?]. exists z. split; last done.
    move: Hyz => [k Hk]. exists (1+k).
    by rewrite /steps' iter_plus /= Hy.
  - exists x. split; first by exists 0.
    move: Hy. rewrite /step' /step.
    rewrite (mm2_state_eta x) /=.
    case: (index x) => [|p]. { move=> _ ? [?] [/mm2_instr_at_bounds]. lia. }
    case Hi: (nth_error M p) => [i|]; first last.
    { move: Hi => /nth_error_None ? _ ? [?] [/mm2_instr_at_bounds]. lia. }
    case: i Hi; [done|done| |].
    + move: (value1 x) => [|a]; first done.
      move=> q /[dup] /target_index_a Hq.
      move=> /nth_error_Some_mm2_instr_at_iff /mm2_instr_at_unique HSp _ ?.
      move=> [?] [/HSp <-] H. inversion H; cbn; subst.
      by case: Hq => ?; [left|right].
    + move: (value2 x) => [|b]; first done.
      move=> q /[dup] /target_index_b Hq.
      move=> /nth_error_Some_mm2_instr_at_iff /mm2_instr_at_unique HSp _ ?.
      move=> [?] [/HSp <-] H. inversion H; cbn; subst.
      by case: Hq => ?; [left|right].
Qed.

(* if (1, 1) f->>t-> (0, 1 + m), then (a, b) t->> (0, a * m + b) *)
Lemma dec_a_0 x m : reaches' (1, (1, 1)) x -> 
  step x (1, (0, 1 + m)) ->
  forall a b, reaches (1, (a, b)) (1, (0, a * m + b)).
Proof.
  move=> H1x H2x. elim.
  - move=> b. by apply: rt_refl.
  - move=> a IH b. move: H1x => /reaches'E [n'] [m'] /= [Hax] [Hbx].
    move=> /(_ (S a) b ltac:(lia) ltac:(lia)).
    move=> /reaches'_incl /rt_trans. apply.
    have ->: m + a * m + b = a * m + (m + b) by lia.
    apply: (rt_trans _ (IH (m + b))).
    apply: rt_step. move Ey: (1, (0, 1 + m)) H2x => y Hxy.
    move: Hxy Ey => [i] [+ Hxy] => /[dup] /mm2_instr_at_pos.
    case: Hxy Hax Hbx => /=.
    1,2,4,5,6: by congruence.
    move=> i' j' a' b' [->] -> -> Hi [] *. subst j' n' m'.
    eexists. split; [eassumption|].
    have [-> ->]: a + 0 = a /\ b + m = m + b by lia.
    by constructor.
Qed.

(* if (1, 1) f->>t-> (1 + n, 0), then (a, b) t->> (b * n + a, 0) *)
Lemma dec_b_0 x n : reaches' (1, (1, 1)) x -> 
  step x (1, (1 + n, 0)) ->
  forall a b, reaches (1, (a, b)) (1, (b * n + a, 0)).
Proof.
  move=> H1x H2x a b. elim: b a.
  - move=> a. by apply: rt_refl.
  - move=> b IH a. move: H1x => /reaches'E [n'] [m'] /= [Hax] [Hbx].
    move=> /(_ (a) (S b) ltac:(lia) ltac:(lia)).
    move=> /reaches'_incl /rt_trans. apply.
    have ->: n + b * n + a = b * n + (n + a) by lia.
    apply: (rt_trans _ (IH (n + a))).
    apply: rt_step. move Ey: (1, (1 + n, 0)) H2x => y Hxy.
    move: Hxy Ey => [i] [+ Hxy] => /[dup] /mm2_instr_at_pos.
    case: Hxy Hax Hbx => /=.
    1,2,3,5,6: by congruence.
    move=> i' j' a' b' -> [->] -> Hi [] *. subst j' n' m'.
    eexists. split; [eassumption|].
    have [-> ->]: b + 0 = b /\ a + n = n + a by lia.
    by constructor.
Qed.

(* if (1, 1) ->> (S a, S b), then (a', b') does not terminate *)
Lemma dec_loop x n m : reaches' (1, (1, 1)) x -> 
  step x (1, (1 + n, 1 + m)) ->
  forall a b, non_terminating (1, (a, b)).
Proof.
  move=> H0x Hx0.
  suff: forall a b, exists a' b', reaches_plus (1, (a, b)) (1, (a', b')).
  { move=> H a b. pose P := fun (x : mm2_state) => index x = 1.
    apply: (mm2_clos_trans_not_terminates P _ (1, (a, b)) erefl).
    move=> [p' [a' b']]. rewrite /P /= => ?.
    have [a'' [b'' H'']] := H a' b'. subst p'. eexists. by split; [eassumption|]. }
  move=> a b. 
  move: (H0x) => /reaches'E [n'] [m'] /= [Hax] [Hbx].
  move=> /(_ a b ltac:(lia) ltac:(lia)).
  move=> /reaches'_incl /clos_rt_t H'.
  move: Hx0 => [i] [/[dup] Hi /mm2_instr_at_pos H''x].
  move Ey: (1, (1 + n, 1 + m)) => y Hxy.
  case: Hxy H''x Ey Hi  H' Hax Hbx => > /=.
  1,2,5,6: by congruence.
  - move=> -> [<- <- <-] Hi H' [?] [?]. subst n' m'.
    exists (a + n), (b + m). apply: H'.
    apply: t_step. have -> : a + S n = S (a + n) by lia.
    by apply: (mm2_step_intro Hi (S (a + n)) (b + m)).
  - move=> -> [<- <- <-] Hi H' [?] [?]. subst n' m'.
    exists (a + n), (b + m). apply: H'.
    apply: t_step. have -> : b + S m = S (b + m) by lia.
    by apply: (mm2_step_intro Hi (a + n) (S (b + m))).
Qed.

Lemma reaches'_None_terminating x y :
  reaches' x y -> mm2_stop M y ->
  forall a b, (a > 0 -> value1 x > 0) -> (b > 0 -> value2 x > 0) -> 
    terminating (index x, (a, b)).
Proof.
  move=> Hx Hy a b ? ?.
  move: Hx => /reaches'E [n] [m] /= [?] [?].
  move=> /(_ a b ltac:(lia) ltac:(lia)) /reaches'_incl.
  move=> /mm2_steps_terminates_l. apply.
  apply: mm2_stop_terminates.
  by apply: (mm2_stop_index_eq Hy).
Qed.

Lemma reaches'_Some_terminating x y z :
  reaches' x y -> step y z -> mm2_stop M z ->
  forall a b, (value1 x > 0 <-> a > 0) -> (value2 x > 0 <-> b > 0) -> 
    terminating (index x, (a, b)).
Proof.
  move=> Hx Hy Hz a b ? ?.
  move: Hx => /reaches'E [n] [m] /= [?] [?].
  move=> /(_ a b ltac:(lia) ltac:(lia)) /reaches'_incl.
  move: Hy => /(mm2_step_parallel (index y, (a + n, b + m))) /= /(_ ltac:(lia)).
  move=> [[pz [az bz]]] /= [?] [?] ?. subst pz.
  move=> /mm2_steps_terminates_l. apply.
  apply: mm2_steps_terminates_l; first by (apply: rt_step; eassumption).
  eexists. split; [by apply: rt_refl|].
  by apply: mm2_stop_index_eq; [eassumption|].
Qed.

Lemma terminating_orI p a b x y : 
  reaches' (p, (S a, S b)) x ->
  step x y ->
  mm2_stop M y ->
  (forall a', terminating (p, (S a', 0))) + (forall b', terminating (p, (0, S b'))).
Proof.
  rewrite (mm2_state_eta x).
  case: (index x) => [|px].
  { move=> _ Hxy _. exfalso. by move: Hxy => [?] [/mm2_instr_at_pos]. }
  case Hi: (nth_error M px) => [i|]; first last.
  { move=> _ Hxy _. exfalso. move: Hxy => [?] [/nth_error_Some_mm2_instr_at_iff]. by rewrite Hi. }
  move: i Hi => [].
  - (* mm2_inc_a instruction *)
    move=> /nth_error_Some_mm2_instr_at_iff Hi Hx H'x Hy. left=> a'.
    move: Hx => /reaches'E [n] [m] /= [?] [?].
    move=> /(_ (S a') 0 ltac:(lia) ltac:(lia)).
    move=> /reaches'_incl /mm2_steps_terminates_l. apply.
    have ? := mm2_step_intro Hi (S a' + n) m.
    apply: mm2_steps_terminates_l.
    + apply: rt_step. eassumption.
    + apply: mm2_stop_terminates. apply: mm2_stop_index_eq; [eassumption|].
      move: H'x => [?] [/mm2_instr_at_unique H'i Hxy].
      move: Hi => /H'i ?. by inversion Hxy; subst.
  - (* mm2_inc_b instruction *)
    move=> /nth_error_Some_mm2_instr_at_iff Hi Hx H'x Hy. right=> b'.
    move: Hx => /reaches'E [n] [m] /= [?] [?].
    move=> /(_ 0 (S b') ltac:(lia) ltac:(lia)).
    move=> /reaches'_incl /mm2_steps_terminates_l. apply.
    have ? := mm2_step_intro Hi n (S b' + m).
    apply: mm2_steps_terminates_l.
    + apply: rt_step. eassumption.
    + apply: mm2_stop_terminates. apply: mm2_stop_index_eq; [eassumption|].
      move: H'x => [?] [/mm2_instr_at_unique H'i Hxy].
      move: Hi => /H'i ?. by inversion Hxy; subst.
  - (* mm2_inc_a instruction *)
    move=> q /nth_error_Some_mm2_instr_at_iff Hi Hx H'x Hy. left=> a'.
    move: Hx => /reaches'E [n] [m] /= [?] [?].
    move=> /(_ (S a') 0 ltac:(lia) ltac:(lia)).
    move=> /reaches'_incl /mm2_steps_terminates_l. apply.
    have ? := mm2_step_intro Hi (S (a' + n)) m.
    apply: mm2_steps_terminates_l.
    + apply: rt_step. eassumption.
    + apply: mm2_stop_terminates. apply: mm2_stop_index_eq; [eassumption|].
      move: H'x => [?] [/mm2_instr_at_unique H'i Hxy].
      move: Hi => /H'i ?. inversion Hxy; subst; by [|cbn; congruence].
  - move=> q /nth_error_Some_mm2_instr_at_iff Hi Hx H'x Hy. right=> b'.
    move: Hx => /reaches'E [n] [m] /= [?] [?].
    move=> /(_ 0 (S b') ltac:(lia) ltac:(lia)).
    move=> /reaches'_incl /mm2_steps_terminates_l. apply.
    have ? := mm2_step_intro Hi n (S (b' + m)).
    apply: mm2_steps_terminates_l.
    + apply: rt_step. eassumption.
    + apply: mm2_stop_terminates. apply: mm2_stop_index_eq; [eassumption|].
      move: H'x => [?] [/mm2_instr_at_unique H'i Hxy].
      move: Hi => /H'i ?. inversion Hxy; subst; by [|cbn; congruence].
Qed.

Lemma transition_loop a b: 
  (forall a' b', (a > 0 <-> a' > 0) -> (b > 0 <-> b' > 0) -> 
     exists a'' b'', reaches_plus (1, (a', b')) (1, (a'', b'')) /\
       (a' > 0 <-> a'' > 0) /\ (b' > 0 <-> b'' > 0)) ->
  non_terminating (1, (a, b)).
Proof.
  move=> H. apply: (mm2_clos_trans_not_terminates 
    (fun '(p', (a', b')) => p' = 1 /\ (a > 0 <-> a' > 0) /\ (b > 0 <-> b' > 0))); last by lia.
  move=> [px [ax bx]] [->] H'.
  move: (H') => [/H] {}H /H [ax'] [bx'] [? ?].
  exists (1, (ax', bx')). split; [done|lia].
Qed.

(* not (1, 1) f->>t-> (0, 0) *)
Lemma not_transition_1_1_to_0_0 x : reaches' (1, (1, 1)) x -> not (step x (1, (0, 0))).
Proof.
  move=> /reaches'E [n] [m] /= [H1x] [H2x] _.
  move Hy: (1, (0, 0)) => y [i] [+ Hxy].
  case: Hxy Hy H1x H2x=> > /= []; lia.
Qed.

Lemma dec_stepI {x y} : step x y -> index y = 1 -> 
  (value1 y < value1 x -> In (mm2_dec_a 1) M) /\
  (value2 y < value2 x -> In (mm2_dec_b 1) M).
Proof.
  move=> [i] [+ Hxy]. case: Hxy => > /=; [lia|lia| | |lia|lia].
  - move=> /[dup] /mm2_instr_at_pos -> /nth_error_Some_mm2_instr_at_iff /nth_error_In *.
    subst. by split; [|lia].
  - move=> /[dup] /mm2_instr_at_pos -> /nth_error_Some_mm2_instr_at_iff /nth_error_In *.
    subst. by split; [lia|].
Qed.

Lemma rev_dec_unique : In (mm2_dec_a 1) M -> In (mm2_dec_b 1) M -> False.
Proof using HM.
  move=> /(@In_nth_error mm2_instr) [p /nth_error_Some_mm2_instr_at_iff Hp].
  move=> /(@In_nth_error mm2_instr) [q /nth_error_Some_mm2_instr_at_iff Hq].
  suff: (S p, (1, 0)) = (S q, (0, 1)) by case.
  apply: (HM); eexists; by split; [eassumption|constructor].
Qed.

(* uniform transition from equivalence class (0, 0) *)
Lemma transition_0_0 :
  (* terminating equivalence class (0, 0) *)
  (terminating (1, (0, 0))) +
  (* non-terminating equivalence class (0, 0) *)
  (non_terminating (1, (0, 0))) +
  (* uniform transition to equivalence class (S a, 0) *)
  (exists a', reaches (1, (0, 0)) (1, (S a', 0))) +
  (* uniform transition to equivalence class (0, S b) *)
  (exists b', reaches (1, (0, 0)) (1, (0, S b'))) +
  (* uniform transition to equivalence class (S a, S b) *)
  (exists a' b', reaches (1, (0, 0)) (1, (S a', S b'))).
Proof using HM.
  have [y [/reaches'_incl H'y]] := reaches'I (1, (0, 0)).
  have [[[pz [az bz]]] Hyz|]:= mm2_sig_step_dec M y; first last.
  { (* termination *)
    move=> Hy _. do 4 left.
    move: H'y => /mm2_steps_terminates_l. apply.
    by apply: mm2_stop_terminates. }
  have H0z : reaches_plus (1, (0, 0)) (pz, (az, bz)).
  { by apply: clos_rt_t; [|apply: t_step]; eassumption. }
  move=> /(_ _ Hyz).
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* termination *)
    move=> H'z. do 4 left.
    eexists. by split; [apply: clos_rt_clos_t|]; eassumption. }
  move=> /= ?. subst pz. move: az bz H0z {Hyz} => [|az] [|bz] H0z.
  - (* non-termination *)
    do 3 left. right. by apply: mm2_loop_not_terminates.
  - (* transition to (0, S b) *)
    do 1 left. right. exists bz. by apply /clos_rt_clos_t.
  - (* transition to (S a, 0) *)
    do 2 left. right. exists az. by apply /clos_rt_clos_t.
  - (* transition to (S a, S b) *)
    right. exists az, bz. by apply /clos_rt_clos_t.
Qed.

(* uniform transition from equivalence class (S a, 0) *)
Lemma transition_Sa_0 :
  (* terminating equivalence class (S a, 0) *)
  (forall a, terminating (1, (S a, 0))) +
  (* non-terminating equivalence class (S a, 0) *)
  (forall a, non_terminating (1, (S a, 0))) +
  (* uniform transition to equivalence class (0, 0) *)
  (forall a, reaches (1, (S a, 0)) (1, (0, 0))) +
  (* uniform transition to equivalence class (0, S b) *)
  (forall a, exists b', reaches (1, (S a, 0)) (1, (0, S b'))) +
  (* uniform transition to equivalence class (S a, S b) *)
  (forall a, exists a' b', reaches (1, (S a, 0)) (1, (S a', S b'))).
Proof using HM.
  have [x' [Hx']] := reaches'I (1, (1, 0)).
  have [[y']|] := mm2_sig_step_dec M x'; first last.
  { (* case: (1, 0) f->> HALT; uniform termination *)
    move=> ??. do 4 left. move=> a. move: Hx' => /reaches'_None_terminating.
    apply=> /=; by [assumption|lia]. }
  move=> /[dup] Hx'y' + H => /H{H}.
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* case: (1, 0) f->>t-> HALT; uniform termination *)
    move: Hx' Hx'y' => /reaches'_Some_terminating H /H {}H /H {}H.
    do 4 left. move=> a. apply: H => /=; lia. }
  move: y' Hx'y' => [py' [ay' [|by']]] + /= Hy'; subst py'.
  { (* case: (1, 0) f->>t-> (_, 0) *)
    move: ay' => [|ay'] H'x'.
    - (* case: (1, 0) f->>t-> (0, 0) uniform transition to (0, 0) *)
      do 2 left. right. move=> a. elim: (S a); first by apply: rt_refl.
      move=> {}a IH. move: Hx' => /reaches'E.
      move=> [n'] [m'] /= [Hax] [Hbx] /(_ (S a) 0 ltac:(lia) ltac:(lia)).
      move=> /reaches'_incl Hk. apply: (rt_trans Hk).
      move: H'x' => /(mm2_step_parallel (index x', (S a + n', m'))) /= /(_ ltac:(lia)).
      move=> [[pz [az bz]]] /= [/rt_step] H [?] ?.
      apply: (rt_trans H). subst pz.
      move: IH. congr reaches. congr (_, (_, _)); lia.
    - (* non-termination *)
      do 3 left. right. move=> a. apply: transition_loop => a' b' ??.
      move: Hx' H'x' => /reaches'E [n] [m] /= [?] [?].
      move=> /(_ a' b' ltac:(lia) ltac:(lia)) /reaches'_incl Hk'.
      move=> /(mm2_step_parallel (index x', (a' + n, b' + m))) /=.
      move=> /(_ ltac:(lia)) [[pz [az bz]]] [/t_step Hz] /= [? ?].
      subst pz. exists az, bz. split; last by lia.
      apply: clos_rt_t; by eassumption. }
  move: ay' => [|ay'] H'x'; first last.
  { (* case: (1, 0) f->>t-> (S a, S b) uniform transition to (S a, S b) *)
    right. move=> a.
    move: Hx' => /reaches'E [n] [m] /= [Hax'] [Hbx'].
    move=> /(_ (S a) 0 ltac:(lia) ltac:(lia)) /reaches'_incl.
    move: H'x' => /(mm2_step_parallel (index x', (S a + n, m))) /=.
    move=> /(_ ltac:(lia)) [[pz' [az' bz']]] /= [/rt_step Hz'] [? ?] Hx'.
    exists (az' - 1), (bz' - 1). apply /(rt_trans Hx').
    move: Hz'. congr reaches. congr (_, (_, _)); lia. }
  (* case: (1, 0) f->>t-> (0, S b) *)
  have := reaches'I (1, (1, 1)).
  move=> [x] [Hx].
  have [[y]|] := mm2_sig_step_dec M x; first last.
  { (* case: (1, 1) f->> HALT; uniform termination *)
    move=> ??. do 4 left. move=> a. move: Hx => /reaches'_None_terminating.
    apply => /=; by [assumption|lia]. }
  move=> /[dup] Hxy + H => /H{H}.
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* case: (1, 1) f->>t-> HALT; uniform termination *)
    move=> Hy. move: (Hx) (Hxy) (Hy) => /terminating_orI => H /H {}H /H {H} [?|HS]; first by (do 4 left).
    do 4 left. move=> [|a].
    { apply: (mm2_steps_terminates_l _ (HS by')).
      by apply: (rt_trans (reaches'_incl Hx') (rt_step H'x')). }
    move: Hx' => /reaches'E [n] [m] /= [?] [?].
    move=> /(_ (S (S a)) 0 ltac:(lia) ltac:(lia)).
    move=> /reaches'_incl /mm2_steps_terminates_l. apply.
    move: H'x' => /(mm2_step_parallel (index x', (S (S a) + n, m))) /=.
    move=> /(_ ltac:(lia)) [[pz' [az' bz']]] /= [Hz'] [?] ?.
    move: Hz' => /rt_step /mm2_steps_terminates_l. apply.
    subst pz'. move: Hx => /reaches'E [n'] [m'] /= [?] [?].
    move=> /(_ az' bz' ltac:(lia) ltac:(lia)).
    move=> /reaches'_incl /mm2_steps_terminates_l. apply.
    move: Hxy => /(mm2_step_parallel (index x, (az' + n', bz' + m'))) /=.
    move=> /(_ ltac:(lia)) [z] [Hz] [?] ?.
    move: Hz => /rt_step /mm2_steps_terminates_l. apply.
    apply: mm2_stop_terminates. by apply: mm2_stop_index_eq; eassumption. }
  (* case (1, 1) f->>t-> (a, b) at index 0 *)
  move=> H0y. move Ha'y: (value1 y) => a'y. move Hb'y: (value2 y) => b'y.
  move: b'y Hb'y => [|b'y] H2y.
  { (* case: (1, 1) f->>t-> (_, 0) impossible *)
    exfalso. apply: rev_dec_unique.
    + apply: (proj1 (dec_stepI H'x' ltac:(done))).
      move: Hx' => /reaches'E [n] [m] /= [?] [?]. lia.
    + apply: (proj2 (dec_stepI Hxy H0y)).
      move: Hx => /reaches'E [n] [m] /= [?] [?]. lia. }
  move: a'y Ha'y => [|a'y] H1y.
  - (* case: (1, 1) f->>t-> (0, S b') uniform transition to (0, Sb') *)
    do 1 left. right. move=> a.
    move: Hx' => /reaches'E [n] [m] /= [?] [?].
    move=> /(_ (S a) 0 ltac:(lia) ltac:(lia)) /reaches'_incl Hk'.
    move: H'x' => /(mm2_step_parallel (index x', (S a + n, m))) /=.
    move=> /(_ ltac:(lia)) [y'] [/rt_step Hy'] [H0y'] ?.
    move: Hx Hxy => /dec_a_0 H. rewrite (mm2_state_eta y) H0y H1y H2y.
    move=> /H {H} => /(_ a (S by')) Hk''.
    exists (a * b'y + by').
    apply /(rt_trans Hk') /(rt_trans Hy').
    rewrite (mm2_state_eta y').
    move: Hk''. congr reaches; congr (_, (_, _)); lia.
  - (* case: (1, 1) f->>t-> (S a', S b') loop *)
    do 3 left. right. move=> a. apply: dec_loop; [eassumption|].
    move: Hxy. rewrite (mm2_state_eta y) H0y H1y H2y. apply.
Qed.

(* uniform transition from equivalence class (0, S b) *)
Lemma transition_0_Sb :
  (* terminating equivalence class *)
  (forall b, terminating (1, (0, S b))) +
  (* non-terminating equivalence class*)
  (forall b, non_terminating (1, (0, S b))) +
  (* uniform transition to equivalence class (0, 0) *)
  (forall b, reaches (1, (0, S b)) (1, (0, 0))) +
  (* uniform transition to equivalence class (S a, 0) *)
  (forall b, exists a', reaches (1, (0, S b)) (1, (S a', 0))) +
  (* uniform transition to equivalence class (S a, S b) *)
  (forall b, exists a' b', reaches (1, (0, S b)) (1, (S a', S b'))).
Proof using HM.
  have [x' [Hx']] := reaches'I (1, (0, 1)).
  have [[y']|] := mm2_sig_step_dec M x'; first last.
  { (* case: (0, 1) f->> HALT; uniform termination *)
    move=> ??. do 4 left. move=> b. move: Hx' => /reaches'_None_terminating.
    apply=> /=; by [assumption|lia]. }
  move=> /[dup] Hx'y' + H => /H{H}.
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* case: (0, 1) f->>t-> HALT; uniform termination *)
    move: Hx' Hx'y' => /reaches'_Some_terminating H /H {}H /H {}H.
    do 4 left. move=> b. apply: H => /=; lia. }
  move: y' Hx'y' => [py' [[|ay'] by']] + /= Hy'; subst py'.
  { (* case: (0, 1) f->>t-> (0, _) *)
    move: by' => [|by'] H'x'.
    - (* case: (0, 1) f->>t-> (0, 0) uniform transition to (0, 0) *)
      do 2 left. right. move=> b. elim: (S b); first by apply: rt_refl. 
      move=> {}b IH. move: Hx' => /reaches'E.
      move=> [n'] [m'] /= [Hax] [Hbx] /(_ 0 (S b) ltac:(lia) ltac:(lia)).
      move=> /reaches'_incl Hk. apply: (rt_trans Hk).
      move: H'x' => /(mm2_step_parallel (index x', (n', S b + m'))) /= /(_ ltac:(lia)).
      move=> [[pz [az bz]]] /= [/rt_step] H [?] ?.
      apply: (rt_trans H). subst pz.
      move: IH. congr reaches. congr (_, (_, _)); lia.
    - (* non-termination *)
      do 3 left. right. move=> b. apply: transition_loop => a' b' ??.
      move: Hx' H'x' => /reaches'E [n] [m] /= [?] [?].
      move=> /(_ a' b' ltac:(lia) ltac:(lia)) /reaches'_incl Hk'.
      move=> /(mm2_step_parallel (index x', (a' + n, b' + m))) /=.
      move=> /(_ ltac:(lia)) [[pz [az bz]]] [/t_step Hz] /= [? ?].
      subst pz. exists az, bz. split; last by lia.
      apply: clos_rt_t; by eassumption. }
  move: by' => [|by'] H'x'; first last.
  { (* case: (0, 1) f->>t-> (S a, S b) uniform transition to (S a, S b) *)
    right. move=> b.
    move: Hx' => /reaches'E [n] [m] /= [Hax'] [Hbx'].
    move=> /(_ 0 (S b) ltac:(lia) ltac:(lia)) /reaches'_incl.
    move: H'x' => /(mm2_step_parallel (index x', (n, S b + m))) /=.
    move=> /(_ ltac:(lia)) [[pz' [az' bz']]] /= [/rt_step Hz'] [? ?] Hx'.
    exists (az' - 1), (bz' - 1). apply /(rt_trans Hx').
    move: Hz'. congr reaches. congr (_, (_, _)); lia. }
  (* case: (0, 1) f->>t-> (S a, 0) *)
  have := reaches'I (1, (1, 1)).
  move=> [x] [Hx].
  have [[y]|] := mm2_sig_step_dec M x; first last.
  { (* case: (1, 1) f->> HALT; uniform termination *)
    move=> ??. do 4 left. move=> b. move: Hx => /reaches'_None_terminating.
    apply => /=; by [assumption|lia]. }
  move=> /[dup] Hxy + H => /H{H}.
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* case: (1, 1) f->>t-> HALT; uniform termination *)
    move=> Hy. move: (Hx) (Hxy) (Hy) => /terminating_orI => H /H {}H /H {H} [HS|?]; last by (do 4 left).
    do 4 left. move=> [|b].
    { apply: (mm2_steps_terminates_l _ (HS ay')).
      by apply: (rt_trans (reaches'_incl Hx') (rt_step H'x')). }
    move: Hx' => /reaches'E [n] [m] /= [?] [?].
    move=> /(_ 0 (S (S b)) ltac:(lia) ltac:(lia)).
    move=> /reaches'_incl /mm2_steps_terminates_l. apply.
    move: H'x' => /(mm2_step_parallel (index x', (n, S (S b) + m))) /=.
    move=> /(_ ltac:(lia)) [[pz' [az' bz']]] /= [Hz'] [?] ?.
    move: Hz' => /rt_step /mm2_steps_terminates_l. apply.
    subst pz'. move: Hx => /reaches'E [n'] [m'] /= [?] [?].
    move=> /(_ az' bz' ltac:(lia) ltac:(lia)).
    move=> /reaches'_incl /mm2_steps_terminates_l. apply.
    move: Hxy => /(mm2_step_parallel (index x, (az' + n', bz' + m'))) /=.
    move=> /(_ ltac:(lia)) [z] [Hz] [?] ?.
    move: Hz => /rt_step /mm2_steps_terminates_l. apply.
    apply: mm2_stop_terminates. by apply: mm2_stop_index_eq; eassumption. }
  (* case (1, 1) f->>t-> (a, b) at index 0 *)
  move=> H0y. move Ha'y: (value1 y) => a'y. move Hb'y: (value2 y) => b'y.
  move: a'y Ha'y => [|a'y] H1y.
  { (* case: (1, 1) f->>t-> (0, _) impossible *)
    exfalso. apply: rev_dec_unique.
    + apply: (proj1 (dec_stepI Hxy H0y)).
      move: Hx => /reaches'E [n] [m] /= [?] [?]. lia.
    + apply: (proj2 (dec_stepI H'x' ltac:(done))).
      move: Hx' => /reaches'E [n] [m] /= [?] [?]. lia. }
  move: b'y Hb'y => [|b'y] H2y.
  - (* case: (1, 1) f->>t-> (S a', 0) uniform transition to (S a', 0') *)
    do 1 left. right. move=> b.
    move: Hx' => /reaches'E [n] [m] /= [?] [?].
    move=> /(_ 0 (S b) ltac:(lia) ltac:(lia)) /reaches'_incl Hk'.
    move: H'x' => /(mm2_step_parallel (index x', (n, S b + m))) /=.
    move=> /(_ ltac:(lia)) [y'] [/rt_step Hy'] [H0y'] ?.
    move: Hx Hxy => /dec_b_0 H. rewrite (mm2_state_eta y) H0y H1y H2y.
    move=> /H {H} => /(_ (S ay') b) Hk''.
    exists (b * a'y + ay').
    apply /(rt_trans Hk') /(rt_trans Hy').
    rewrite (mm2_state_eta y').
    move: Hk''. congr reaches; congr (_, (_, _)); lia.
  - (* case: (1, 1) f->>t-> (S a', S b') loop *)
    do 3 left. right. move=> b. apply: dec_loop; [eassumption|].
    move: Hxy. rewrite (mm2_state_eta y) H0y H1y H2y. apply.
Qed.

(* uniform transition from equivalence class (S a, S b) *)
Lemma transition_Sa_Sb :
  (* terminating equivalence class (S a, 0) *)
  (forall a b, terminating (1, (S a, S b))) +
  (* non-terminating equivalence class (S a, 0) *)
  (forall a b, non_terminating (1, (S a, S b))) +
  (* uniform transition to equivalence class (0, 0) *)
  (forall a b, reaches (1, (S a, S b)) (1, (0, 0))) +
  (* uniform transition to equivalence class (S a, 0) *)
  (forall a b, exists a', reaches (1, (S a, S b)) (1, (S a', 0))) +
  (* uniform transition to equivalence class (0, S b) *)
  (forall a b, exists b', reaches (1, (S a, S b)) (1, (0, S b'))).
Proof using HM.
  have := reaches'I (1, (1, 1)).
  move=> [x] [H0x].
  have [[y H'x]|] := mm2_sig_step_dec M x; first last.
  { (* case: (1, 1) f->> HALT; uniform termination *)
    move=> Hy _. do 4 left. move=> a b.
    move: H0x Hy => /reaches'_None_terminating /[apply] /=. apply; lia. }
  move=> /(_ _ H'x).
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* case: (1, 0) f->>t-> HALT; uniform termination *)
    move: H0x H'x => /reaches'_Some_terminating /[apply] /[apply] H.
    do 4 left. move=> a b. apply: H => /=; lia. }
  move: y H'x => [py' [[|ay'] [|by']]] H'x /= Hy'; subst py'.
  - (* case: (1, 1) f->>t-> (0, 0) impossible *)
    by move: H0x H'x => /not_transition_1_1_to_0_0 /[apply].
  - (* case: (1, 1) f->>t-> (0, S b) uniform transition to (0, S b) *)
    right. move=> a b.
    move: H0x H'x => /dec_a_0 H /H /(_ (S a) (S b)) Hk'.
    exists (S a * by' + S b - 1).
    move: Hk'. congr reaches. congr (_, (_, _)); lia.
  - (* case: (1, 1) f->>t-> (S a, 0) uniform transition to (S a, 0) *)
    do 1 left. right. move=> a b.
    move: H0x H'x => /dec_b_0 H /H /(_ (S a) (S b)) Hk'.
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

Lemma reaches_neq_incl {x y} : reaches x y -> x <> y -> reaches_plus x y.
Proof.
  move=> /clos_rt_rtn1_iff []; [done|].
  move=> ??? /clos_rt_rtn1_iff? _.
  by apply: clos_rt_t; [|apply: t_step]; eassumption.
Qed.

Lemma uniform_transition ab :
  In ab representatives -> 
  (* uniform termination *)
  (forall a'b', RZ ab a'b' -> terminating (1, a'b')) +
  (* uniform non-termination *)
  (forall a'b', RZ ab a'b' -> non_terminating (1, a'b')) +
  (* uniform transition *)
  {v | In v representatives /\
    (forall a'b', RZ ab a'b' -> exists w, RZ v w /\ reaches_plus (1, a'b') (1, w)) }.
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
    exists a'b', RZ v a'b' /\ reaches_plus (1, ab) (1, a'b')) ->
  forall ab, RZ v ab -> non_terminating (1, ab).
Proof.
  move=> Hv ab Hab [z] [/mm2_terminates_Acc] /[apply] /Acc_clos_trans.
  move Ex: (1, ab) => x Hx.
  elim: Hx ab Ex Hab => {}x _ IH ab ? Hab. subst x.
  have [a'b' [Ha'b' /clos_trans_flip Ha'b'ab]] := Hv ab Hab.
  by apply: (IH _ Ha'b'ab a'b').
Qed.

Lemma uniform_representative_decision v :
  In v representatives -> 
  (* uniform termination *)
  (forall ab, RZ v ab -> terminating (1, ab)) +
  (* uniform non-termination *)
  (forall ab, RZ v ab -> non_terminating (1, ab)).
Proof using HM.
  move: v.
  have: { L & incl L representatives & 
    (forall v, In v representatives -> 
    (forall ab, RZ v ab -> terminating (1, ab)) + (forall ab, RZ v ab -> non_terminating (1, ab)) +
    { w | In w L /\
      (forall ab, RZ v ab -> exists a'b', RZ w a'b' /\ reaches_plus (1, ab) (1, a'b')) } ) }.
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
    by move=> /mm2_steps_terminates_l H /clos_rt_clos_t /H.
  - (* non-termination *)
    move=> Hv0 Hv. left. right=> ab /Hv [a'b'] [/Hv0].
    by move=> /mm2_steps_not_terminates_l H /clos_rt_clos_t /H.
  - (* chaining *)
    move=> [w'] /= [/HE [|]].
    + (* non-termination *)
      move=> <- /RZ_loop Hv0 Hv. left. right=> ab /Hv [a'b'] [/Hv0].
      by move=> /mm2_steps_not_terminates_l H /clos_rt_clos_t /H.
    + move=> ? Hv0 Hv. right. exists w'. split; first done.
      move=> ab /Hv [a'b'] [/Hv0] [a''b''] [? HSk'] HSk.
      exists a''b''. split; first done.
      by apply: t_trans; eassumption.
Qed.

Lemma uniform_decision_0 a b : (terminating (1, (a, b))) + (non_terminating (1, (a, b))).
Proof using HM.
  have [v []] := get_representative (a, b).
  move=> /uniform_representative_decision [] => H /H; tauto.
Qed.

(* informative decision statement for reversible halting for mm2 *)
Theorem decision (c: mm2_state) : (terminating c) + (not (terminating c)).
Proof using HM.
  have [y [/reaches'_incl Hk]] := reaches'I c.
  have [[[pz [az bz]] Hyz]|] := mm2_sig_step_dec M y; first last.
  { (* termination *)
    move=> ??. left. apply: (mm2_steps_terminates_l Hk).
    by apply: mm2_stop_terminates. }
  have Hcz : reaches c (pz, (az, bz)).
  { apply: rt_trans; [|apply: rt_step]; by eassumption. }
  move=> /(_ _ Hyz).
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* termination *)
    move=> ?. left.
    move: Hcz => /mm2_steps_terminates_l. apply.
    by apply: mm2_stop_terminates. }
  move=> /= ?. subst pz. case: (uniform_decision_0 az bz).
  - (* termination *)
    move=> /mm2_steps_terminates_l H'z. left. by apply: H'z.
  - (* non-termination *)
    move=> /mm2_steps_not_terminates_l H'z. right. by apply: H'z.
Qed.

End Construction.

Require Import Undecidability.Synthetic.Definitions.

(* decision procedure for the halting problem for reversible mm2 *)
Definition decide : { M: list mm2_instr | mm2_reversible M } * mm2_state -> bool :=
  fun '(exist _ M HM, c) =>
    match decision M HM c with
    | inl _ => true
    | inr _ => false
    end.

(* decision procedure correctness *)
Lemma decide_spec : decider decide MM2_REV_HALT.
Proof.
  rewrite /decider /reflects /decide => - [[M HM] c].
  case: (decision M HM c).
  - tauto.
  - move=> H. split; [by move=> /H | done].
Qed.
