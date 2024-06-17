(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(*
  Reduction from:
    Two Counter Machine Halting starting from (0, 0) (MM2_ZERO_HALTING)
  to:
    Simple Semi-Thue System 01 Rewriting (SSTS01)
*)

Require Import List Relation_Operators Operators_Properties.
Require Import PeanoNat Lia.
Import ListNotations.

Require Undecidability.StringRewriting.SSTS.
Require Undecidability.MinskyMachines.MM2.
Require Undecidability.MinskyMachines.Util.MM2_facts.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

(* auxiliary list facts *)
Module Facts.
Lemma Forall_repeatI {X : Type} {P : X -> Prop} {x n} : 
  P x -> Forall P (repeat x n).
Proof.
  elim: n; first by constructor.
  move=> ? IH ?. constructor; [done | by apply: IH].
Qed.

Lemma In_appl {X : Type} {x: X} {l1 l2: list X} : In x l1 -> In x (l1 ++ l2).
Proof. move=> ?. apply: in_or_app. by left. Qed.

Lemma In_appr {X : Type} {x: X} {l1 l2: list X} : In x l2 -> In x (l1 ++ l2).
Proof. move=> ?. apply: in_or_app. by right. Qed.
End Facts.

Import Facts.

(* Auxiliary, richer rewriting system to encode mm2 computation *)
Module SR2ab.

(* Pair of (symbol type, optional mm2 program counter)
   to encode a mm2 configuration as a list of symbols *)
Definition Symbol : Set := nat * option nat.

(* rules ab -> cd *)
Definition Srs := list ((Symbol * Symbol) * (Symbol * Symbol)).

Inductive step (srs: Srs) : list Symbol -> list Symbol -> Prop := 
  | step_intro {u v a b c d} : 
      In ((a, b), (c, d)) srs -> step srs (u ++ a :: b :: v) (u ++ c :: d :: v).

Definition multi_step (srs: Srs) : list Symbol -> list Symbol -> Prop := 
  clos_refl_trans (list Symbol) (step srs).

Lemma sym_eq_dec (x y: Symbol) : {x = y} + {x <> y}.
Proof. by do 3 (decide equality). Qed.

Lemma stepI {srs u v a b c d s t} : 
  s = (u ++ a :: b :: v) -> t = (u ++ c :: d :: v) -> In ((a, b), (c, d)) srs ->
  step srs s t.
Proof. move=> -> ->. by constructor. Qed.

Lemma multi_step_appI {srs u v s t} : multi_step srs s t -> multi_step srs (u ++ s ++ v) (u ++ t ++ v).
Proof.
  elim; [| move=> *; by apply: rt_refl | move=> *; apply: rt_trans; by eassumption ].
  move=> {}s {}t [] u' v' > ?. 
  apply /rt_step /(stepI (u := u ++ u') (v := v' ++ v)); last by eassumption.
  all: by rewrite -?app_assoc.
Qed.

Lemma multi_step_applI {srs u s t} : multi_step srs s t -> multi_step srs (u ++ s) (u ++ t).
Proof. move=> /multi_step_appI => /(_ u []). by rewrite ?app_nil_r. Qed.

Lemma multi_step_apprI {srs v s t} : multi_step srs s t -> multi_step srs (s ++ v) (t ++ v).
Proof. by move=> /multi_step_appI => /(_ [] v). Qed.

Import MM2 MM2_facts.

Local Arguments rt_trans {A R x y z}.
Local Arguments in_combine_l {A B l l' x y}.
Local Notation mm2_state := (nat*(nat*nat))%type.

Section Reduction.
(* given two-counter machine *)
Context (mm : list mm2_instr).

Lemma instr_at_in_combine {i x}:
  mm2_instr_at x i mm -> In (i, x) (combine (seq 1 (length mm)) mm).
Proof.
  move=> [mml] [mmr] [-> <-].
  suff: forall n, In (n + length mml, x)
    (combine (seq n (length (mml ++ x :: mmr))) (mml ++ x :: mmr)) by apply.
  elim: mml => >. { rewrite /= Nat.add_0_r. by left. }
  move=> IH n /=. right. rewrite -Nat.add_succ_comm. by apply: IH.
Qed.

#[local] Arguments in_split {A x l}.

Lemma inv_instr_at_in_combine {i x}:
  In (i, x) (combine (seq 1 (length mm)) mm) -> mm2_instr_at x i mm.
Proof.
  move=> /in_split [l] [r] Hlr.
  exists (map snd l), (map snd r). move: Hlr.
  suff: forall mm n, combine (seq n (length mm)) mm = l ++ (i, x) :: r ->
    mm = map snd l ++ x :: map snd r /\ n + length (map snd l) = i by apply.
  elim: l.
  { move=> [|mm2i mm'] n /=; [done|].
    move=> [-> ->] <-. split; [|lia].
    congr cons. elim: mm' (S i). { done. }
    by move=> > + ? /= => <-. }
  move=> [i' mm2i'] l IH [|mm2i mm'] n /=; [done|].
  move=> [-> ->] /IH [-> <-]. by split; [|lia].
Qed.

Local Arguments List.app : simpl never.
Local Arguments Nat.sub : simpl never.
Local Arguments repeat : simpl never.
Local Arguments app_inj_tail {A x y a b}.

Local Notation sb := ((0, @None nat)). (* blank *)
Local Notation sl := ((1, @None nat)). (* left marker *)
Local Notation sr := ((2, @None nat)). (* right marker *)
Local Notation sm := ((3, @None nat)). (* middle marker *)

Local Notation sz := ((4, @None nat)). (* 0 *)
Local Notation so := ((5, @Some nat 0)). (* 1 *)
Local Notation st := ((6, @None nat)). (* temporary marker *)

Local Notation sb' p := ((0, @Some nat p)). (* blank *)
Local Notation sl' p := ((1, @Some nat p)). (* left marker *)
Local Notation sr' p := ((2, @Some nat p)). (* right marker *)
Local Notation sm' p := ((3, @Some nat p)). (* middle marker *)

Definition instr_state (mm2i : mm2_instr) :=
  match mm2i with
  | mm2_dec_a q => q
  | mm2_dec_b q => q
  | _ => 0
  end.

Definition state_bound := 2 + length mm + list_sum (map instr_state mm).

(* encode instruction i at position n *)
Definition enc_Instruction (ni: (nat * mm2_instr)) : Srs :=
  match ni with
  | (p, mm2_inc_a) => [((sz, sl' p), (sl' (S p), sb))]
  | (p, mm2_inc_b) => [((sr' p, sz), (sb, sr' (S p)))]
  | (p, mm2_dec_a q) => [((sl' p, sm), (sl' (S p), sm)); ((sl' p, sb), (sz, sl' q))]
  | (p, mm2_dec_b q) => [((sm, sr' p), (sm, sr' (S p))); ((sb, sr' p), (sr' q, sz))] 
  end.

(* constructed string rewriting system *)
Definition srs : Srs := 
  (* initialization *)
  [((sz, sz), (st, sr)); (* 00 -> tr *)
   ((sz, st), (sl' 1, sm)) (* 0t -> l_1 m *)] ++
  (* simulation *)
  flat_map enc_Instruction (combine (seq 1 (length mm)) mm) ++
  (* state movement to the right *)
  flat_map (fun p => [
    ((sl' p, sb), (sl, sb' p)); ((sl' p, sm), (sl, sm' p)); 
    ((sb' p, sb), (sb, sb' p)); ((sb' p, sm), (sb, sm' p)); ((sb' p, sr), (sb, sr' p));
    ((sm' p, sb), (sm, sb' p)); ((sm' p, sr), (sm, sr' p))]) (seq 0 state_bound) ++
  (* state movement to the left *)
  flat_map (fun p => [
    ((sb, sr' p), (sb' p, sr)); ((sm, sr' p), (sm' p, sr)); 
    ((sb, sb' p), (sb' p, sb)); ((sm, sb' p), (sm' p, sb)); ((sl, sb' p), (sl' p, sb));
    ((sb, sm' p), (sb' p, sm)); ((sl, sm' p), (sl' p, sm))]) (seq 0 state_bound) ++
  (* finalization *)
  map (fun p => ((sz, sl' p), (so, so))) (seq (S (length mm)) (state_bound - S (length mm))) ++
  [((sz, sl' 0), (so, so));
   ((sz, so), (so, so)); ((so, sb), (so, so)); ((so, sm), (so, so));
   ((so, sr), (so, so)); ((so, sz), (so, so))].

(* initialization, simulation, finalization *)
Inductive srs_spec (a b c d: Symbol) : Prop :=
  | srs_i0 : ((sz, sz), (st, sr)) = ((a, b), (c, d)) -> srs_spec a b c d
  | srs_i1 : ((sz, st), (sl' 1, sm)) = ((a, b), (c, d)) -> srs_spec a b c d
  | srs_sim0 {p} : ((sr' p, sz), (sb, sr' (S p))) = ((a, b), (c, d)) -> mm2_instr_at (mm2_inc_b) p mm -> srs_spec a b c d
  | srs_sim1 {p} : ((sz, sl' p), (sl' (S p), sb)) = ((a, b), (c, d)) -> mm2_instr_at (mm2_inc_a) p mm -> srs_spec a b c d
  | srs_sim2 {p q} : ((sm, sr' p), (sm, sr' (S p))) = ((a, b), (c, d)) -> mm2_instr_at (mm2_dec_b q) p mm -> srs_spec a b c d
  | srs_sim3 {p q} : ((sb, sr' p), (sr' q, sz))= ((a, b), (c, d)) -> mm2_instr_at (mm2_dec_b q) p mm -> srs_spec a b c d
  | srs_sim4 {p q} : ((sl' p, sm), (sl' (S p), sm)) = ((a, b), (c, d)) -> mm2_instr_at (mm2_dec_a q) p mm -> srs_spec a b c d
  | srs_sim5 {p q} : ((sl' p, sb), (sz, sl' q)) = ((a, b), (c, d)) -> mm2_instr_at (mm2_dec_a q) p mm -> srs_spec a b c d
  | srs_fin0 {p} : ((sz, sl' p), (so, so)) = ((a, b), (c, d)) -> S (length mm) <= p < state_bound -> srs_spec a b c d
  | srs_fin'0 {p} : ((sz, sl' p), (so, so)) = ((a, b), (c, d)) -> p = 0 -> srs_spec a b c d
  | srs_fin1 : ((sz, so), (so, so)) = ((a, b), (c, d)) -> srs_spec a b c d
  | srs_fin2 : ((so, sb), (so, so)) = ((a, b), (c, d)) -> srs_spec a b c d
  | srs_fin3 : ((so, sm), (so, so)) = ((a, b), (c, d)) -> srs_spec a b c d
  | srs_fin4 : ((so, sr), (so, so)) = ((a, b), (c, d)) -> srs_spec a b c d
  | srs_fin5 : ((so, sz), (so, so)) = ((a, b), (c, d)) -> srs_spec a b c d.

(* opaque state movement *)
Inductive srs_mlr_spec (a b c d: Symbol) : Prop :=
  | srs_mr0 {p} : ((sl' p, sb), (sl, sb' p)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d
  | srs_mr1 {p} : ((sl' p, sm), (sl, sm' p)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d
  | srs_mr2 {p} : ((sb' p, sb), (sb, sb' p)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d
  | srs_mr3 {p} : ((sb' p, sm), (sb, sm' p)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d
  | srs_mr4 {p} : ((sb' p, sr), (sb, sr' p)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d
  | srs_mr5 {p} : ((sm' p, sb), (sm, sb' p)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d
  | srs_mr6 {p} : ((sm' p, sr), (sm, sr' p)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d
  | srs_ml0 {p} : ((sb, sr' p), (sb' p, sr)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d
  | srs_ml1 {p} : ((sm, sr' p), (sm' p, sr)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d
  | srs_ml2 {p} : ((sb, sb' p), (sb' p, sb)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d
  | srs_ml3 {p} : ((sm, sb' p), (sm' p, sb)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d
  | srs_ml4 {p} : ((sl, sb' p), (sl' p, sb)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d
  | srs_ml5 {p} : ((sb, sm' p), (sb' p, sm)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d
  | srs_ml6 {p} : ((sl, sm' p), (sl' p, sm)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d.

Lemma srs_specI a b c d : In ((a, b), (c, d)) srs -> srs_spec a b c d \/ srs_mlr_spec a b c d.
Proof.
  rewrite /srs. case /in_app_iff.
  { firstorder (by eauto using srs_spec with nocore). }
  case /in_app_iff.
  { move=> /in_flat_map [[? i]] [/inv_instr_at_in_combine].
    move: i => []> /=; intuition (by eauto using srs_spec, or with nocore). }
  case /in_app_iff.
  { move=> /in_flat_map [?] [/in_seq] [_ ?].
    firstorder (by eauto using srs_mlr_spec with nocore). }
  case /in_app_iff.
  { move=> /in_flat_map [?] [/in_seq] [_ ?].
    firstorder (by eauto using srs_mlr_spec with nocore). }
  case /in_app_iff.
  { move=> /in_map_iff [?] [?] /in_seq H. left.
    apply: srs_fin0; first by eassumption.
    move: H. rewrite /state_bound. by lia. }
  case.
  { move=> [] *. subst. left. by eauto using srs_spec, erefl with nocore. }
  by firstorder (by eauto using srs_spec with nocore).
Qed.

Lemma In_srsI {a b c d} : srs_spec a b c d \/ srs_mlr_spec a b c d -> In ((a, b), (c, d)) srs.
Proof.
  case.
  - move=> [] > <- *.
    1-2: apply /In_appl; rewrite /=; by tauto.
    1-6: apply /In_appr /In_appl /in_flat_map; eexists;
      (constructor; [apply: instr_at_in_combine; by eassumption | by move=> /=; tauto ]).
    1: apply /In_appr /In_appr /In_appr /In_appr /In_appl /in_map_iff; eexists;
      (constructor; [by reflexivity | apply /in_seq; by lia ]).
    1-6: do 5 (apply /In_appr); move=> /=; subst; by tauto.
  - move=> [] p <- *.
    1-7: apply /In_appr /In_appr /In_appl /in_flat_map; exists p;
      (constructor; [apply /in_seq; by lia | by move=> /=; tauto ]).
    1-7: apply /In_appr /In_appr /In_appr /In_appl /in_flat_map; exists p;
      (constructor; [apply /in_seq; by lia | by move=> /=; tauto ]).
Qed.

Lemma srs_mlr_specE {a b c d} : srs_mlr_spec a b c d -> 
  exists x y p,
  ((a, b), (c, d)) = (((x, Some p), (y, None)), ((x, None), (y, Some p))) \/
  ((a, b), (c, d)) = (((x, None), (y, Some p)), ((x, Some p), (y, None))).
Proof. move=> [] > [] ? ? ? ? _; subst; do 3 eexists; by tauto. Qed.

(* resolve In _ srs goals : by eauto with in_srs_db nocore. *)
Local Create HintDb in_srs_db.

Local Hint Resolve or_introl or_intror conj In_srsI : in_srs_db.
Local Hint Immediate erefl : in_srs_db.
Local Hint Constructors srs_spec srs_mlr_spec : in_srs_db.

Definition stepI_nil := (@step_intro srs []).

Lemma move_sb_right {p n} : p < state_bound -> 
  multi_step srs ((sb' p) :: repeat sb n) ((repeat sb n) ++ [sb' p]).
Proof.
  move=> Hp. elim: n; first by apply: rt_refl.
  move=> n IH /=. apply: rt_trans; 
    [apply: rt_step | apply: (multi_step_applI (u := [sb])); exact: IH].
  apply: stepI_nil. by eauto with in_srs_db nocore.
Qed.

Lemma move_sb_left {p n} : p < state_bound -> multi_step srs ((repeat sb n) ++ [sb' p]) ((sb' p) :: repeat sb n).
Proof.
  move=> Hp. elim: n; first by apply: rt_refl.
  move=> n IH /=. apply: rt_trans; 
    [apply: (multi_step_applI (u := [sb])); exact: IH | apply: rt_step].
  apply: stepI_nil. by eauto with in_srs_db nocore.
Qed.

Local Notation mm2_reaches x y := (clos_refl_trans _ (mm2_step mm) x y).

Section Transport.

Definition c0 := (1, (0, 0)).

Context (c'0 : mm2_state) (Hc0c'0 : mm2_reaches c0 c'0) (Hc'0 : mm2_stop mm c'0).

Lemma Hbound : { bound : nat | forall y, mm2_reaches c0 y -> (fst (snd y) + snd (snd y)) < bound }.
Proof using Hc0c'0 Hc'0.
  move: (c'0) (Hc0c'0) (Hc'0) => z.
  move=> /mm2_terminates_Acc /[apply]. elim.
  move=> x _ IH.
  have [[y]|Hx] := mm2_sig_step_dec mm x.
  - move=> /[dup] /IH [bound Hbound] Hxy.
    exists (1 + bound + (fst (snd x)) + (snd (snd x))).
    move=> y' /clos_rt_rt1n_iff Hxy'.
    case: Hxy' Hxy; [lia|].
    move=> > /mm2_step_det H + /H ?. subst y.
    move=> /clos_rt_rt1n_iff /Hbound. lia.
  - exists (1 + (fst (snd x)) + (snd (snd x))).
    move=> y /clos_rt_rt1n_iff Hxy.
    case: Hxy Hx; [lia|].
    by move=> > + + H => /H.
Qed.

Lemma mm2_instr_at_state_bound {mm2i p} :
  mm2_instr_at mm2i p mm -> S p < state_bound /\ instr_state mm2i < state_bound.
Proof.
  rewrite /state_bound.
  move=> [?] [?] [-> <-]. rewrite !length_app !map_app !list_sum_app /=.
  split; lia.
Qed.

Lemma mm_state_ub y : mm2_reaches c0 y -> fst y < state_bound.
Proof.
  move=> /(@clos_rt_rtn1 mm2_state). elim.
  - rewrite /state_bound /=. lia.
  - move=> > [?] [/mm2_instr_at_state_bound + H] _.
    case: H => > /=; lia.
Qed.

Definition ab_ub := sval Hbound.

Lemma Hab_ub y : mm2_reaches c0 y -> (fst (snd y) + snd (snd y)) < ab_ub.
Proof. by apply: (svalP Hbound). Qed.

Definition d := 5 + ab_ub + ab_ub. (* maximal space requirement *)

(* s is (0^(n-a) l_p _^a m _^b r 0^(n-b)) with a unique state annotation *)
Definition enc_Config : mm2_state -> list Symbol :=
  fun '(p, (a, b)) => 
    (repeat sz (1 + ab_ub-a)) ++ [sl' p] ++ (repeat sb a) ++ [sm] ++ 
    (repeat sb b) ++ [sr] ++ (repeat sz (1 + ab_ub-b)).

(* s is (0^(n-a) l _^a m _^b r_p 0^(n-b)) with a unique state annotation *)
Definition enc_Config' : mm2_state -> list Symbol :=
  fun '(p, (a, b)) => 
    (repeat sz (1 + ab_ub-a)) ++ [sl] ++ (repeat sb a) ++ [sm] ++ 
    (repeat sb b) ++ [sr' p] ++ (repeat sz (1 + ab_ub-b)).

Lemma multi_step_enc_c0 : multi_step srs (repeat sz d) (enc_Config c0).
Proof using.
  apply: (rt_trans (y := (repeat sz (1 + ab_ub)) ++ [sz] ++ [st] ++ [sr] ++ (repeat sz (1 + ab_ub)))).
  - have ->: d = 1 + ab_ub + 1 + 1 + 1 + 1 + ab_ub by (rewrite /d; lia).
    rewrite ?repeat_app -?app_assoc. do ? apply: multi_step_applI.
    apply /rt_step /stepI_nil. by eauto with in_srs_db nocore.
  - apply /multi_step_applI /rt_step /stepI_nil. by eauto with in_srs_db nocore.
Qed.

Lemma move_sb_right' {p n x y} : p < state_bound -> ((x, y) = (1, 3) \/ (x, y) = (3, 2)) ->
  multi_step srs ([(x, Some p)] ++ repeat sb n ++ [(y, None)]) ([(x, None)] ++ repeat sb n ++ [(y, Some p)]).
Proof.
  move=> ? /= Hxy. case: n.
  - apply /rt_step /stepI_nil.
    move: Hxy => [] [-> ->]; by eauto with in_srs_db nocore.
  - move=> n. apply: (rt_trans (y := [(x, None)] ++ [sb' p] ++ (repeat sb n) ++ [(y, None)])).
    + have ->: repeat sb (S n) = [sb] ++ repeat sb n by done.
      rewrite /= -?app_assoc. apply /rt_step /stepI_nil.
      move: Hxy => [] [-> _]; by eauto with in_srs_db nocore.
    + rewrite -?app_assoc. apply: multi_step_applI. 
      apply: (rt_trans (y := (repeat sb n) ++ [sb' p] ++ [(y, None)])).
      * rewrite ?app_assoc. apply: multi_step_apprI. by apply: move_sb_right.
      * have ->: S n = n + 1 by lia. rewrite repeat_app -?app_assoc.
        apply /multi_step_applI /rt_step /stepI_nil.
        move: Hxy => [] [_ ->]; by eauto with in_srs_db nocore.
Qed.

Lemma move_sb_left' {p n x y} : p < state_bound -> ((x, y) = (1, 3) \/ (x, y) = (3, 2)) ->
  multi_step srs ([(x, None)] ++ repeat sb n ++ [(y, Some p)]) ([(x, Some p)] ++ repeat sb n ++ [(y, None)]).
Proof.
  move=> ? /= Hxy. case: n.
  - apply /rt_step /stepI_nil.
    move: Hxy => [] [-> ->]; by eauto with in_srs_db nocore.
  - move=> n. apply: (rt_trans (y := [(x, None)] ++ (repeat sb n) ++ [sb' p] ++ [(y, None)])).
    + rewrite (ltac:(lia) : S n = n + 1) repeat_app -?app_assoc. do ? apply: multi_step_applI. 
      apply /rt_step /stepI_nil.
      move: Hxy => [] [_ ->]; by eauto with in_srs_db nocore.
    + rewrite ?app_assoc. apply: multi_step_apprI.
      apply: (rt_trans (y := [(x, None)] ++ [sb' p] ++ (repeat sb n))).
      * rewrite -?app_assoc. apply: multi_step_applI. by apply: move_sb_left.
      * apply /rt_step /stepI_nil.
        move: Hxy => [] [-> _]; by eauto with in_srs_db nocore.
Qed.

Lemma move_right {c} : mm2_reaches c0 c -> 
  multi_step srs (enc_Config c) (enc_Config' c). 
Proof.
  move: c => [p [a b]] /[dup] /mm_state_ub ?.
  move=> /(svalP Hbound (p, (a, b))) ?.
  apply: multi_step_applI. rewrite ?app_assoc. apply: multi_step_apprI.
  apply: (rt_trans (y := [sl] ++ (repeat sb a) ++ [sm' p] ++ (repeat sb b) ++ [sr])).
  - rewrite ?app_assoc. do 2 apply: multi_step_apprI.
    apply: move_sb_right'; by tauto.
  - rewrite -?app_assoc. do 2 apply: multi_step_applI.
    apply: move_sb_right'; by tauto.
Qed.

Lemma move_left {c} : mm2_reaches c0 c ->
  multi_step srs (enc_Config' c) (enc_Config c). 
Proof.
  move: c => [p [a b]] /[dup] /mm_state_ub ?.
  move=> /(svalP Hbound (p, (a, b))) ?.
  apply: multi_step_applI. rewrite ?app_assoc. apply: multi_step_apprI.
  apply: (rt_trans (y := [sl] ++ (repeat sb a) ++ [sm' p] ++ (repeat sb b) ++ [sr])).
  - rewrite -?app_assoc. do 2 apply: multi_step_applI.
    apply: move_sb_left'; by tauto.
  - rewrite ?app_assoc. do 2 apply: multi_step_apprI.
    apply: move_sb_left'; by tauto.
Qed.

Lemma simulate_mm_step {x y} : mm2_reaches c0 x -> mm2_step mm x y ->
  multi_step srs (enc_Config x) (enc_Config y).
Proof.
  move=> /[dup] /(Hab_ub x) H'x Hx Hxy.
  have Hy : mm2_reaches c0 y. { by apply: rt_trans; [apply Hx|apply rt_step]. }
  move: Hxy => [instr] [Hinstr H].
  have := move_right Hx. have := move_left Hy. (* movements  *)
  case: H H'x Hinstr.
  - (* inc a *)
    move=> p a b /= ?? H'x H'y.
    have [-> ->]: S ab_ub - a = (ab_ub - a) + 1 /\ S a = 1 + a by lia.
    rewrite ?repeat_app -?app_assoc. apply: multi_step_applI.
    apply /rt_step /stepI_nil. by eauto with in_srs_db nocore.
  - (* inc b *)
    move=> p a b /= ?? H'x H'y.
    apply: rt_trans; first by eassumption.
    apply: rt_trans; last by eassumption.
    have [-> ->]: S b = b + 1 /\ S ab_ub - b = 1 + (S ab_ub - (b + 1)) by lia.
    rewrite ?repeat_app -?app_assoc. do 5 apply: multi_step_applI.
    apply /rt_step /stepI_nil. by eauto with in_srs_db nocore.
  - (* dec_a > 0 *)
    move=> p q a b /= ?? H'x H'y.
    have ->: S ab_ub - a = (ab_ub - a) + 1 by lia.
    rewrite repeat_app -?app_assoc.
    apply /multi_step_applI /rt_step /stepI_nil. by eauto with in_srs_db nocore.
  - (* dec_b > 0 *)
    move=> p q a b /= ?? H'x H'y.
    apply: rt_trans; first by eassumption.
    apply: rt_trans; last by eassumption.
    have [-> ->] : S b = b + 1 /\ S ab_ub - b = 1 + (S ab_ub - (b + 1)) by lia.
    rewrite ?repeat_app -?app_assoc. do 5 apply: multi_step_applI. 
    apply /rt_step /stepI_nil. by eauto with in_srs_db nocore.
  - (* dec_a = 0 *)
    move=> p a b /= ?? H'x H'y.
    apply /multi_step_applI /rt_step /stepI_nil. by eauto with in_srs_db nocore.
  - (* dec_b = 0 *)
    move=> p a b /= ?? H'x H'y.
    apply: rt_trans; first by eassumption.
    apply: rt_trans; last by eassumption.
    do 3 apply: multi_step_applI.
    apply /rt_step /stepI_nil. by eauto with in_srs_db nocore.
Qed.

Lemma multi_step_repeat_solI n : multi_step srs (repeat sz n ++ [so]) (repeat so (n+1)).
Proof.
  elim: n; first by apply: rt_refl.
  move=> n IH. rewrite repeat_app. 
  have ->: S n = n + 1 by lia.
  apply: (rt_trans (y := repeat sz n ++ [so] ++ [so]));
    last by (rewrite ?app_assoc; apply: multi_step_apprI).
  rewrite repeat_app -?app_assoc.
  apply /multi_step_applI /rt_step /stepI_nil.
  by eauto with in_srs_db nocore.
Qed.

Lemma multi_step_repeat_sorI {n x} : x = sb \/ x = sz -> 
  multi_step srs ([so] ++ repeat x n) ([so] ++ repeat so n).
Proof.
  move=> Hx. elim: n; first by apply: rt_refl.
  move=> n IH. 
  apply: (rt_trans (y := ([so] ++ [so] ++ repeat x n))); last by apply: multi_step_applI.
  apply /rt_step /stepI_nil.
  move: Hx => [] ->; by eauto with in_srs_db nocore.
Qed.

Lemma multi_step_repeat_sorI' {s t n x} : x = sb \/ x = sz -> 
  multi_step srs ([so] ++ s) ([so] ++ t) ->
  multi_step srs ([so] ++ repeat x n ++ s) ([so] ++ repeat so n ++ t).
Proof.
  move=> /multi_step_repeat_sorI H1 H2.
  apply: (rt_trans (y := ([so] ++ repeat so n ++ s))).
  - rewrite ?app_assoc. by apply: multi_step_apprI.
  - have ->: [so] = repeat so 1 by done. rewrite ?app_assoc -repeat_app.
    have ->: 1 + n = n + 1 by lia. rewrite repeat_app -?app_assoc.
    by apply: multi_step_applI.
Qed.

Lemma simulate_mm_halting {x} : mm2_reaches c0 x ->
  (forall y, not (mm2_step mm x y)) -> multi_step srs (enc_Config x) (repeat so d).
Proof.
  move: x => [p [a b]].
  move=> /[dup] /Hab_ub /= ?.
  move=> Hx H'x.
  apply: (rt_trans (y := (repeat sz (ab_ub - a)) ++ [so] ++ [so] ++ _)).
  - rewrite (ltac:(lia) : S ab_ub - a = (ab_ub - a) + 1) repeat_app -?app_assoc.
    apply /multi_step_applI /rt_step /stepI_nil.
    move: p Hx H'x => [|p].
    + move=> *. by eauto with in_srs_db nocore.
    + move=> /mm_state_ub Hx H'x.
      have ? : S (length mm) <= (S p) < state_bound.
      { split; [|done]. suff: not (p < length mm) by lia.
        move=> /nth_error_Some.
        case Hinstr: (nth_error mm p) => [instr|]; [|done].
        have [y Hxy] := mm2_progress instr (S p, (a, b)).
        move=> _. apply: (H'x y). exists instr.
        split; [|done].
        move: Hinstr => /(@nth_error_split mm2_instr) [?] [?] [-> <-].
        by do 2 eexists. }
      by eauto with in_srs_db nocore.
  - apply: (rt_trans (y := (repeat so (ab_ub - a + 1) ++ [so] ++
      repeat sb a ++ [sm] ++ repeat sb b ++ [sr] ++ repeat sz (S ab_ub - b)))).
    + rewrite ?app_assoc. do 6 apply: multi_step_apprI. by apply: multi_step_repeat_solI.
    + have ->: d = (ab_ub - a + 1) + 1 + a + 1 + b + 1 + (S ab_ub - b) by (rewrite /d; lia).
      rewrite ?repeat_app -?app_assoc. do 2 apply: multi_step_applI.
      apply: multi_step_repeat_sorI'; first by left.
      apply: (rt_trans (y := ([so] ++ [so] ++ repeat sb b ++ [sr] ++ repeat sz (S ab_ub - b)))).
      * apply /rt_step /stepI_nil. by eauto with in_srs_db nocore.
      * apply: multi_step_applI. apply: multi_step_repeat_sorI'; first by left.
        apply: (rt_trans (y := ([so] ++ [so] ++ repeat sz (S ab_ub - b)))).
        ** apply /rt_step /stepI_nil. by eauto with in_srs_db nocore.
        ** apply: multi_step_applI. apply: multi_step_repeat_sorI. by right.
Qed.

Lemma to_SR2ab : multi_step srs (repeat sz (1+(d - 1))) (repeat so (1+(d - 1))).
Proof using Hc0c'0 Hc'0.
  have H'y := simulate_mm_halting Hc0c'0 Hc'0.
  apply: rt_trans; last by eassumption.
  apply: rt_trans; first by apply: (multi_step_enc_c0).
  move: (Hc0c'0) => /(@clos_rt_rtn1 mm2_state).
  elim. { by apply: rt_refl. }
  move=> > /simulate_mm_step IH /(@clos_rtn1_rt mm2_state) /IH.
  move=> *. by apply: rt_trans; eassumption.
Qed.

End Transport.

Section InverseTransport.
Context (N: nat). (* number of 0s / 1s *)
Context (HN: multi_step srs (repeat sz (1+N)) (repeat so (1+N))). (* 0^N ->> 1^N *)

Local Definition rt_rt1n {A R x y} := @clos_rt_rt1n_iff A R x y.

(* s is (0^n1 l _^a m _^b r 0^n2) with a unique state annotation *)
Definition encodes : mm2_state -> list Symbol -> Prop :=
  fun c s => 
  exists u v t, let '(p, (a, b)) := c in
    s = u ++ t ++ v /\
    map fst t = map fst ([sl] ++ repeat sb a ++ [sm] ++ repeat sb b ++ [sr]) /\
    filter (fun x => if x is None then false else true) (map snd t) = [Some p].

Lemma In_srs_stE {a b c d} : In ((a, b), (c, d)) srs ->
  ((sz, sz), (st, sr)) = ((a, b), (c, d)) \/
  ((sz, st), (sl' 1, sm)) = ((a, b), (c, d)) \/
  if a is (_, None) then (if b is (_, None) then False else True) else True.
Proof. move=> /srs_specI [] [] > [] ? ? ? ? *; subst; by tauto. Qed.

Lemma init_encodes : exists s, encodes c0 s /\ multi_step srs s (repeat so (1+N)).
Proof using HN.
  have [s] : exists s, 
    multi_step srs s (repeat so (1+N)) /\ 
    Forall (fun x => snd x = None) s /\
    forall n, nth n s sz = st -> nth (1+n) s sz = sr.
  { eexists. constructor; [|constructor]; [by eassumption | apply /Forall_repeatI; by tauto |].
    move: (1+N) => m n H. exfalso. elim: n m H; first by case.
    move=> n IH [|m]; [done | by apply: IH]. }
  move Ht: (repeat so (1+N)) => t [/rt_rt1n Hst] [].
  elim: Hst Ht; first by move=> ? <- /Forall_cons_iff [].
  move=> {}s {}t > Hst Ht IH /IH {IH}.
  case: Hst Ht => u v a b c d /In_srs_stE [|[]].
  - move=> [] <- <- <- <- _ IH.
    move=> /Forall_app [Hu] /Forall_cons_iff [_] /Forall_cons_iff [_ Ht] Huv.
    apply: IH.
    + apply /Forall_app. by do ? constructor.
    + move=> n. have := Huv n. elim: (u) n; first by move=> [|[|n]].
      clear. move=> x {}u IH [|n]; last by move/IH.
      move: (u) => [|? ?]; [by move=> H /H | done].
  - move=> [] <- <- <- <- /rt_rt1n Ht _ _ /(_ (1 + length u)).
    do 2 (rewrite app_nth2; first by lia).
    rewrite (ltac:(lia) : 1 + length u - length u = 1).
    rewrite (ltac:(lia) : 1 + (1 + length u) - length u = 2).
    move=> /(_ ltac:(done)) Hv. eexists. constructor; last by eassumption.
    move: (v) Hv => [|? v']; first done.
    move=> /= ->. exists u, v', [sl' 1; sm; sr].
    constructor; [done | by constructor].
  - move=> H _ _ /Forall_app [_] /Forall_cons_iff [+] /Forall_cons_iff [+] _.
    by move: a b H => [? [?|]] [? [?|]].
Qed.

(* possibilities to split two symbols among one app *)
Lemma eq2_app {u v a b} {s t: list Symbol} : u ++ a :: b :: v = s ++ t ->
  (exists v1, v = v1 ++ t /\ s = u ++ a :: b :: v1) \/
  (s = u ++ [a] /\ t = b :: v) \/
  (exists u2, u = s ++ u2 /\ t = u2 ++ a :: b :: v).
Proof.
  elim: u s.
  - move=> [|y1 [|y2 s]].
    + rewrite ?app_nil_l. move=> <-. right. right. by exists [].
    + move=> []. rewrite [in [] ++ _]/List.app => <- <- /=. right. by left.
    + move=> [] <- <- ->. left. by exists s.
  - move=> x1 u IH [|y1 s].
    + rewrite ?app_nil_l. move=> <-. right. right. by exists (x1 :: u).
    + move=> [] <- /IH [|[|]].
      * move=> [?] [-> ->]. left. by eexists.
      * move=> [-> ->]. right. by left.
      * move=> [?] [-> ->]. right. right. by eexists.
Qed.

(* possibilities to split two symbols among one twp apps *)
Lemma eq2_app_app {u a b v u' v'} {s: list Symbol} : length s > 1 ->
  u ++ a :: b :: v = u' ++ s ++ v' ->
  (exists u'2, v = u'2 ++ s ++ v') \/ 
  (exists s2, u' = u ++ [a] /\ s = b :: s2 /\ v = s2 ++ v') \/
  (exists s1 s2, s = s1 ++ [a] ++ [b] ++ s2 /\ u = u' ++ s1 /\ v = s2 ++ v') \/
  (exists s1, u = u' ++ s1 /\ s = s1 ++ [a] /\ v' = b ::  v) \/
  (exists v'1, u = u' ++ s ++ v'1).
Proof.
  move=> Hs /eq2_app [|[|]].
  - move=> [?] [-> ->]. left. by eexists.
  - move=> [->]. move: s Hs => [|? s] /=; first by lia.
    move=> _ [] <- <-. right. left. by eexists.
  - move=> [?] [->] /esym /eq2_app [|[|]].
    + move=> [?] [-> ->]. right. right. left. by do 2 eexists.
    + move=> [-> ->]. do 3 right. left. by eexists.
    + move=> [?] [-> ->]. do 4 right. by eexists.
Qed.

(* specification of inner mm2 step *)
Inductive srs_step_spec (u v: list Symbol) (a b: Symbol) (n m: nat) : Prop :=
  | srs_step0 : a.1 = sl.1 -> b.1 = sm.1 -> u = [] -> n = 0 -> srs_step_spec u v a b n m
  | srs_step1 : a.1 = sl.1 -> b.1 = sb.1 -> u = [] -> n = 1 + (n - 1) -> srs_step_spec u v a b n m
  | srs_step2 : a.1 = sm.1 -> b.1 = sr.1 -> v = [] -> m = 0 -> srs_step_spec u v a b n m
  | srs_step3 : a.1 = sb.1 -> b.1 = sr.1 -> v = [] -> m = 1 + (m - 1) -> srs_step_spec u v a b n m.

Lemma srs_step_specI {u v a b n m} : 
  map fst (u ++ [a] ++ [b] ++ v) = map fst ([sl] ++ repeat sb n ++ [sm] ++ repeat sb m ++ [sr]) ->
  srs_step_spec u v a b n m \/ 
  (a.1 = sb.1 /\ b.1 = sb.1) \/ (a.1 = sb.1 /\ b.1 = sm.1) \/ (a.1 = sm.1 /\ b.1 = sb.1).
Proof.
  move: u => [|? u].
  { move: n => [|n].
    - move=> [] *. left. by apply: srs_step0.
    - move=> [] *. left. apply: srs_step1; by [|lia]. }
  move=> [] _. rewrite -/(_ ++ _).
  elim /rev_ind: v.
  { rewrite app_nil_r ?map_app /=.
    rewrite ?app_assoc. move=> /app_inj_tail [].
    have [->|->] : m = 0 \/ m = (m - 1) + 1 by lia.
    - rewrite app_nil_r. move=> /app_inj_tail [] *. left. by apply: srs_step2.
    - rewrite repeat_app map_app ?app_assoc.
      move=> /app_inj_tail [] *. left. apply: srs_step3; by [|lia]. }
  move=> ? v _. rewrite ?map_app ?app_assoc. 
  move=> /app_inj_tail [+] _. move=> + /ltac:(right).
  elim: u n.
  { move=> [|[|n]].
    - move: m => [|m [] *]; [done | by tauto ].
    - move=> [] *. by tauto.
    - move=> [] *. by tauto. }
  move=> ? u IH [|n]; last by move=> [_] /IH.
  move=> [_] {IH}. rewrite -?/(_ ++ _). elim: m u; first by case.
  move=> m IH [|? u]; last by move=> [_] /IH.
  move: m {IH} => [|m] []; [done | by tauto].
Qed.

(* each srs step is sound *)
Lemma simulate_srs_step {x s t} : step srs s t -> encodes x s ->
  encodes x t \/ (forall y, mm2_step mm x y -> encodes y t).
Proof.
  move: x => [p [a b]] [] u v a' b' c' d' H [u'] [v'] [{}t].
  rewrite -?/([_] ++ [_] ++ v). move=> [+] [H1t H2t] => /eq2_app_app.
  have : length t > 1.
  { move: H1t => /(congr1 (@length _)).
    rewrite ?map_app ?length_app ?length_map /=. move=> ->. by lia. }
  move=> Ht /(_ Ht) {Ht}.
  case; [|case; [|case; [|case]]].
  - move=> [u'2 ->]. left.
    exists (u ++ c' :: d' :: u'2), v', t.
    constructor; [by rewrite -?app_assoc | done].
  - move=> [s2] [?] [? ?]. subst. move: H1t H2t => [].
    move: H => /srs_specI [|] [] > [] ????; subst; try done; [| |].
    + move=> Hi _ H1s2 [<- H2s2]. right.
      move=> y [?] [/(mm2_instr_at_unique Hi) <-] Hxy.
      inversion Hxy. subst.
      eexists u, v', (_ :: _ :: s2).
      constructor; [done | constructor; by rewrite /= ?H1s2  ?H2s2].
    + move=> ? _ _ [<-] _ *. right.
      move=> y Hxy. exfalso. move: y Hxy.
      apply /mm2_stop_index_iff => /=. lia.
    + move=> -> _ _ /= [<-] _. right.
      move=> y Hxy. exfalso. move: y Hxy.
      apply /mm2_stop_index_iff => /=. by left.
  - move=> [s1] [s2] [?] [? ?]. subst.
    move: H H1t H2t => /srs_specI [].
    + move=> H + + /ltac:(right). move=> /[dup] [/srs_step_specI] [].
      * move=> H'. move: H' H => [] ? ? ? ? [] > [] ? ? ? ?; subst; try done; [ | | | ].
        ** rewrite app_nil_r /=. move=> Hi [H1] [<-] H2.
           move=> y [?] [/(mm2_instr_at_unique Hi) <-] Hxy.
           inversion Hxy. subst.
           eexists u', v', (_ :: _ :: _). constructor; [done | by rewrite /= H1 H2].
        ** rewrite app_nil_r /= ?map_app. move: (a) => [|?]; first done.
           move=> Hi [] H1 [<-] H2.
           move=> y [?] [/(mm2_instr_at_unique Hi) <-] Hxy.
           inversion Hxy. subst. try rewrite [in LHS]/List.app in H1.
           eexists (u' ++ [sz]), v', (_ :: _).
           rewrite -?app_assoc. constructor; [done | by rewrite /= ?map_app H1 H2].
        ** rewrite ?map_app filter_app /= app_nil_r /step.
           move=> Hi + /(app_inj_tail (y := [])) [H2] [<-].
           rewrite ?app_assoc app_nil_r.
           move=> /app_inj_tail [/app_inj_tail] [H1] _ _.
           move=> y [?] [/(mm2_instr_at_unique Hi) <-] Hxy.
           inversion Hxy. subst.
           eexists u', v', (_ ++ [_; _]).
           rewrite -?app_assoc. constructor; first done.
           by rewrite ?map_app filter_app /= H1 H2.
        ** rewrite [in repeat sb b](ltac:(lia) : b = (b - 1) + 1) repeat_app.
           rewrite ?map_app ?filter_app ?app_assoc ?app_nil_r /= /step.
           move=> Hi + /(app_inj_tail (y := [])) [H2] [<-].
           move=> /app_inj_tail [/app_inj_tail] [H1] _ _.
           have -> : b = S (Nat.pred b) by lia.
           move=> y [?] [/(mm2_instr_at_unique Hi) <-] Hxy.
           inversion Hxy. subst.
           eexists u', ([sz] ++ v'), (_ ++ [_]).
           rewrite (ltac:(lia) : b = 1 + (b - 1)) -?app_assoc /=. 
           constructor; first done.
           by rewrite ?map_app filter_app /= H1 H2 -?app_assoc.
      * move: H => + + _ /ltac:(exfalso).
        move=> [] > [] *; subst; by firstorder done.
    + move=> + + + /ltac:(left; exists u', v', (s1 ++ c' :: d' :: s2)).
      move=> /srs_mlr_specE [x] [y] [q] [] [] ? ? ? ? H1t H2t; 
        subst; rewrite -?app_assoc.
      * constructor; first done.
        constructor; first by rewrite -H1t ?map_app.
        move: H2t. by rewrite ?map_app ?filter_app /=.
      * constructor; first done.
        constructor; first by rewrite -H1t ?map_app.
        move: H2t. by rewrite ?map_app ?filter_app /=.
  - move=> [s1] [?] [? ?]. subst.
    move: (H1t). rewrite ?map_app ?app_assoc. move=> /app_inj_tail [_].
    move: H H1t H2t => /srs_specI [|] [] > [] ? ? ? ?; subst; try done; [].
    move=> Hi H1s1. rewrite map_app filter_app. 
    move=> /(app_inj_tail (y := [])) [H2s2] [<-] _.
    right.
    move=> y [?] [/(mm2_instr_at_unique Hi) <-] Hxy.
    inversion Hxy. subst.
    eexists u', v, (s1 ++ [_; _]).
    rewrite -?app_assoc. constructor; [done | constructor].
    * move: H1s1. rewrite ?map_app ?app_assoc. move=> /app_inj_tail [-> _].
      by rewrite (ltac:(lia) : S b = b + 1) [repeat _ (b + 1)]repeat_app map_app -?app_assoc.
    * by rewrite map_app filter_app /= H2s2.
  - move=> [v'1 ->]. left.
    exists u', (v'1 ++ c' :: d' :: v), t.
    constructor; [by rewrite -?app_assoc | done].
Qed.

Lemma to_MM2_ZERO_HALTING : MM2_ZERO_HALTING mm.
Proof using HN.
  rewrite /MM2_ZERO_HALTING -/c0.
  have [s [H1s H2s]] := init_encodes.
  move Ht: (repeat so (1+N)) (c0) H2s H1s => t c Hst.
  have {}Ht : Forall (fun x => fst so = x) (map fst t).
  { subst t. elim: (N); by constructor. }
  move: Hst Ht c. move=> /rt_rt1n. elim.
  - move=> {}s Hs [? [? ?]] /= [?] [?] [{}t] [?] [H]. subst s.
    move: Hs. rewrite ?map_app ?Forall_app H.
    by move=> [_] [/Forall_cons_iff] [].
  - move=> > /simulate_srs_step H _ IH /IH {}IH c /H [].
    + by move=> /IH.
    + have [[y Hcy]|?] := mm2_exists_step_dec mm c.
      * move=> /(_ y Hcy) /IH [c'0 [? ?]].
        exists c'0. split; [|done].
        by apply: rt_trans; [apply: rt_step|]; eassumption.
      * move=> _. exists c. by split; [apply: rt_refl|].
Qed.

End InverseTransport.

End Reduction.

End SR2ab.

Module Argument.

Import SSTS.
Import SR2ab (Srs, Symbol, sym_eq_dec).

Local Arguments rt_trans {A R x y z}.

(* injective pairing *)
Definition enc_pair '(x, y) : nat := (x + y) * (x + y) + y.

Lemma enc_pair_inj {xy x'y'} : enc_pair xy = enc_pair x'y' -> xy = x'y'.
Proof.
  move: xy x'y' => [x y] [x' y'] /=. rewrite pair_equal_spec.
  have : x + y <> x' + y' \/ x + y = x' + y' by lia.
  case; by nia.
Qed.

Opaque enc_pair.

Section SR2ab_SSTS01.

(* given simple rewriting system *)
Context (srs : Srs) (a0: Symbol) (b0: Symbol) (Ha0b0: b0 <> a0).

Definition enc (x: Symbol) : nat :=
  if sym_eq_dec x a0 then 0
  else if sym_eq_dec x b0 then 1
  else 2 + (
    match x with
    | (n, None) => enc_pair (n, 0)
    | (n, Some m) => enc_pair (n, 1 + m)
    end).
    
(* construct a simple semi-Thue system *)
Definition ssts : Ssts := map (fun '((a, b), (c, d)) => ((enc a, enc b), (enc c, enc d))) srs.

Lemma sim_step {s t} : SR2ab.step srs s t -> SSTS.step ssts (map enc s) (map enc t).
Proof.
  case => > ?. rewrite ?map_app /=.
  apply: step_intro. rewrite /ssts in_map_iff.
  eexists. by constructor; last by eassumption.
Qed.

Lemma enc_inj {a b} : enc a = enc b -> a = b.
Proof.
  rewrite /enc. move: (sym_eq_dec a a0) (sym_eq_dec a b0) (sym_eq_dec b a0) (sym_eq_dec b b0).
  move=> [] ? [] ? [] ? [] ? /=; try congruence.
  move: (a) (b) => [? [?|]] [? [?|]] /= [] /enc_pair_inj []; by congruence.
Qed.

Lemma map_enc_inj {s t} : map enc s = map enc t -> s = t.
Proof.
  elim: s t; first by case.
  move=> ? ? IH [|? ?]; first done.
  by move=> /= [/enc_inj -> /IH ->].
Qed.

Lemma inv_sim_step {s t'} : SSTS.step ssts (map enc s) t' -> exists t, t' = map enc t /\ SR2ab.step srs s t.
Proof.
  move Hs': (map enc s) => s' Hs't'.
  case: Hs't' Hs' => u' v' a' b' c' d' H Hs.
  move: H. rewrite /ssts in_map_iff. move=> [[[a b]]] [c d] [[]] ? ? ? ?. subst.
  move=> H. exists (firstn (length u') s ++ c :: d :: skipn (length u' + 2) s). constructor.
  - rewrite map_app /= -firstn_map -skipn_map Hs.
    rewrite firstn_app (ltac:(lia) : length u' - length u' = 0) firstn_all.
    rewrite skipn_app (ltac:(lia) : length u' + 2 - length u' = 2) skipn_all2 /=; first by lia.
    by rewrite app_nil_r.
  - move: H => /SR2ab.stepI. apply; last done.
    apply: map_enc_inj. rewrite Hs map_app /= -firstn_map -skipn_map Hs.
    rewrite firstn_app (ltac:(lia) : length u' - length u' = 0) firstn_all.
    rewrite skipn_app (ltac:(lia) : length u' + 2 - length u' = 2) skipn_all2 /=; first by lia.
    by rewrite app_nil_r.
Qed.

Lemma repeat_a0 {n} : repeat 0 n = map enc (repeat a0 n).
Proof.
  elim: n; first done.
  move=> n /= ->. congr cons.
  rewrite /enc. by case: (sym_eq_dec a0 a0).
Qed.

Lemma repeat_b0 {n} : repeat 1 n = map enc (repeat b0 n).
Proof using Ha0b0.
  elim: n; first done.
  move=> n /= ->. congr cons.
  rewrite /enc. case: (sym_eq_dec b0 a0); [done | by case: (sym_eq_dec b0 b0)].
Qed.

Lemma transport n :
  SR2ab.multi_step srs (repeat a0 (1+n)) (repeat b0 (1+n)) ->
  SSTS.multi_step ssts (repeat 0 (1+n)) (repeat 1 (1+n)).
Proof using Ha0b0.
  rewrite repeat_a0 repeat_b0. 
  move: (repeat a0 _) (repeat b0 _) => s t. elim.
  - move=> > ?. apply: rt_step. by apply: sim_step.
  - move=> *. by apply rt_refl.
  - move=> *. apply: rt_trans; by eassumption.
Qed.

Lemma inverse_transport n :
  SSTS.multi_step ssts (repeat 0 (1+n)) (repeat 1 (1+n)) ->
  SR2ab.multi_step srs (repeat a0 (1+n)) (repeat b0 (1+n)).
Proof using Ha0b0.
  rewrite repeat_a0 repeat_b0.
  move: (repeat a0 _) (repeat b0 _) => s t.
  move Hs': (map enc s) => s'. move Ht': (map enc t) => t' /(@clos_rt_rt1n_iff _ _) Hs't'.
  elim: Hs't' s t Hs' Ht'.
  - move=> ? s t *. subst. have -> : s = t by apply: map_enc_inj. 
    by apply rt_refl.
  - move=> > IH1 _ IH2 *. subst. move: IH1 => /inv_sim_step [t] [? ?]. subst.
    apply /rt_trans; [apply: rt_step; by eassumption | by apply: IH2].
Qed.

End SR2ab_SSTS01.

End Argument.

Import MM2 SSTS.
Require Import Undecidability.Synthetic.Definitions.

(* Two Counter Machine Halting starting from (0, 0) 
   many-one reduces to Simple Semi-Thue System 01 Rewriting *)
Theorem reduction : MM2_ZERO_HALTING ⪯ SSTS01.
Proof.
  eexists=> [mm]. split.
  - move=> [c'0] [Hc0c'0 Hc'0]. eexists.
    by apply: Argument.transport; [|apply: SR2ab.to_SR2ab; eassumption].
  - move=> [N HN].
    apply: SR2ab.to_MM2_ZERO_HALTING.
    by apply: Argument.inverse_transport; [|eassumption].
Qed.
