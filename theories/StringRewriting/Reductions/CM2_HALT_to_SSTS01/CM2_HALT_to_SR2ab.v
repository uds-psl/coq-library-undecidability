Require Import List Relation_Operators Operators_Properties Lia.
Import ListNotations.

Require Import Undecidability.StringRewriting.Reductions.CM2_HALT_to_SSTS01.SR2ab.
Require Import Undecidability.CounterMachines.CM2.

Require Import Undecidability.StringRewriting.Util.List_facts.
Require Import Undecidability.StringRewriting.Reductions.CM2_HALT_to_SSTS01.SR2ab_facts.
Require Import Undecidability.CounterMachines.Util.Facts Undecidability.CounterMachines.Util.CM2_facts.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

Local Arguments rt_trans {A R x y z}.
Local Arguments in_combine_l {A B l l' x y}.

Module Facts.

Lemma iter_plus {X: Type} {f: X -> X} {x: X} {n m: nat} : 
  Nat.iter (n + m) f x = Nat.iter n f (Nat.iter m f x).
Proof. by rewrite /Nat.iter nat_rect_plus. Qed.

Lemma nth_error_Some_in_combine {X: Type} {l: list X} {i x}:
  nth_error l i = Some x -> 
  In (i, x) (combine (seq 0 (length l)) l).
Proof.
  move Hk: (0) => k Hi. have ->: (i = i + k) by lia.
  elim: l i k {Hk} Hi; first by case.
  move=> y l IH [|i] k.
  - move=> /= [<-]. by left.
  - move=> /IH {}IH /=. right. by have ->: (S (i + k) = i + S k) by lia.
Qed.

Lemma inv_nth_error_Some_in_combine {X: Type} {l: list X} {i x}:
  In (i, x) (combine (seq 0 (length l)) l) -> nth_error l i = Some x.
Proof.
  move Hk: (0) => k. rewrite [in (_, _)](ltac:(lia) : (i = i + k)).
  elim: l i k {Hk}; first by case.
  move=> y l IH i k /= [].
  - move=> [? ->]. by have ->: i = 0 by lia.
  - move: i => [|i].
    + move=> /in_combine_l /in_seq. by lia.
    + have ->: S i + k = i + S k by lia.
      by move=> /IH.
Qed.
End Facts.

Module Argument.
Import Facts.
Local Arguments List.app : simpl never.
Local Arguments Nat.sub : simpl never.
Local Arguments repeat : simpl never.
Local Arguments app_inj_tail {A x y a b}.

Section Reduction.
(* given two-counter machine *)
Context (cm : Cm2).

Fixpoint cm_steps n x :=
  match n with
  | 0 => x
  | S n => if CM2.step cm x is Some y then cm_steps n y else x
  end.

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

Definition states := map (fun i => if i is dec _ q then q else 0) cm.
Definition sum : list nat -> nat := fold_right Nat.add 0. 

Definition state_bound := 1 + length cm + sum states.

Lemma state_boundP {p i} : nth_error cm p = Some i -> 
  (if i is dec _ q then q else 0) + 1 + p < state_bound.
Proof.
  rewrite /state_bound /states.
  elim: (cm) p; first by case.
  move=> ? l IH [|p] /= => [[->] | /IH]; last by lia.
  by case: (i); lia.
Qed.

(* encode instruction i at position n *)
Definition enc_Instruction (ni: (nat * Instruction)) : Srs :=
  match ni with
  | (p, inc b) => if b then [((sr' p, sz), (sb, sr' (S p)))] else [((sz, sl' p), (sl' (S p), sb))]
  | (p, dec b q) => 
      if b then [((sm, sr' p), (sm, sr' (S p))); ((sb, sr' p), (sr' q, sz))] 
      else [((sl' p, sm), (sl' (S p), sm)); ((sl' p, sb), (sz, sl' q))]
  end.

(* constructed string rewriting system *)
Definition srs : Srs := 
  (* initialization *)
  [((sz, sz), (st, sr)); (* 00 -> tr *)
   ((sz, st), (sl' 0, sm)) (* 0t -> l_0 m *)] ++
  (* simulation *)
  flat_map enc_Instruction (combine (seq 0 (length cm)) cm) ++
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
  map (fun p => ((sz, sl' p), (so, so))) (seq (length cm) (state_bound - length cm)) ++
  [((sz, so), (so, so)); ((so, sb), (so, so)); ((so, sm), (so, so)); 
   ((so, sr), (so, so)); ((so, sz), (so, so))].

(* initialization, simulation, finalization *)
Inductive srs_spec (a b c d: Symbol) : Prop :=
  | srs_i0 : ((sz, sz), (st, sr)) = ((a, b), (c, d)) -> srs_spec a b c d
  | srs_i1 : ((sz, st), (sl' 0, sm)) = ((a, b), (c, d)) -> srs_spec a b c d
  | srs_sim0 {p} : ((sr' p, sz), (sb, sr' (S p))) = ((a, b), (c, d)) -> nth_error cm p = Some (inc true) -> srs_spec a b c d
  | srs_sim1 {p} : ((sz, sl' p), (sl' (S p), sb)) = ((a, b), (c, d)) -> nth_error cm p = Some (inc false) -> srs_spec a b c d
  | srs_sim2 {p q} : ((sm, sr' p), (sm, sr' (S p))) = ((a, b), (c, d)) -> nth_error cm p = Some (dec true q) -> srs_spec a b c d
  | srs_sim3 {p q} : ((sb, sr' p), (sr' q, sz))= ((a, b), (c, d)) -> nth_error cm p = Some (dec true q) -> srs_spec a b c d
  | srs_sim4 {p q} : ((sl' p, sm), (sl' (S p), sm)) = ((a, b), (c, d)) -> nth_error cm p = Some (dec false q) -> srs_spec a b c d
  | srs_sim5 {p q} : ((sl' p, sb), (sz, sl' q)) = ((a, b), (c, d)) -> nth_error cm p = Some (dec false q) -> srs_spec a b c d
  | srs_fin0 {p} : ((sz, sl' p), (so, so)) = ((a, b), (c, d)) -> length cm <= p < state_bound -> srs_spec a b c d
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
  { move=> /in_flat_map [[? i]] [/inv_nth_error_Some_in_combine].
    move: i => [] [] > /=; firstorder (by eauto using srs_spec with nocore). }
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
  by firstorder (by eauto using srs_spec with nocore).
Qed.

Lemma In_srsI {a b c d} : srs_spec a b c d \/ srs_mlr_spec a b c d -> In ((a, b), (c, d)) srs.
Proof.
  case.
  - move=> [] > <- *.
    1-2: apply /In_appl; rewrite /=; by tauto.
    1-6: apply /In_appr /In_appl /in_flat_map; eexists; 
      (constructor; [apply: nth_error_Some_in_combine; by eassumption | by move=> /=; tauto ]).
    1: apply /In_appr /In_appr /In_appr /In_appr /In_appl /in_map_iff; eexists;
      (constructor; [by reflexivity | apply /in_seq; by lia ]).
    1-5: do 5 (apply /In_appr); move=> /=; by tauto.
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

Section Transport.
(* number of steps until halting *)
Context (n_cm: nat).
Definition c0 := (0, (0, 0)).
Context (H_n_cm: CM2.steps cm n_cm c0 = None).

Lemma cm_steps_S n x : cm_steps (S n) x = cm_steps 1 (cm_steps n x).
Proof.
  elim: n x; first done.
  move=> n IH x.
  have ->: S (S n) = (S n) + 1 by lia.
  rewrite /=.
  have ->: n + 1 = S n by lia.
  case Hxy: (step cm x) => [y|].
  - by rewrite IH.
  - by rewrite Hxy.
Qed.

Lemma cm_steps_plus n m x : cm_steps (n + m) x = cm_steps n (cm_steps m x).
Proof.
  elim: n; first done.
  move=> n IH. by rewrite [S n + m]/= (cm_steps_S (n + m)) (cm_steps_S n) IH.
Qed.

Lemma steps_Some_cm_steps n x y : steps cm n x = Some y -> cm_steps n x = y.
Proof.
  elim: n x. { by move=> ? [<-]. }
  move=> n IH x /=. rewrite obind_oiter.
  case: (step cm x) => [z|]; last by rewrite oiter_None.
  by apply: IH.
Qed.

Lemma steps_None_cm_steps n x : steps cm n x = None ->
  cm_steps 1 (cm_steps n x) = (cm_steps n x).
Proof.
  elim: n x; first done.
  move=> n IH x /=. rewrite obind_oiter.
  case Hxy: (step cm x) => [y|]; last by rewrite Hxy.
  by move=> /IH.
Qed.

(*
Lemma cm_steps_ub n : steps cm n c0 = None -> cm_steps n c0 = cm_steps n_cm c0.
Proof.
  elim: n (n_cm) (H_n_cm); first done.
  move=> n IH [|n_cm']; first done.
  rewrite /=.
*)

Lemma cm_steps_haltingP x : cm_steps 1 x = x <-> length cm <= state x.
Proof using.
  rewrite /=.
  case Hxy: (step cm x) => [y|].
  { split.
    - move=> ?. subst y. by move: Hxy => /step_neq.
    - move=> /nth_error_None Hx. move: Hxy.
      by rewrite /step Hx. }
  split; last done.
  by move: Hxy => /step_None'.
Qed.

Lemma halting_eq n : cm_steps (n + n_cm) c0 = cm_steps n_cm c0.
Proof using H_n_cm.
  elim: n; first done.
  move=> n IH.
  have ->: S n + n_cm = 1 + (n + n_cm) by lia.
  rewrite cm_steps_plus IH.
  by apply: steps_None_cm_steps.
Qed.

Lemma cm_steps_values_ub n : 
  value1 (cm_steps n c0) + value2 (cm_steps n c0) <= n.
Proof using.
  elim: n. { rewrite /=. lia. }
  move=> n IH. have ->: S n = 1 + n by lia.
  rewrite cm_steps_plus /=.
  case Hx: (step cm (cm_steps n c0)) => [x|]; last by lia.
  move: Hx => /step_values_bound. lia.
Qed.

Lemma cm_values_ub n : 
  value1 (cm_steps n c0) + value2 (cm_steps n c0) <= n_cm.
Proof using H_n_cm.
  have [?|->] : n <= n_cm \/ n = ((n - n_cm) + n_cm) by lia.
  - have := cm_steps_values_ub n. lia.
  - rewrite halting_eq.
    by apply: cm_steps_values_ub.
Qed.

Lemma cm_state_ub n : state (cm_steps n c0) < state_bound.
Proof.
  elim: n. { rewrite /= /state_bound. lia. }
  move=> n IH. have ->: S n = 1 + n by lia.
  rewrite cm_steps_plus /=.
  case Hx: (step cm (cm_steps n c0)) => [x|]; last done.
  move: Hx. rewrite /step.
  move: (cm_steps n c0) => [p [a b]] /=.
  case Hoi: (nth_error cm p) => [i|]; last done.
  move: Hoi => /state_boundP.
  case: i x.
  - move=> ? [? [? ?]] /= ? []. lia.
  - move: a b => [|?] [|?] [] ? [? [? ?]] /= ? []; lia.
Qed.

Definition d := 5 + n_cm + n_cm. (* maximal space requirement *)

(* s is (0^(n-a) l_p _^a m _^b r 0^(n-b)) with a unique state annotation *)
Definition enc_Config : Config -> list Symbol :=
  fun '(p, (a, b)) => 
    (repeat sz (1 + n_cm-a)) ++ [sl' p] ++ (repeat sb a) ++ [sm] ++ 
    (repeat sb b) ++ [sr] ++ (repeat sz (1 + n_cm-b)).

(* s is (0^(n-a) l _^a m _^b r_p 0^(n-b)) with a unique state annotation *)
Definition enc_Config' : Config -> list Symbol :=
  fun '(p, (a, b)) => 
    (repeat sz (1 + n_cm-a)) ++ [sl] ++ (repeat sb a) ++ [sm] ++ 
    (repeat sb b) ++ [sr' p] ++ (repeat sz (1 + n_cm-b)).

Lemma multi_step_enc_c0 : multi_step srs (repeat sz d) (enc_Config c0).
Proof using.
  apply: (rt_trans (y := (repeat sz (1 + n_cm)) ++ [sz] ++ [st] ++ [sr] ++ (repeat sz (1 + n_cm)))).
  - have ->: d = 1 + n_cm + 1 + 1 + 1 + 1 + n_cm by (rewrite /d; lia).
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

Lemma move_right n : let c := (cm_steps n c0) in 
  multi_step srs (enc_Config c) (enc_Config' c). 
Proof.
  move=> c. subst c. have := cm_state_ub n.
  move: (cm_steps n c0) => [p [a b]] /= ?.
  apply: multi_step_applI. rewrite ?app_assoc. apply: multi_step_apprI.
  apply: (rt_trans (y := [sl] ++ (repeat sb a) ++ [sm' p] ++ (repeat sb b) ++ [sr])).
  - rewrite ?app_assoc. do 2 apply: multi_step_apprI.
    apply: move_sb_right'; by tauto.
  - rewrite -?app_assoc. do 2 apply: multi_step_applI.
    apply: move_sb_right'; by tauto.
Qed.

Lemma move_left n : let c := (cm_steps n c0) in 
  multi_step srs (enc_Config' c) (enc_Config c). 
Proof.
  move=> c. subst c. have := cm_state_ub n.
  move: (cm_steps n c0) => [p [a b]] /= ?.
  apply: multi_step_applI. rewrite ?app_assoc. apply: multi_step_apprI.
  apply: (rt_trans (y := [sl] ++ (repeat sb a) ++ [sm' p] ++ (repeat sb b) ++ [sr])).
  - rewrite -?app_assoc. do 2 apply: multi_step_applI.
    apply: move_sb_left'; by tauto.
  - rewrite ?app_assoc. do 2 apply: multi_step_apprI.
    apply: move_sb_left'; by tauto.
Qed.

Lemma simulate_cm_step {n} : let c := (cm_steps n c0) in
  multi_step srs (enc_Config c) (enc_Config (cm_steps 1 c)).
Proof using H_n_cm.
  move=> c. subst c.
  have := cm_values_ub n.
  have := move_right n. have := move_left (1+n).
  rewrite cm_steps_plus /=.
  case: (cm_steps n c0) => p [a b] /=. rewrite /step.
  move Hoi: (nth_error cm p) => oi.
  case: oi Hoi; last by (move=> *; apply: rt_refl). case; case.
  (* inc b *)
  - move=> ? /= Hr Hl ?.
    apply: rt_trans; first by eassumption.
    apply: rt_trans; last by eassumption.
    have [-> ->]: S b = b + 1 /\ S n_cm - b = 1 + (S n_cm - (b + 1)) by lia.
    rewrite ?repeat_app -?app_assoc. do 5 apply: multi_step_applI.
    apply /rt_step /stepI_nil. by eauto with in_srs_db nocore.
  (* inc a *)
  - move=> ? _ _ ? /=.
    have [-> ->]: S n_cm - a = (n_cm - a) + 1 /\ S a = 1 + a by lia.
    rewrite ?repeat_app -?app_assoc. apply: multi_step_applI.
    apply /rt_step /stepI_nil. by eauto with in_srs_db nocore.
  (* dec b q *)
  - move=> q ? /= Hr Hl Hb.
    apply: rt_trans; first by eassumption.
    apply: rt_trans; last by eassumption.
    case: (b) Hb => [_ | b' Hb'] /=.
    + do 3 apply: multi_step_applI.
      apply /rt_step /stepI_nil. by eauto with in_srs_db nocore.
    + have [-> ->] : S b' = b' + 1 /\ S n_cm - b' = 1 + (S n_cm - (b' + 1)) by lia.
      rewrite ?repeat_app -?app_assoc. do 5 apply: multi_step_applI. 
      apply /rt_step /stepI_nil. by eauto with in_srs_db nocore.
  (* dec a q*)
  - move=> q ? _ _ Ha.
    case: (a) Ha => [_ | a' Ha'] /=.
    + apply /multi_step_applI /rt_step /stepI_nil.
      by eauto with in_srs_db nocore.
    + rewrite (ltac:(lia) : (S n_cm - a' = (n_cm - a') + 1)) repeat_app -?app_assoc.
      apply /multi_step_applI /rt_step /stepI_nil.
      by eauto with in_srs_db nocore.
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

Lemma simulate_cm_halting {n} : let c := (cm_steps n c0) in
  cm_steps 1 c = c -> multi_step srs (enc_Config c) (repeat so d).
Proof using H_n_cm.
  move=> c. subst c. move=> /cm_steps_haltingP.
  have := cm_values_ub n. have := cm_state_ub n.
  move: (cm_steps n c0) => [p [a b]] /= *.
  apply: (rt_trans (y := (repeat sz (n_cm - a)) ++ [so] ++ [so] ++ _)).
  - rewrite (ltac:(lia) : S n_cm - a = (n_cm - a) + 1) repeat_app -?app_assoc.
    apply /multi_step_applI /rt_step /stepI_nil.
    by eauto with in_srs_db nocore.
  - apply: (rt_trans (y := (repeat so (n_cm - a + 1) ++ [so] ++
      repeat sb a ++ [sm] ++ repeat sb b ++ [sr] ++ repeat sz (S n_cm - b)))).
    + rewrite ?app_assoc. do 6 apply: multi_step_apprI. by apply: multi_step_repeat_solI.
    + have ->: d = (n_cm - a + 1) + 1 + a + 1 + b + 1 + (S n_cm - b) by (rewrite /d; lia).
      rewrite ?repeat_app -?app_assoc. do 2 apply: multi_step_applI.
      apply: multi_step_repeat_sorI'; first by left.
      apply: (rt_trans (y := ([so] ++ [so] ++ repeat sb b ++ [sr] ++ repeat sz (S n_cm - b)))).
      * apply /rt_step /stepI_nil. by eauto with in_srs_db nocore.
      * apply: multi_step_applI. apply: multi_step_repeat_sorI'; first by left.
        apply: (rt_trans (y := ([so] ++ [so] ++ repeat sz (S n_cm - b)))).
        ** apply /rt_step /stepI_nil. by eauto with in_srs_db nocore.
        ** apply: multi_step_applI. apply: multi_step_repeat_sorI. by right.
Qed.
End Transport.

Lemma transport : CM2_HALT cm -> SR2ab (srs, sz, so).
Proof.
  move=> [n Hn]. move: (Hn) (Hn) => /steps_None_cm_steps.
  move=> /simulate_cm_halting H /H {}H. exists (@d n - 1).
  apply: rt_trans; last by eassumption.
  apply: rt_trans; first by apply: (multi_step_enc_c0).
  elim: (n in cm_steps n); first by apply: rt_refl.
  move=> m IH {H}. apply: rt_trans; [by exact: IH |].
  rewrite cm_steps_S. by apply: simulate_cm_step.
Qed.

Section InverseTransport.
Context (N: nat). (* number of 0s / 1s *)
Context (HN: multi_step srs (repeat sz (1+N)) (repeat so (1+N))). (* 0^N ->> 1^N *)

Local Definition rt_rt1n {A R x y} := @clos_rt_rt1n_iff A R x y.

(* s is (0^n1 l _^a m _^b r 0^n2) with a unique state annotation *)
Definition encodes : Config -> list Symbol -> Prop :=
  fun c s => 
  exists u v t, let '(p, (a, b)) := c in
    s = u ++ t ++ v /\
    map fst t = map fst ([sl] ++ repeat sb a ++ [sm] ++ repeat sb b ++ [sr]) /\
    filter (fun x => if x is None then false else true) (map snd t) = [Some p].

Lemma In_srs_stE {a b c d} : In ((a, b), (c, d)) srs ->
  ((sz, sz), (st, sr)) = ((a, b), (c, d)) \/
  ((sz, st), (sl' 0, sm)) = ((a, b), (c, d)) \/
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
    move=> /= ->. exists u, v', [sl' 0; sm; sr].
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
    + move=> [] <- <- /=. right. by left.
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

(* specification of inner Cm2 step *)
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
Lemma simulate_srs_step {c s t} : SR2ab.step srs s t -> encodes c s -> 
  cm_steps 1 c = c \/ encodes c t \/ encodes (cm_steps 1 c) t.
Proof.
  move: c => [p [a b]] [] u v a' b' c' d' H [u'] [v'] [{}t].
  rewrite -?/([_] ++ [_] ++ v). move=> [+] [H1t H2t] => /eq2_app_app.
  have : length t > 1.
  { move: H1t => /(congr1 (@length _)).
    rewrite ?map_app ?app_length ?map_length /=. move=> ->. by lia. }
  move=> Ht /(_ Ht) {Ht}.
  case; [|case; [|case; [|case]]].
  - move=> [u'2 ->]. right. left.
    exists (u ++ c' :: d' :: u'2), v', t.
    constructor; [by rewrite -?app_assoc | done].
  - move=> [s2] [?] [? ?]. subst. move: H1t H2t => [].
    move: H => /srs_specI [|] [] > [] ? ? ? ?; subst; try done; [|].
    + move=> Hi _ H1s2 [<- H2s2]. right. right.
      rewrite /= /step Hi. eexists u, v', (_ :: _ :: s2).
      constructor; [done | constructor; by rewrite /= ?H1s2  ?H2s2].
    + move=> ? _ _ [<-] _ *. left.
      apply /cm_steps_haltingP => /=. by lia.
  - move=> [s1] [s2] [?] [? ?]. subst.
    move: H H1t H2t => /srs_specI [].
    + move=> H + + /ltac:(right; right). move=> /[dup] [/srs_step_specI] [].
      * move=> H'. move: H' H => [] ? ? ? ? [] > [] ? ? ? ?; subst; try done; [ | | | ].
        ** rewrite app_nil_r /= /step. move=> + [H1] [<-] => -> H2.
           eexists u', v', (_ :: _ :: _). constructor; [done | by rewrite /= H1 H2].
        ** rewrite app_nil_r /= ?map_app /step. move: (a) => [|?]; first done.
           move=> + [] H1 [<-] H2 => ->.
           eexists (u' ++ [sz]), v', (_ :: _).
           rewrite -?app_assoc. constructor; [done | by rewrite /= ?map_app H1 H2].
        ** rewrite ?map_app filter_app /= app_nil_r /step.
           move=> + + /(app_inj_tail (y := [])) [H2] [<-].
           move=> ->. rewrite ?app_assoc app_nil_r.
           move=> /app_inj_tail [/app_inj_tail] [H1] _ _.
           eexists u', v', (_ ++ [_; _]).
           rewrite -?app_assoc. constructor; first done.
           by rewrite ?map_app filter_app /= H1 H2.
        ** rewrite [in repeat sb b](ltac:(lia) : b = (b - 1) + 1) repeat_app.
           rewrite ?map_app ?filter_app ?app_assoc ?app_nil_r /= /step.
           move=> + + /(app_inj_tail (y := [])) [H2] [<-].
           move=> ->. move=> /app_inj_tail [/app_inj_tail] [H1] _ _.
           eexists u', ([sz] ++ v'), (_ ++ [_]).
           rewrite (ltac:(lia) : b = 1 + (b - 1)) -?app_assoc /=. 
           constructor; first done.
           by rewrite ?map_app filter_app /= H1 H2 -?app_assoc.
      * move: H => + + _ /ltac:(exfalso).
        move=> [] > [] *; subst; by firstorder done.
    + move=> + + + /ltac:(right; left; exists u', v', (s1 ++ c' :: d' :: s2)).
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
    right. right. rewrite /= /step Hi. eexists u', v, (s1 ++ [_; _]).
    rewrite -?app_assoc. constructor; [done | constructor].
    * move: H1s1. rewrite ?map_app ?app_assoc. move=> /app_inj_tail [-> _].
      by rewrite (ltac:(lia) : 1 + b = b + 1) [repeat _ (b + 1)]repeat_app map_app -?app_assoc.
    * by rewrite map_app filter_app /= H2s2.
  - move=> [v'1 ->]. right. left.
    exists u', (v'1 ++ c' :: d' :: v), t.
    constructor; [by rewrite -?app_assoc | done].
Qed.

Lemma halting_cmI : exists n, cm_steps 1 (cm_steps n c0) = cm_steps n c0.
Proof using HN.
  have [s [H1s H2s]] := init_encodes.
  move Ht: (repeat so (1+N)) (c0) H2s H1s => t c Hst.
  have {}Ht : Forall (fun x => fst so = x) (map fst t).
  { subst t. elim: (N); by constructor. }
  move: Hst Ht c. move=> /rt_rt1n. elim.
  - move=> {}s Hs [? [? ?]] /= [?] [?] [{}t] [?] [H]. subst s.
    move: Hs. rewrite ?map_app ?Forall_app H.
    by move=> [_] [/Forall_cons_iff] [].
  - move=> > /simulate_srs_step H _ IH /IH {}IH c /H {H} [|[]].
    + move=> ?. by exists 0.
    + by move=> /IH.
    + move=> /IH [n Hn]. exists (n + 1).
      by rewrite ?cm_steps_plus.
Qed.

End InverseTransport.

Lemma inverse_transport : SR2ab (srs, sz, so) -> CM2_HALT cm.
Proof.
  move=> [n Hn].
  have [m  Hm] := halting_cmI n Hn.
  exists (S m) => /=.
  case Hx: (steps cm m (0, (0, 0))) => [x|]; last done.
  move: (Hm) => /cm_steps_haltingP.
  move: (Hx) => /steps_Some_cm_steps.
  rewrite /c0 /= /step.
  by move=> -> /nth_error_None ->.
Qed.

End Reduction.
End Argument.

Require Import Undecidability.Synthetic.Definitions.

Theorem reduction : CM2_HALT ⪯ SR2ab.
Proof.
  exists (fun cm => (Argument.srs cm, (4, None), (5, Some 0))).
  intro cm. constructor.
  - exact (Argument.transport cm).
  - exact (Argument.inverse_transport cm).
Qed.
