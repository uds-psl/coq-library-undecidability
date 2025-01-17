From Undecidability.LambdaCalculus Require Import Krivine Lambda Util.term_facts.
Require Import Undecidability.L.Util.L_facts.

From Stdlib Require Import List Lia Relations.
Import ListNotations.
Import L (term, var, app, lam).
Import Lambda (wCBN_step, subst).

#[local] Notation step := wCBN_step.

From Stdlib Require Import ssreflect.

Set Default Goal Selector "!".

#[local] Unset Implicit Arguments.

Lemma halt_cbnE ts ctx u : halt_cbn ts ctx u ->
  match u with
  | var 0 =>
      match ctx with
      | [] => False
      | (closure ctx' t')::_ => halt_cbn ts ctx' t'
      end
  | var (S n) => 
      match ctx with
      | [] => False
      | _::ctx' => halt_cbn ts ctx' (var n)
      end
  | app s t => halt_cbn ((closure ctx t) :: ts) ctx s
  | lam s =>
      match ts with
      | [] => True
      | t'::ts' => halt_cbn ts' (t'::ctx) s
      end
  end.
Proof. by case. Qed.

(* recursively substitute each local context, rename all free varaibles to 0 *)
Fixpoint flatten (u : eterm) : term :=
  let '(closure ctx t) := u in subst (fun n => ren (fun _ => 0) (nth n (map flatten ctx) (var 0))) t.

Lemma flatten_var_0 t ctx :
  flatten (closure (t :: ctx) (var 0)) = flatten t.
Proof.
  move: t => [? ?] /=. rewrite !simpl_term /=.
  apply: ext_subst_term => ?. by rewrite !simpl_term.
Qed.

Lemma flatten_var_S t ctx n :
  flatten (closure (t :: ctx) (var (S n))) = flatten (closure ctx (var n)).
Proof. done. Qed.

Fixpoint term_size (t : term) : nat :=
  match t with
  | var n => n
  | app s t => 1 + term_size s + term_size t
  | lam s => 1 + term_size s
  end.

Fixpoint eterm_size (u : eterm) : nat :=
  let '(closure ctx t) := u in 1 + list_sum (map eterm_size ctx) + (term_size t).

Lemma eterm_ind' (P : eterm -> Prop) :
  (forall (l : list eterm) (t : term), Forall P l -> P (closure l t)) ->
  forall u, P u.
Proof.
  move=> H. elim /(Nat.measure_induction _ eterm_size).
  move=> [ctx t] IH. apply: H.
  elim: ctx IH.
  - by constructor.
  - move=> ?? IH IH'. constructor.
    + apply: IH'=> /=. lia.
    + apply: IH => /= *. apply: IH'=> /=. lia.
Qed.

Definition context_size (ctx : list eterm) : nat :=
  eterm_size (closure ctx (var 0)).

Lemma flatten_cons u sigma s :
  subst (fun n : nat => ren (fun _ => 0) (scons u sigma n)) s =
  subst (scons (ren (fun _ => 0) u) var)
    (subst (scons (var 0) (funcomp (ren S) (funcomp (ren (fun _ => 0)) sigma))) s).
Proof.
  rewrite /= !simpl_term. apply: ext_subst_term.
  move=> [|n] /=; first done.
  by rewrite !simpl_term ren_as_subst_term.
Qed.

(* halt_cbn is invariant closure flattening *)
Lemma halt_cbn_flatten_iff {ts1 ts2 ctx1 ctx2 s1 s2} :
  halt_cbn ts1 ctx1 s1 ->
  map flatten ts1 = map flatten ts2 ->
  flatten (closure ctx1 s1) = flatten (closure ctx2 s2) ->
  halt_cbn ts2 ctx2 s2.
Proof.
  move=> H. elim: H ts2 ctx2 s2; clear ts1 ctx1 s1.
  - move=> ts ctx t ctx' ? IH ts2 ctx2 s2.
    rewrite flatten_var_0. by move=> /IH /[apply].
  - move=> ts1 ctx1 n t ? IH ts2 ctx2 s2.
    rewrite flatten_var_S. by move=> /IH /[apply].
  - move=> ts1 ctx1 s t ? IH ts2 ctx2 s2.
    elim /(Nat.measure_induction _ context_size): ctx2 s2.
    move=> ctx2 IH' []. 
    + (* s2 is (var n) *)
      move: ctx2 IH' => [|[ctx'2 t'2] ctx2] IH'. { by case. }
      move=> [|n].
      * rewrite flatten_var_0.
        move=> /= ??. apply: halt_var_0. apply: IH' => //=.
        rewrite /context_size /=. lia.
      * rewrite flatten_var_S.
        move=> /= ??. apply: halt_var_S. apply: IH' => //=.
        rewrite /context_size /=. lia.
    + move=> ??? /= [] /IH {}IH ?.
      apply: halt_app. apply: IH => //=. by congr cons.
    + done.
  - move=> t1 ts1 ctx1 s1 ? IH [|t2 ts2] ctx2 s2; first done.
    move=> [Ht1t2 ?].
    elim /(Nat.measure_induction _ context_size): ctx2 s2.
    move=> ctx2 IH' []. 
    + (* s2 is (var n) *)
      move: ctx2 IH' => [|[ctx'2 t'2] ctx2] IH'. { by case. }
      move=> [|n].
      * rewrite flatten_var_0.
        move=> /= ?. apply: halt_var_0. apply: IH' => //=.
        rewrite /context_size /=. lia.
      * rewrite flatten_var_S.
        move=> /= ?. apply: halt_var_S. apply: IH' => //=.
        rewrite /context_size /=. lia.
    + done.
    + move=> s2 /= [Hs1s2]. apply: halt_lam_ts. apply: IH => //=.
      by rewrite Ht1t2 !flatten_cons Hs1s2.
  - move=> ctx1 s1 [|t2 ts2] ctx2 s2; last done.
    move=> _.
    elim /(Nat.measure_induction _ context_size): ctx2 s2.
    move=> ctx2 IH' []. 
    + (* s2 is (var n) *)
      move: ctx2 IH' => [|[ctx'2 t'2] ctx2] IH'. { by case. }
      move=> [|n].
      * rewrite flatten_var_0.
        move=> /= ?. apply: halt_var_0. apply: IH' => //=.
        rewrite /context_size /=. lia.
      * rewrite flatten_var_S.
        move=> /= ?. apply: halt_var_S. apply: IH' => //=.
        rewrite /context_size /=. lia.
    + done.
    + move=> *. by apply: halt_lam.
Qed.

Lemma step_halt_cbn s t ts ctx : closed s -> step s t ->
  halt_cbn ts ctx t -> halt_cbn ts ctx s.
Proof.
  move=> Hs Hst. elim: Hst Hs ts ctx; clear s t.
  - move=> s t /closed_app [Hs Ht] ts ctx H'.
    apply: halt_app. apply: halt_lam_ts.
    apply: (halt_cbn_flatten_iff H'); first done.
    rewrite /= !simpl_term /=. apply: ext_subst_term.
    move=> [|n] /=; last done.
    rewrite !simpl_term. apply: ext_subst_term.
    move=> n /=. by rewrite !simpl_term.
  - move=> s s' t ? IH /closed_app [Hs Ht] ts ctx /halt_cbnE /IH {}IH.
    apply: halt_app. by apply: IH.
Qed.

#[local] Notation all := (fold_right and True).

Fixpoint eclosed (u : eterm) :=
  let '(closure ctx t) := u in bound (length ctx) t /\ all (map eclosed ctx).

Lemma eclosed_closed t : 
  (forall sigma, subst sigma t = t) ->
  eclosed (closure [] t).
Proof.
  move=> H. split; last done.
  apply /closed_dcl /closed_I.
  move=> ?. by rewrite L_subst_Lambda_subst.
Qed.

Inductive Krivine_step : (list eterm * list eterm * term) -> (list eterm * list eterm * term) -> Prop :=
  | Krivine_step_var_0 ts ctx t ctx' : Krivine_step (ts, (closure ctx t)::ctx', var 0) (ts, ctx, t)
  | Krivine_step_var_S ts t ctx n : Krivine_step (ts, t::ctx, var (S n)) (ts, ctx, var n)
  | Krivine_step_app ts ctx s t : Krivine_step (ts, ctx, app s t) ((closure ctx t)::ts, ctx, s)
  | Krivine_step_lam t ts ctx s : Krivine_step (t::ts, ctx, lam s) (ts, t::ctx, s).

Lemma halt_cbn_Krivine_step ts ctx t : halt_cbn ts ctx t ->
  exists ctx' t', clos_refl_trans _ Krivine_step (ts, ctx, t) (nil, ctx', lam t').
Proof.
  elim.
  - move=> > ? [?] [?] ?. do 2 eexists.
    apply: rt_trans; [apply: rt_step; by constructor|eassumption].
  - move=> > ? [?] [?] ?. do 2 eexists.
    apply: rt_trans; [apply: rt_step; by constructor|eassumption].
  - move=> > ? [?] [?] ?. do 2 eexists.
    apply: rt_trans; [apply: rt_step; by constructor|eassumption].
  - move=> > ? [?] [?] ?. do 2 eexists.
    apply: rt_trans; [apply: rt_step; by constructor|eassumption].
  - move=> >. do 2 eexists. by apply: rt_refl.
Qed. 

Lemma Krivine_step_halt_cbn ts ctx t ctx' t' : clos_refl_trans _ Krivine_step (ts, ctx, t) (nil, ctx', lam t') ->
  halt_cbn ts ctx t.
Proof.
  move=> /clos_rt_rt1n_iff.
  move E: ([], ctx', lam t') => x H.
  change (halt_cbn ts ctx t) with (halt_cbn (fst (fst (ts, ctx, t))) (snd (fst (ts, ctx, t))) (snd (ts, ctx, t))).
  elim: H E.
  - move=> ? <-. by constructor.
  - move=> > H _ IH ?. subst. case: H IH=> > /(_ eq_refl) ?; by constructor.
Qed.

Lemma Krivine_step_eclosed ts ctx t ts' ctx' t' : Krivine_step (ts, ctx, t) (ts', ctx', t') -> Forall eclosed ts -> eclosed (closure ctx t) ->
  Forall eclosed ts' /\ eclosed (closure ctx' t').
Proof.
  move EX: (ts, ctx, t) => X.
  move EY: (ts', ctx', t') => Y H.
  case: H EX EY=> > [-> -> ->] [-> -> ->] /=.
  - tauto.
  - move=> ? [/boundE] *. split; [done|split; [apply: dclvar; lia|tauto]].
  - move=> ? [/boundE] ??. split; [|tauto].
    constructor; cbn; tauto.
  - move=> /Forall_cons_iff ? [/boundE]. tauto.
Qed.

Lemma Krivine_step_halt_cbn_step ts ctx t ts' ctx' t' :
  Krivine_step (ts, ctx, t) (ts', ctx', t') ->
  halt_cbn ts' ctx' t' -> halt_cbn ts ctx t.
Proof.
  move EX: (ts, ctx, t) => X.
  move EY: (ts', ctx', t') => Y H.
  case: H EX EY=> > [-> -> ->] [] *; subst.
  all: by constructor.
Qed.

Lemma Krivine_step_halt_cbn' ts ctx t Y : clos_refl_trans _ Krivine_step (ts, ctx, t) Y ->
  Forall eclosed ts -> eclosed (closure ctx t) -> (forall Z, not (Krivine_step Y Z)) ->
  halt_cbn ts ctx t.
Proof.
  move E: (ts, ctx, t) => X /clos_rt_rt1n_iff H.
  elim: H ts ctx t E.
  - move=> [[ts ctx] t] > [-> -> ->].
    move: t => [[|x]|s t|t].
    + move: ctx => [|[??]?] /=.
      * move=> ? [/boundE]. lia.
      * move=> _ _ H. exfalso. apply: H. by constructor.
    + move: ctx => [|[??]?] /=.
      * move=> ? [/boundE]. lia.
      * move=> _ _ H. exfalso. apply: H. by constructor.
    + move=> _ _ H. exfalso. apply: H. by constructor.
    + move: ts => [|??] /=.
      * move=> *. by constructor.
      * move=> _ _ H. exfalso. apply: H. by constructor.
  - move=> [[??]?] [[??]?] ? /[dup] /Krivine_step_eclosed H1.
    move=> /Krivine_step_halt_cbn_step H _ IH ??? [???] *. subst.
    apply: H. apply: IH; tauto.
Qed.
