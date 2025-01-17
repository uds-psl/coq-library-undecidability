(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  Abstract machine for closed L-term evaluation.

  A closed L-term s evaluates to a term t iff
  the abstract "machine" relates s with some closure y such that flatten y = t
*)

From Stdlib Require Import List Relations.
Import ListNotations.
Require Import Undecidability.L.L Undecidability.L.Util.L_facts.

From Stdlib Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

(* (closure ctx t) is a L-term t in the environment ctx *)
Inductive eterm := closure : list eterm -> term -> eterm.

Inductive machine : eterm -> list (bool * eterm) -> eterm -> Prop :=
  | machine_var_0 x xs vs y :
      machine x vs y ->
      machine (closure (x :: xs) (var 0)) vs y
  | machine_var_S x xs n vs y :
      machine (closure xs (var n)) vs y ->
      machine (closure (x :: xs) (var (S n))) vs y
  | machine_app xs s t vs y :
      machine (closure xs s) ((true, (closure xs t)) :: vs) y ->
      machine (closure xs (app s t)) vs y
  | machine_lam_swap xs s z vs y :
      machine z ((false, (closure xs s)) :: vs) y ->
      machine (closure xs (lam s)) ((true, z) :: vs) y
  | machine_lam_subst xss xts s t vs y :
      machine (closure ((closure xts (lam t)) :: xss) s) vs y ->
      machine (closure xts (lam t)) ((false, (closure xss s)) :: vs) y
  | machine_lam xs s :
      machine (closure xs (lam s)) nil (closure xs (lam s)).

(* generic facts *)
Module Facts.

(* transforms a goal (A -> B) -> C into goals A and B -> C *)
Lemma unnest : forall (A B C : Type), A -> (B -> C) -> (A -> B) -> C.
Proof. auto. Qed.

Lemma cons_inj {X : Type} {x1 x2 : X} {l1 l2} : x1 :: l1 = x2 :: l2 -> x1 = x2 /\ l1 = l2.
Proof. by case. Qed.

End Facts.

Import Facts.

(* highly sensitive! *)
Fixpoint subst_many (s : term) n (ts : list term) :=
  match s with
  | var x => nth x (map var (seq 0 n) ++ ts) (var x)
  | app s t => app (subst_many s n ts) (subst_many t n ts)
  | lam s => lam (subst_many s (S n) ts)
  end.

(* recursively substitute each local context *)
Fixpoint flatten (u : eterm) : term :=
  let '(closure ctx t) := u in subst_many t 0 (map flatten ctx).

Fixpoint term_size (t : term) : nat :=
  match t with
  | var n => S n
  | app s t => 1 + term_size s + term_size t
  | lam s => 2 + term_size s
  end.

Fixpoint eterm_size (u : eterm) : nat :=
  let '(closure ctx t) := u in list_sum (map eterm_size ctx) + (term_size t).

Definition context_size (ctx : list eterm) : nat :=
  eterm_size (closure ctx (var 0)).

Lemma term_size_S s : term_size s = S (Nat.pred (term_size s)).
Proof.
  elim: s => /=; lia.
Qed.

Lemma machineE xs s vs y : machine (closure xs s) vs y ->
  match s with
  | var 0 =>
    match xs with
    | x :: xs => machine x vs y
    | _ => False
    end
  | var (S n) =>
    match xs with
    | x :: xs => machine (closure xs (var n)) vs y
    | _ => False
    end
  | app s t => machine (closure xs s) ((true, (closure xs t)) :: vs) y
  | lam s =>
    match vs with
    | (true, z) :: vs => machine z ((false, (closure xs s)) :: vs) y
    | (false, (closure x's s')) :: vs => machine (closure ((closure xs (lam s)) :: x's) s') vs y
    | nil => True
    end
  end.
Proof.
  intros H. by inversion H.
Qed.

#[local] Notation all := (fold_right and True).

Fixpoint eclosed (u : eterm) :=
  let '(closure ctx t) := u in bound (length ctx) t /\ all (map eclosed ctx).

(* construct term from context *)
Fixpoint traverse (s : term) (vs : list (bool * eterm)) : term :=
  match vs with
  | nil => s
  | (true, u) :: vs => traverse (app s (flatten u)) vs
  | (false, closure xs u) :: vs => traverse (app (flatten (closure xs (lam u))) s) vs
  end.

Lemma boundE k s : bound k s ->
  match s with
  | var n => k > n
  | app s t => bound k s /\ bound k t
  | lam s => bound (S k) s
  end.
Proof. by case. Qed.

Lemma all_Forall {X : Type} {P : X -> Prop} {l : list X} : all (map P l) <-> Forall P l.
Proof.
  elim: l; [done|].
  move=> x l IH /=. split.
  - move=> [? /IH ?]. by constructor.
  - by move=> /Forall_cons_iff [? /IH ?].
Qed.

Lemma all_map_impl {X : Type} {P Q : X -> Prop} {l : list X} :
  (forall x, P x -> Q x) -> all (map P l) -> all (map Q l).
Proof.
  move=> /Forall_impl H /all_Forall /H ?. by apply /all_Forall.
Qed.

Lemma bound_subst_many s n ts : all (map closed ts) ->
  bound (n + length ts) s -> bound n (subst_many s n ts).
Proof.
  move=> Hts. elim: s n.
  - move=> x n /boundE ? /=.
    have [?|?] : x < n \/ n <= x by lia.
    + rewrite app_nth1. { by rewrite length_map length_seq. }
      by rewrite map_nth seq_nth; [|constructor].
    + rewrite app_nth2 length_map length_seq; [done|].
      apply: (@bound_ge 0); [|lia].
      apply /closed_dcl.
      rewrite (nth_indep _ _ (lam (var 0))); [lia|].
      case: (nth_in_or_default (x - n) ts (lam # 0)).
      * move: Hts => /all_Forall /Forall_forall. by apply.
      * by move=> ->.
  - move=> s IHs t IHt n /boundE [/IHs ? /IHt ?]. by constructor.
  - move=> s IHs n /boundE /(IHs (S n)) ?. by constructor.
Qed.

Lemma eclosed_closed_flatten x : eclosed x -> closed (flatten x).
Proof.
  elim /(induction_ltof1 _ eterm_size) : x.
  move=> [ctx s] /= IH [Hs] Hctx.
  apply /closed_dcl. apply: bound_subst_many; [|by rewrite length_map].
  rewrite map_map.
  apply /all_Forall /Forall_forall => y Hy. apply: IH.
  - rewrite /ltof /=.
    move: Hy => /(@in_split eterm) [?] [?] ->.
    rewrite map_app /= list_sum_app /= term_size_S. lia.
  - move: Hctx => /all_Forall /Forall_forall. by apply.
Qed.

Lemma bound_var_S_iff n x : bound (S n) (var (S x)) <-> bound n (var x).
Proof.
  split; intros H; inversion H; constructor; lia.
Qed.

Lemma traverse_step s t vs : step s t -> step (traverse s vs) (traverse t vs).
Proof.
  elim: vs s t; [done|].
  move=> [[] [xs u]] vs IH s t ?.
  - apply: IH. by apply: stepAppL.
  - apply: IH. by apply: stepAppR.
Qed.

Lemma subst_subst_many s n ts u : all (map closed ts) ->
  subst (subst_many s (S n) ts) n u = subst_many s n (u :: ts).
Proof.
  move=> Hts. elim: s n.
  - move=> x n. rewrite /subst_many.
    have -> : S n = n + 1 by lia.
    rewrite seq_app /= map_app -app_assoc /=.
    suff: forall k, subst (nth x (map var (seq k n) ++ (var (k+n)) :: ts) (var (k + x))) (k+n) u =
      nth x (map var (seq k n) ++ u :: ts) (var (k+x)) by apply.
    elim: n x.
    + move=> [|x] k /=; [by rewrite Nat.eqb_refl|].
      have : k + S x > k by lia.
      elim: ts Hts x (k + S x).
      * move=> _ [|x] ? /=; case Ek: (Nat.eqb _ _); move=> /Nat.eqb_spec in Ek; by [|lia].
      * move=> t ts IH /= [Ht ?] [|x] ??; [by apply: Ht|].
        by apply: IH.
    + move=> n IH [|x] k /=.
      * by case Ek: (Nat.eqb _ _); move=> /Nat.eqb_spec in Ek; [lia|].
      * rewrite -!Nat.add_succ_comm. by apply: IH.
  - move=> s IHs t IHt n /=. by rewrite IHs IHt.
  - move=> s IHs n /=. by rewrite IHs.
Qed.

Lemma flatten_app xs s t : flatten (closure xs (app s t)) = app (flatten (closure xs s)) (flatten (closure xs t)).
Proof. done. Qed.

Lemma flatten_lam xs s : flatten (closure xs (lam s)) = lam (subst_many s 1 (map flatten xs)).
Proof. done. Qed.

Lemma flatten_var xs x : flatten (closure xs (var x)) = nth x (map flatten xs) (var x).
Proof. done. Qed.

#[local] Arguments flatten : simpl never.

Definition eclosed_future v :=
  match v with
  | (true, x) => eclosed x
  | (false, closure xs s) => eclosed (closure xs (lam s))
  end.

Lemma machine_inverse_simulation x vs y : machine x vs y -> eclosed x -> Forall eclosed_future vs ->
  L.eval (traverse (flatten x) vs) (flatten y).
Proof.
  elim; cbn.
  - move=> {}x xs {}vs {}y _ IH.
    move=> [?] [??]. by apply: IH.
  - move=> {}x xs n {}vs {}y _ IH.
    move=> [/bound_var_S_iff] /[dup] /boundE Hxsn ? [? ?].
    rewrite flatten_var.
    rewrite (nth_indep _ _ (var n)). { rewrite length_map. cbn. lia. }
    by apply: IH.
  - move=> xs s t {}vs {}y _ IH.
    move=> [/boundE] [??] ??. by apply: IH; [|constructor].
  - move=> xs s z {}vs {}y _ IH [??] /Forall_cons_iff [??].
    by apply: IH; [|constructor].
  - move=> xss xts s t {}vs {}y _ IH.
    move=> [??] /Forall_cons_iff /= [[/boundE]] ? Hxss ?.
    apply: step_eval. { apply: traverse_step. by apply: stepApp. }
    suff -> : subst (subst_many s 1 (map flatten xss)) 0 (lam (subst_many t 1 (map flatten xts))) =
      subst_many s 0 (lam (subst_many t 1 (map flatten xts)) :: map flatten xss) by apply: IH.
    apply subst_subst_many.
    rewrite map_map. apply: all_map_impl Hxss.
    by apply: eclosed_closed_flatten.
  - move=> {}xs s *. by apply: eval_abs.
Qed.

#[local] Arguments in_split {A x l}. 
#[local] Arguments ltof /.

Lemma flatten_closure_var_S x xs n :
  n < length xs ->
  flatten (closure (x :: xs) (var (S n))) = flatten (closure xs (var n)).
Proof.
  move=> ?.
  rewrite !flatten_var /=.
  apply: nth_indep. by rewrite length_map.
Qed.

Definition flatten_future v :=
  match v with
  | (true, x) => (true, flatten x)
  | (false, closure xs s) => (false, flatten (closure xs (lam s)))
  end.

Lemma machine_var_bound xs x vs y : machine (closure xs (var x)) vs y -> x < length xs.
Proof.
  elim: x xs.
  - move=> [|??] /machineE /=; lia.
  - move=> ? IH [|??] /machineE; [done|].
    move=> /IH /=. lia.
Qed.

Lemma flatten_closure_var_bound xs x : (if flatten (closure xs (var x)) is var _ then False else True) -> x < length xs.
Proof.
  rewrite flatten_var.
  move=> H. suff: not (length xs <= x) by lia.
  move=> ?. by rewrite nth_overflow in H; [rewrite length_map|].
Qed.

Lemma flatten_eq_var_S {xs s x' x's x} :
  flatten (closure xs s) = flatten (closure (x' :: x's) (var (S x))) ->
  if s is var _ then True else flatten (closure xs s) = flatten (closure x's (var x)).
Proof.
  move=> H.
  have := @flatten_closure_var_bound (x' :: x's) (S x).
  rewrite -H [in _ = _]H.
  move: s {H} => [] /=.
  - done.
  - move=> ?? /(_ Logic.I) ?. by rewrite flatten_closure_var_S; [lia|].
  - move=> ? /(_ Logic.I) ?. by rewrite flatten_closure_var_S; [lia|].
Qed.

Lemma eclosed_app xs s t : eclosed (closure xs (app s t)) -> eclosed (closure xs s) /\ eclosed (closure xs t).
Proof.
  move=> /= [/boundE]. tauto.
Qed.

Lemma eclosed_var_0 x xs : eclosed (closure (x :: xs) (var 0)) -> eclosed x.
Proof.
  by move=> [?] [?].
Qed.

Lemma eclosed_var_S x xs n : eclosed (closure (x :: xs) (var (S n))) -> eclosed (closure xs (var n)).
Proof.
  by move=> /= [/bound_var_S_iff ?] [??].
Qed.

(* machine is invariant closure flattening *)
Lemma machine_flatten_equiv {x1 vs1 y1 x2 vs2} :
  machine x1 vs1 y1 ->
  eclosed x1 ->
  eclosed x2 ->
  Forall eclosed_future vs1 ->
  Forall eclosed_future vs2 ->
  map flatten_future vs1 = map flatten_future vs2 ->
  flatten x1 = flatten x2 ->
  exists y2, flatten y1 = flatten y2 /\ machine x2 vs2 y2.
Proof.
  have H' : forall y1 (P Q : eterm -> Prop), (forall y2, P y2 -> Q y2) ->
    (exists y2 : eterm, flatten y1 = flatten y2 /\ P y2) ->
    (exists y2 : eterm, flatten y1 = flatten y2 /\ Q y2).
  { move=> > ? [y2] [??]. exists y2. firstorder done. }
  move=> H. elim: H x2 vs2.
  - move=> {}x1 xs1 {}vs1 {}y1 ? IH x2 vs2 /= [? [??]] ???. by apply: IH.
  - move=> {}x1 xs1 n1 {}vs1 {}y1 /machine_var_bound ? IH x2 vs2.
    rewrite flatten_closure_var_S. { done. }
    move=> /= [/bound_var_S_iff ? [??]].
    move=> /IH /[apply] /[apply] /[apply] /[apply]. by apply.
  - move=> xs1 s1 t1 {}vs1 {}y1 ? IH [xs2 u] vs2 Hs1t1 Hu Hvs1 Hvs2 ?.
    elim /(@induction_ltof1 _ context_size): xs2 u Hu.
    move=> xs2 IH2 [].
    + move=> [|x2].
      * move: xs2 IH2 => [|[? ?] ?]; [done|].
        move=> IH2 /eclosed_var_0 ?. rewrite flatten_var /=.
        move=> /IH2.
        apply: unnest. { rewrite /context_size /= term_size_S. lia. }
        apply: unnest. { done. }
        apply: H' => y2 ?. by apply: machine_var_0.
      * move: xs2 IH2 => [|[? ?] ?]; [done|].
        move=> IH2 /eclosed_var_S ? /flatten_eq_var_S /IH2.
        apply: unnest. { cbn. rewrite /list_sum term_size_S. lia. }
        apply: unnest. { done. }
        apply: H' => y2 ?. by apply: machine_var_S.
    + move=> s2 t2. move: Hs1t1. rewrite !flatten_app.
      move=> /eclosed_app [??] /eclosed_app [??].
      move=> [+ ?] => /IH => /(_ ((true, closure xs2 t2) :: vs2)).
      apply: unnest. { done. }
      apply: unnest. { done. }
      apply: unnest. { by constructor. }
      apply: unnest. { by constructor. }
      apply: unnest. { cbn. by congruence. }
      move=> [y2] [? ?]. exists y2. split; [done|].
      by apply: machine_app.
    + done.
  - move=> xs1 s1 z1 {}vs1 {}y1 ? IH [xs2 u] vs2 Hs1 Hu Hvs1 Hvs2 Hvs.
    elim /(@induction_ltof1 _ context_size): xs2 u Hu.
    move=> xs2 IH2 [].
    + move=> [|x2].
      * move: xs2 IH2 => [|[? ?] ?]; [done|].
        move=> IH2 /eclosed_var_0 ?. rewrite flatten_var /=.
        move=> /IH2.
        apply: unnest. { rewrite /context_size /= term_size_S. lia. }
        apply: unnest. { done. }
        apply: H' => y2 ?. by apply: machine_var_0.
      * move: xs2 IH2 => [|[? ?] ?]; [done|].
        move=> IH2 /eclosed_var_S ? /flatten_eq_var_S /IH2.
        apply: unnest. { cbn. rewrite /list_sum term_size_S. lia. }
        apply: unnest. { done. }
        apply: H' => y2 ?. by apply: machine_var_S.
    + done.
    + move=> s2. move: Hvs1 => /Forall_cons_iff [Hz1 Hvs1].
      move: vs2 Hvs Hvs2 {IH2} => [|[[] [xss2 t2]]vs2]; [done| |done].
      move=> /= /cons_inj [] /pair_equal_spec [_] + ? /Forall_cons_iff [??] ? Hs.
      move=> /IH => /(_ ((false, closure xs2 s2) :: vs2)).
      apply: unnest. { done. }
      apply: unnest. { done. }
      apply: unnest. { by constructor. }
      apply: unnest. { by constructor. }
      apply: unnest. { cbn. by congruence. }
      apply: H' => y2 ?. by apply: machine_lam_swap.
  - move=> xss1 xts1 s1 t1 {}vs1 {}y1 ? IH [xs2 u] vs2 Ht1 Hu Hvs1 Hvs2 Hvs.
    elim /(@induction_ltof1 _ context_size): xs2 u Hu.
    move=> xs2 IH2 [].
    + move=> [|x2].
      * move: xs2 IH2 => [|[? ?] ?]; [done|].
        move=> IH2 /eclosed_var_0 ?. rewrite flatten_var /=.
        move=> /IH2.
        apply: unnest. { rewrite /context_size /= term_size_S. lia. }
        apply: unnest. { done. }
        apply: H' => y2 ?. by apply: machine_var_0.
      * move: xs2 IH2 => [|[? ?] ?]; [done|].
        move=> IH2 /eclosed_var_S ? /flatten_eq_var_S /IH2.
        apply: unnest. { cbn. rewrite /list_sum term_size_S. lia. }
        apply: unnest. { done. }
        apply: H' => y2 ?. by apply: machine_var_S.
    + done.
    + move=> t2 /= ?. move: Hvs1 => /= /Forall_cons_iff [Hs1 Hvs1].
      move: vs2 Hvs Hvs2 {IH2} => [|[[] [xss2 s2]]vs2]; [done|done|].
      move=> /= /cons_inj [] /pair_equal_spec [_] Hs.
      move=> + /Forall_cons_iff [] /= [/boundE ? Hxss2] ? Ht.
      move=> /(IH (closure (closure xs2 (lam t2) :: xss2) s2)).
      apply: unnest. { move: Ht1 Hs1 => /= [??] [/boundE ??]. tauto. }
      apply: unnest. { cbn. tauto. }
      apply: unnest. { done. }
      apply: unnest. { done. }
      apply: unnest.
      { move: (Hs). rewrite /flatten -/flatten /= Ht.
        move=> [].
        rewrite -subst_subst_many.
        { move: Hs1 => /= [?]. rewrite map_map.
          apply: all_map_impl. by apply: eclosed_closed_flatten. }
        rewrite -subst_subst_many.
        { move: Hxss2. rewrite map_map.
          apply: all_map_impl. by apply: eclosed_closed_flatten. }
        by move=> ->. }
      apply: H' => y2 ?. by apply: machine_lam_subst.
  - move=> xs1 s1 [xs2 u] [|??]; [|done].
    move=> _ _ _ _ _.
    elim /(@induction_ltof1 _ context_size): xs2 u.
    move=> xts2 IH2 [].
    + move=> [|x2].
      * move: xts2 IH2 => [|[? ?] ?]; [done|].
        move=> IH2. rewrite flatten_var /=.
        move=> /IH2. apply: unnest. { rewrite /context_size /= term_size_S. lia. }
        apply: H' => y2 ?. by apply: machine_var_0.
      * move: xts2 IH2 => [|[? ?] ?]; [done|].
        move=> IH2 /flatten_eq_var_S /IH2.
        apply: unnest. { cbn. rewrite /list_sum term_size_S. lia. }
        apply: H' => y2 ?. by apply: machine_var_S.
    + done.
    + move=> s2 ?. eexists. split; [eassumption|].
      by apply: machine_lam.
Qed.

(* reduces rhs only if lhs is already lam *)
Inductive step' : term -> term -> Prop :=
  | step'App  s t     : step' (app (lam s) (lam t)) (subst s 0 (lam t))
  | step'AppR s t  t' : step' t t' -> step' (app (lam s) t) (app (lam s) t')
  | step'AppL s s' t  : step' s s' -> step' (app s t) (app s' t).

Lemma subst_many_nil s n : subst_many s n [] = s.
Proof.
  elim: s n.
  - move=> x n /=. rewrite app_nil_r map_nth. congr var.
    have [?|?] : x < n \/ n <= x by lia.
    + by apply seq_nth.
    + apply nth_overflow. by rewrite length_seq.
  - by move=> /= ? + ? + ? => -> ->.
  - by move=> /= ? + ? => ->.
Qed.

Lemma flatten_term s : flatten (closure [] s) = s.
Proof.
  by apply subst_many_nil.
Qed.

Lemma subst_subst_many_single s n t : subst s n t = subst_many s n [t].
Proof.
  elim: s n.
  - move=> x n /=.
    have [?|[->|Hxn]] : x < n \/ x = n \/ (x - n = S (x - n - 1)) by lia.
    + rewrite app_nth1. { by rewrite length_map length_seq. }
      rewrite map_nth seq_nth. { done. }
      case E: (Nat.eqb _ _); move=> /Nat.eqb_spec in E; [lia|done].
    + rewrite Nat.eqb_refl. by rewrite app_nth2 length_map length_seq ?Nat.sub_diag.
    + case E: (Nat.eqb _ _); move=> /Nat.eqb_spec in E; [lia|].
      rewrite app_nth2 length_map length_seq. { lia. }
      rewrite Hxn /=. by case: (x - n - 1).
  - by move=> ? + ? + ? /= => -> ->.
  - by move=> ? + ? /= => ->.
Qed.

Lemma step'_machine s t vs y : step' s t -> closed s -> Forall eclosed_future vs ->
  machine (closure [] t) vs y -> exists y', flatten y' = flatten y /\ machine (closure [] s) vs y'.
Proof.
  move=> H. elim: H vs y.
  - move=> {}s {}t vs y /closed_app [/closed_dcl /boundE Hs /closed_dcl Ht] Hvs IH.
    have : flatten (closure [] (subst s 0 (lam t))) = flatten (closure [closure [] (lam t)] s).
    { rewrite /flatten -/flatten /= !flatten_term subst_many_nil. by apply: subst_subst_many_single. }
    move: IH => /machine_flatten_equiv /[apply] => /(_ vs).
    apply: unnest. { by split; [apply: closed_subst|]. }
    apply: unnest. { done. }
    move=> /(_ Hvs Hvs erefl) [y' [? ?]].
    exists y'. split; [done|].
    apply: machine_app.
    apply: machine_lam_swap.
    by apply: machine_lam_subst.
  - move=> {}s {}t u ? IH vs y /closed_app [Hs Ht] Hvs.
    move=> /machineE /machineE /(IH _ y Ht).
    apply: unnest. { constructor; [|done]. by split; [apply /closed_dcl|]. }
    move=> [y'] [??].
    exists y'. split; [done|].
    apply: machine_app. by apply: machine_lam_swap.
  - move=> {}s {}t u ? IH vs y /closed_app [Hs ?] Hvs.
    move=> /machineE /(IH _ y Hs).
    apply: unnest. { constructor; [|done]. by split; [apply /closed_dcl|]. }
    move=> [y'] [??].
    exists y'. by split; [|apply: machine_app].
Qed.

#[local] Notation steps' := (clos_refl_trans term step').

Lemma steps'AppL {s s' t} : steps' s s' -> steps' (app s t) (app s' t).
Proof.
  elim.
  - move=> *. apply: rt_step. by apply: step'AppL.
  - move=> *. by apply: rt_refl.
  - move=> *. by apply: rt_trans; eassumption.
Qed.

Lemma steps'AppR {s t t'} : steps' t t' -> steps' (app (lam s) t) (app (lam s) t').
Proof.
  elim.
  - move=> *. apply: rt_step. by apply: step'AppR.
  - move=> *. by apply: rt_refl.
  - move=> *. by apply: rt_trans; eassumption.
Qed.

Lemma eval_is_lam s t : L.eval s t -> exists t', t = lam t'.
Proof.
  by elim => *; [eexists|].
Qed.

Lemma eval_steps' s t : L.eval s t -> steps' s t.
Proof.
  elim. { move=> ?. by apply: rt_refl. }
  move=> {}s s' {}t t' u' _ Hss' /eval_is_lam [t''] -> Htt' _ H.
  apply: rt_trans; [|eassumption].
  apply: rt_trans. { by apply: (steps'AppL Hss'). }
  apply: rt_trans. { by apply: (steps'AppR Htt'). }
  apply: rt_step. by apply: step'App.
Qed.

Lemma step_step' s t : step' s t -> step s t.
Proof.
  elim; by auto using step with nocore.
Qed.

Lemma step'_closed s t : step' s t -> closed s -> closed t.
Proof.
  by move=> /step_step' /closed_step.
Qed.

Lemma machine_simulation {s t} : L.eval s t -> closed s ->
  exists y, flatten y = t /\ machine (closure [] s) [] y.
Proof.
  move=> /[dup] + /eval_is_lam [t'].
  move=> /eval_steps' /clos_rt_rt1n_iff. elim.
  { move=> ? -> ?. eexists. by split; [apply flatten_term|apply machine_lam]. }
  move=> {}s u {}t /[dup] /step'_machine Hsu /step'_closed H'su _ /[apply].
  move=> + /[dup] /H'su => /[apply] - [y] [<-].
  move=> /Hsu /[apply]. by apply.
Qed.

(*
  A closed L-term s evaluates to a term t iff
  machine relates s with some y such that flatten y = t
*)
Theorem machine_correctness {s t} : closed s -> (L.eval s t) <-> 
  (exists y, flatten y = t /\ machine (closure [] s) [] y).
Proof.
  move=> Hs. split.
  - move=> /machine_simulation. by apply.
  - move=> [?] [+] /machine_inverse_simulation.
    move=> ->. rewrite flatten_term.
    move=> /closed_dcl in Hs. by apply.
Qed.
