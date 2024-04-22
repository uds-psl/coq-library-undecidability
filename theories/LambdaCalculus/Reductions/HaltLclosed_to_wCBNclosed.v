(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  Reduction from:
    L halting for closed terms (HaltLclosed)
  to:
    Weak call-by-name leftmost outermost normalization of closed lambda-terms (wCBNclosed)

  Related Work:
  [1] Plotkin, Gordon.
      "Call-by-name, call-by-value and the λ-calculus."
      Theoretical computer science 1.2 (1975): 125-159.
*)

From Undecidability.LambdaCalculus Require Import Lambda Util.term_facts Util.wCBN_facts.

From Undecidability Require Import L.Util.L_facts.

From Coq Require Import Relations Wellfounded.Transitive_Closure List Lia.
Import L (term, var, app, lam).
Import Lambda (subst, wCBN_step, wCBN_stepSubst, wCBN_stepApp).
From Coq Require Import ssreflect.

Import Relation_Operators (t1n_trans).
Import Datatypes (id).

Set Default Goal Selector "!".

#[local] Notation step := wCBN_step.

Module Argument.

#[local] Arguments id : simpl never.
#[local] Arguments clos_refl_trans {A}.
#[local] Arguments clos_trans {A}.
#[local] Unset Implicit Arguments.

Lemma t_trans' {A : Type} {R : relation A} {x x' y z : A} : 
  x = x' -> clos_trans R x y -> clos_trans R y z -> clos_trans R x' z.
Proof. move=> ->. by apply: t_trans. Qed.

Lemma clos_t_rt s t : clos_trans step s t -> clos_refl_trans step s t.
Proof. elim; eauto using @clos_refl_trans. Qed.

Lemma closed_eval {s t} : L.eval s t -> closed s -> closed t.
Proof. by move=> /eval_iff [/closed_star]. Qed.

(* call-by-value to call-by-name continuation translation *)
Fixpoint cbv_cbn (t : term) : term :=
  match t with
  | var n => lam (app (var 0) (var (S n)))
  | app s t => lam (app (ren S (cbv_cbn s)) (lam (app (ren S (ren S (cbv_cbn t))) (lam (app (app (var 1) (var 0)) (var 2))))))
  | lam s => lam (app (var 0) (ren S (lam (cbv_cbn s))))
  end.

Definition Psi (t : term) :=
  match t with
  | var n => var n
  | app s t => app s t
  | lam s => lam (cbv_cbn s)
  end.

Lemma cbv_cbn_ren xi s : cbv_cbn (ren xi s) = ren xi (cbv_cbn s).
Proof.
  elim: s xi.
  - done.
  - move=> ? IH1 ? IH2 xi /=. by rewrite IH1 IH2 !simpl_term.
  - move=> ? IH xi /=. rewrite IH !simpl_term.
    congr lam. congr app. congr lam.
    apply: ext_ren_term. by case.
Qed.

Lemma cbv_cbn_subst sigma s :
  (forall n, match sigma n with | app _ _ => False | _ => True end) ->
  cbv_cbn (subst sigma s) = subst (funcomp Psi sigma) (cbv_cbn s).
Proof.
  elim: s sigma.
  - move=> n sigma Hsigma /=.
    have := Hsigma n. by case: (sigma n).
  - move=> s IH1 t IH2 sigma Hsigma /=.
    rewrite (IH1 _ Hsigma) (IH2 _ Hsigma) /=.
    rewrite !simpl_term /=.
    congr lam. congr app. congr lam. congr app.
    apply: ext_subst_term => ? /=. by rewrite !simpl_term.
  - move=> s IH sigma Hsigma /=. rewrite IH.
    { move=> [|n] /=; first done.
      have := Hsigma n. by case: (sigma n). }
    rewrite !simpl_term.
    congr lam. congr app. congr lam.
    apply: ext_subst_term => - [|n] /=; first done.
    have := Hsigma n. case: (sigma n); [done|done|].
    move=> s' /= _. rewrite !cbv_cbn_ren.
    congr lam. rewrite !simpl_term.
    apply: ext_ren_term. by case.
Qed.

(* (colon s u) is Plotkin's (s : k) operator *)
Fixpoint colon s u :=
  match s with
  | var n => var n
  | lam _ => app u (Psi s)
  | app s t =>
      match s with
      | var n => var n
      | app s1 s2 => (id colon) s (lam (app (ren S (cbv_cbn t)) (lam (app (app (var 1) (var 0)) (ren S (ren S u))))))
      | lam _ => colon t (lam (app (app (ren S (Psi s)) (var 0)) (ren S u)))
      end
  end.

(* non-capturing leftmost outermost cbv step relation *)
Inductive cbv_step : term -> term -> Prop :=
  | cbv_step_lam s t : cbv_step (app (lam s) (lam t)) (subst (scons (lam t) var) s)
  | cbv_step_appL s s' t : cbv_step s s' -> cbv_step (app s t) (app s' t)
  | cbv_step_appR s t t' : cbv_step t t' -> cbv_step (app (lam s) t) (app (lam s) t').

Lemma cbv_steps_appL {s s' t} :
  clos_refl_trans cbv_step s s' -> clos_refl_trans cbv_step (app s t) (app s' t).
Proof. elim; by eauto using @clos_refl_trans, cbv_step with nocore. Qed.

Lemma cbv_steps_appR {s t t'} :
  clos_refl_trans cbv_step t t' -> clos_refl_trans cbv_step (app (lam s) t) (app (lam s) t').
Proof. elim; by eauto using @clos_refl_trans, cbv_step with nocore. Qed.

Lemma eval_cbv_steps s t : L.eval s t -> closed s -> clos_refl_trans cbv_step s t.
Proof.
  elim; clear s t. { move=> *. by apply: rt_refl. }
  move=> s u t t' v Hsu IH1 Htt' IH2 Hv IH3 /closed_app [Hs Ht].
  move: (Hs) => /IH1 => - {}IH1. move: (Ht) => /IH2 => - {}IH2.
  have Ht' : closed t' by (apply: closed_eval; eassumption).
  have Hu : bound 1 u.
  { by have /closed_dcl /boundE := closed_eval Hsu Hs. } 
  have /IH3 {}IH3 : closed (L.subst u 0 t').
  { apply /closed_dcl. apply: closed_subst; [done|by apply /closed_dcl]. }
  move: IH3.
  have -> : L.subst u 0 t' = subst (scons t' var) u.
  { rewrite L_subst_Lambda_subst; first done.
    apply: (bound_ext_subst_term Hu).
    move=> [|n]; [done|lia]. }
  move=> {}IH3.
  apply: rt_trans. { apply: cbv_steps_appL. eassumption. }
  apply: rt_trans. { apply: cbv_steps_appR. eassumption. }
  apply: rt_trans; last by eassumption.
  move: Htt' => /eval_iff [_] [? ->].
  apply: rt_step. by apply: cbv_step_lam.
Qed.

Lemma bound_cbv_cbn k t : bound k t -> bound k (cbv_cbn t).
Proof.
  elim.
  - move=> *. do 3 constructor; lia.
  - move=> * /=. do 2 constructor.
    + by apply: bound_ren; [eassumption|lia].
    + do 2 constructor.
      * rewrite !simpl_term /=. apply: bound_ren; [eassumption|lia].
      * do 2 constructor; [constructor|]; constructor; lia.
  - move=> * /=. do 3 constructor; first by lia.
    apply: bound_ren; [eassumption|].
    move=> [|n] /=; lia.
Qed.

Lemma cbv_step_closed {s s'} : cbv_step s s' -> closed s -> closed s'.
Proof.
  elim.
  - move=> > /closed_app [/closed_dcl /boundE ?] /closed_dcl ?.
    apply /closed_dcl. apply: bound_subst; first by eassumption.
    move=> [|n]; [done|lia].
  - move=> > ? H /closed_app [/H ? ?]. by apply: app_closed.
  - move=> > ? H /closed_app [? /H ?]. by apply: app_closed; [|].
Qed.

Lemma cbv_steps_closed {s s'} : clos_refl_trans cbv_step s s' -> closed s -> closed s'.
Proof. elim; by  eauto using cbv_step_closed. Qed.

Lemma cbv_step_L_step s s' : cbv_step s s' -> closed s -> L_facts.step s s'.
Proof.
  elim; clear s s'.
  - move=> s s' /closed_app [/closed_dcl /boundE ?] /closed_dcl ?.
    have := L_facts.stepApp s s'. congr L_facts.step.
    rewrite L_subst_Lambda_subst. { by apply /closed_dcl. }
    apply: bound_ext_subst_term; first by eassumption.
    move=> [|n]; [done|lia].
  - move=> > ? H /closed_app [/H ? ?]. by apply: stepAppL.
  - move=> > ? H /closed_app [? /H ?]. by apply: stepAppR.
Qed.

Lemma steps_to_colon s u : closed s -> clos_trans step (app (cbv_cbn s) u) (colon s u).
Proof.
  elim: s u.
  - by move=> > /not_closed_var.
  - move=> s IH1 t IH2 u /= /closed_app [/[dup] Hs /IH1 {}IH1 /IH2 {}IH2].
    have {}IH1 := IH1 (lam (app (ren S (cbv_cbn t)) (lam (app (app (var 1) (var 0)) (ren S (ren S u)))))).
    have {}IH2 := IH2 (lam (app (app (ren S (Psi s)) (var 0)) (ren S u))).
    move: (s) Hs IH1 IH2 => [].
    + by move=> > /not_closed_var.
    + move=> s1 s2 _. move: (app s1 s2) => s' IH1 IH2.
      apply: t_trans. { apply: t_step. by apply: wCBN_stepSubst. }
      move: IH1. by rewrite /= !simpl_term !ren_as_subst_term.
    + move=> s' _ IH1 IH2.
      apply: t_trans. { apply: t_step. by apply: wCBN_stepSubst. }
      move: IH1 => /t_trans'. apply.
      { rewrite /= !simpl_term !ren_as_subst_term. congr app.
        congr lam. congr app. congr lam. apply: ext_subst_term. by case. }
      apply: t_trans. { apply: t_step. by apply: wCBN_stepSubst. }
      move: IH2. by rewrite /= !simpl_term !ren_as_subst_term.
  - move=> s IH u ?.
    apply: t_step. rewrite /=. apply: stepLam'.
    rewrite /= !simpl_term /=. congr app. congr lam.
    rewrite -[LHS]subst_var_term. apply: ext_subst_term. by case.
Qed.

Lemma colon_redex s t u : closed (lam s) -> closed (lam t) ->
  clos_trans step (colon (app (lam s) (lam t)) u) (colon (subst (scons (lam t) var) s) u).
Proof.
  move=> /= Hs Ht.
  apply: t_trans. { apply: t_step. by apply: wCBN_stepSubst. } rewrite /=.
  apply: t_trans. { apply: t_step. apply: wCBN_stepApp. by apply: wCBN_stepSubst. }
  have /(steps_to_colon _ u) : closed (subst (scons (lam t) var) s).
  { move: Hs Ht => /closed_dcl /boundE ? /closed_dcl ?.
    apply /closed_dcl. apply: bound_subst; first by eassumption.
    move=> [|n]; [done|lia]. }
  rewrite !simpl_term /= cbv_cbn_subst. { by case. }
  congr clos_trans. congr app. apply: ext_subst_term. by case.
Qed.

Lemma cbv_step_to_lam s1 s2 t : cbv_step (app s1 s2) (lam t) ->
  exists s1' s2', s1 = lam s1' /\ s2 = lam s2' /\ lam t = subst (scons (lam s2') var) s1'.
Proof.
  move Es': (app s1 s2) => s'. move Et': (lam t) => t' Hs't'.
  elim: Hs't' s1 s2 t Es' Et'; [|done|done].
  move=> > [? ?] ?. do 2 eexists. by split; [eassumption|split; [eassumption|]].
Qed.

Lemma simulate_cbv_step s s' : cbv_step s s' -> closed s ->
  forall x, clos_trans step (colon s x) (colon s' x).
Proof.
  elim; clear s s'.
  - move=> s t /closed_app [? ?]. move=> ?. by apply: colon_redex.
  - move=> s s' t Hss' IH /closed_app [/[dup] /IH {}IH Hs Ht].
    have [s1 [s2 ?]] : exists s1 s2, s = app s1 s2.
    { by case: Hss' => *; eexists; eexists. }
    subst s. rewrite /=.
    move: s' IH Hss' => [].
    + by move=> ? ? /cbv_step_closed /(_ Hs) /not_closed_var.
    + move=> s'1 s'2 IH Hss' x. by apply: IH.
    + move=> s' IH /cbv_step_to_lam [s1'] [s2'] [? [? Hs']].
      move=> x. subst.
      apply: t_trans. { by apply: IH. }
      apply: t_trans. { apply: t_step.  by apply: wCBN_stepSubst. }
      have := steps_to_colon t (lam (app (app (ren S (Psi (lam s'))) # 0) (ren S x))) Ht.
      by rewrite /= !simpl_term !ren_as_subst_term.
  - move=> > ? IH /closed_app [? /IH] {}IH x.
    by apply: IH.
Qed.

(* cbv simulation lemma for closed terms *)
Lemma simulation {s t} : L.eval s t -> closed s ->
  forall x, clos_refl_trans step (colon s x) (colon t x).
Proof.
  move=> /eval_cbv_steps + /[dup] => /[apply].
  elim.
  - move=> > /simulate_cbv_step /[apply] H x.
    by apply: clos_t_rt.
  - move=> *. by apply: rt_refl.
  - move=> *. apply: rt_trans; by eauto using cbv_steps_closed.
Qed.

Lemma terminating_Acc s t : clos_refl_trans step s (lam t) -> Acc (fun t' s' => step s' t') s.
Proof.
  move Et': (lam t) => t' /(clos_rt_rt1n term) Hst'.
  elim: Hst' t Et'.
  { move=> ?? <-. by constructor => ? /stepE. }
  move=> x y z Hxy Hyz IH t ?. constructor => y'.
  move: Hxy => /step_fun /[apply] <-. apply: IH. by eassumption.
Qed.

Lemma cbv_step_lam_or_progress {s} : closed s -> (exists s', s = lam s') \/ (exists t, cbv_step s t).
Proof.
  elim: s.
  - by move=> ? /not_closed_var.
  - move=> s IHs t IHt /closed_app [/IHs {}IHs /IHt {}IHt]. right.
    case: IHs; case: IHt.
    + move=> [? ->] [? ->]. eexists. by apply: cbv_step_lam.
    + move=> [? ?] [? ->]. eexists. apply: cbv_step_appR. by eassumption.
    + move=> [? ->] [? ?]. eexists. apply: cbv_step_appL. by eassumption.
    + move=> [? ?] [? ?]. eexists. apply: cbv_step_appL. by eassumption.
  - move=> *. left. by eexists.
Qed.

Lemma clos_trans_swap s t : clos_trans step s t -> clos_trans (fun t' s' => step s' t') t s.
Proof. elim; by eauto using @clos_trans with nocore. Qed.

Lemma inverse_simulation s t :
  clos_refl_trans step (colon s (lam (var 0))) (lam t) -> closed s ->
  exists t', eval s t'.
Proof.
  move=> /terminating_Acc /(Acc_clos_trans term).
  move Es': (colon s (lam (var 0))) => s' Hs'.
  elim: Hs' s Es' => {}s' _ IH s ? Hs. subst s'.
  suff : exists t', star L_facts.step s (lam t').
  { move=> [t' ?]. by exists (lam t'). }
  case: (cbv_step_lam_or_progress Hs).
  { move=> [t' ->]. exists t'. by apply: starR. }
  move=> [s'] /[dup] /cbv_step_L_step /(_ Hs) H0s.
  move=> /[dup] /simulate_cbv_step /(_ Hs (lam (var 0))) /clos_trans_swap /IH H1s.
  move=> /cbv_step_closed /(_ Hs) /H1s => /(_ eq_refl) [? [Hs't']] [t' ?].
  subst. exists t'. by apply: starC; eassumption.
Qed.

Lemma bound_colon {n s u} : bound n s -> bound n u -> bound n (colon s u).
Proof.
  move=> H. elim: H u.
  - move=> * /=. by constructor.
  - move=> ? [?|??|?] ? IH'1 IH1 ? IH2 ??.
    + done.
    + move=> /=. apply: IH1. do 2 constructor.
      * apply: bound_ren; [apply: bound_cbv_cbn; eassumption|lia].
      * do 2 constructor; [do 2 constructor|]; [lia ..|].
        rewrite simpl_term /=.
        apply: bound_ren; [eassumption|lia].
    + move=> /=. apply: IH2. do 2 constructor.
      * do 2 constructor; [|lia].
        move=> /boundE in IH'1.
        apply: bound_ren; [apply: bound_cbv_cbn; eassumption|].
        move=> [|?] /=; lia.
      * apply: bound_ren; [eassumption|lia].
  - move=> * /=. constructor; [done|constructor].
    by apply: bound_cbv_cbn.
Qed.

Lemma closed_colon {s} : closed s -> forall sigma, subst sigma (colon s (lam (var 0))) = colon s (lam (var 0)).
Proof.
  move=> Hs sigma. rewrite subst_L_closed; last done.
  by apply /closed_dcl /bound_colon; apply /closed_dcl.
Qed.

End Argument.

Require Import Undecidability.Synthetic.Definitions.
Require Undecidability.L.Reductions.HaltL_to_HaltLclosed.
Import HaltL_to_HaltLclosed (HaltLclosed).

#[local] Unset Asymmetric Patterns.

(* reduction from L halting to weak call-by-name leftmost outermost normalization *)
(* note: currently HaltLclosed is defined in HaltL_to_HaltLclosed *)
Theorem reduction : HaltLclosed ⪯ wCBNclosed.
Proof.
  exists (fun '(exist _ s Hs) => exist _ (Argument.colon s (lam (var 0))) (Argument.closed_colon Hs)).
  move=> [s Hs]. split.
  - move=> [t] /= /[dup] [[_ []]] t' ->.
    move=> /eval_iff /= /Argument.simulation.
    move=> /(_ Hs (lam (var 0))) ?. exists (Argument.cbv_cbn t').
    apply: rt_trans; first by eassumption.
    apply: rt_step. by apply: wCBN_stepSubst.
  - move=> [t] /Argument.inverse_simulation. by apply.
Qed.
