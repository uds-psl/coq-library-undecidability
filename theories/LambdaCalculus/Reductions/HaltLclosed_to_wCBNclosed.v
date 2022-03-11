(*
  Autor(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  Reduction from:
    L halting for closed terms (HaltLclosed)
  to:
    Weak call-by-name leftmost outermost normalization of closed terms (wCBNclosed)

  Related Work:
  [1] Plotkin, Gordon.
      "Call-by-name, call-by-value and the λ-calculus."
      Theoretical computer science 1.2 (1975): 125-159.
*)

From Undecidability.LambdaCalculus Require Import wCBN Util.term_facts Util.wCBN_facts.

From Undecidability Require Import L.Util.L_facts.

From Coq Require Import Relations List Lia.
Import L (term, var, app, lam).
Import wCBN (subst, step, stepLam, stepApp).
From Coq Require Import ssreflect ssrbool ssrfun.

Import Relation_Operators (t1n_trans).
Import Datatypes (id).

Set Default Goal Selector "!".

Module Argument.

#[local] Arguments id : simpl never.
#[local] Arguments clos_refl_trans {A}.
#[local] Arguments clos_trans {A}.
#[local] Unset Implicit Arguments.

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
  { rewrite L_subst_wCBN_subst; first done.
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
  elim: t k.
  - move=> n k /boundE H. rewrite /cbv_cbn. apply: dcllam.
    apply: dclApp; apply: dclvar; lia.
  - move=> ? IH1 ? IH2 k /boundE [/IH1 {}IH1 /IH2 {}IH2] /=.
    apply: dcllam. apply: dclApp.
    + apply: (bound_ren IH1). lia.
    + apply: dcllam. apply: dclApp.
      * rewrite !simpl_term /=. apply: (bound_ren IH2). lia.
      * apply: dcllam. apply: dclApp; [apply: dclApp|]; apply: dclvar; lia.
  - move=> ? IH k /boundE /IH {}IH /=.
    apply: dcllam. apply: dclApp; [apply: dclvar; lia|].
    apply: dcllam. apply: (bound_ren IH).
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
    rewrite L_subst_wCBN_subst. { by apply /closed_dcl. }
    apply: bound_ext_subst_term; first by eassumption.
    move=> [|n]; [done|lia].
  - move=> > ? H /closed_app [/H ? ?]. by apply: stepAppL.
  - move=> > ? H /closed_app [? /H ?]. by apply: stepAppR.
Qed.

Lemma cbv_steps_eval s t : clos_refl_trans cbv_step s (lam t) -> closed s -> L.eval s (lam t).
Proof.
  move=> /(clos_rt_rt1n term) Hst Hs. apply /eval_iff. split; last by eexists.
  move: (lam t) Hst Hs => t'. elim.
  - move=> *. by apply: starR.
  - move=> > /[dup] /cbv_step_closed H1 /cbv_step_L_step H2 _ H3.
    by eauto using star with nocore.
Qed.

Lemma t_trans' {A : Type} {R : relation A} {x x' y z : A} : 
  x = x' -> clos_trans R x y -> clos_trans R y z -> clos_trans R x' z.
Proof. move=> ->. by apply: t_trans. Qed.

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
      apply: t_trans. { apply: t_step. by apply: stepLam. }
      move: IH1. by rewrite /= !simpl_term !ren_as_subst_term.
    + move=> s' _ IH1 IH2.
      apply: t_trans. { apply: t_step. by apply: stepLam. }
      move: IH1 => /t_trans'. apply.
      { rewrite /= !simpl_term !ren_as_subst_term. congr app.
        congr lam. congr app. congr lam. apply: ext_subst_term. by case. }
      apply: t_trans. { apply: t_step. by apply: stepLam. }
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
  apply: t_trans. { apply: t_step. by apply: stepLam. } rewrite /=.
  apply: t_trans. { apply: t_step. apply: stepApp. by apply: stepLam. }
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
      apply: t_trans. { apply: t_step.  by apply: stepLam. }
      have := steps_to_colon t (lam (app (app (ren S (Psi (lam s'))) # 0) (ren S x))) Ht.
      by rewrite /= !simpl_term !ren_as_subst_term.
  - move=> > ? IH /closed_app [? /IH] {}IH x.
    by apply: IH.
Qed.

Lemma clos_t_rt s t : clos_trans step s t -> clos_refl_trans step s t.
Proof. elim; eauto using @clos_refl_trans. Qed.

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

Lemma colon_progress s t x : step (colon s x) t -> exists s', s = lam s' \/ cbv_step s s'.
Proof.
  elim: s x t.
  - by move=> > /stepE.
  - move=> [n1|s1 s2|s1] IH1 s3 IH2 x t /=.
    + by move=> /stepE.
    + move=> /IH1 [s'] [|?]; first done.
      eexists. right. apply: cbv_step_appL. by eassumption.
    + move=> /IH2 [s'] [|].
      * move=> ->. eexists. right. by apply: cbv_step_lam.
      * move=> ?. eexists. right. apply: cbv_step_appR. by eassumption.
  - move=> *. eexists. by left.
Qed.

Definition rcomp {X Y Z} (R : X -> Y -> Prop) (S : Y -> Z -> Prop) : X -> Z -> Prop :=
  fun x z => exists y, R x y /\ S y z.

Definition pow X R n : X -> X -> Prop := Nat.iter n (rcomp R) eq.

Lemma clos_refl_trans_pow s t : 
  clos_refl_trans step s t -> exists k, Nat.iter k (rcomp step) eq s t.
Proof.
  move=> /(clos_rt_rt1n term). elim.
  - move=> ?. by exists 0.
  - move=> > ? ? [k Hk]. exists (S k). eexists. by split; [eassumption|].
Qed.

Lemma clos_trans_pow s t : 
  clos_trans step s t -> exists k, Nat.iter (S k) (rcomp step) eq s t.
Proof.
  move=> /(clos_trans_t1n term). elim.
  - move=> *. exists 0. eexists. by split; [eassumption|].
  - move=> > ? ? [k Hk]. exists (S k). eexists. by split; [eassumption|].
Qed.

Lemma iter_step_sub k k' s s' t :
  Nat.iter (S k) (rcomp step) eq s (lam t) ->
  Nat.iter (S k') (rcomp step) eq s s' -> 
  Nat.iter (k - k') (rcomp step) eq s' (lam t).
Proof.
  elim: k k' s s'.
  - rewrite /rcomp /=. move=> k' s s' [u] [/step_fun Hsu ?]. subst u.
    move=> [u] [/Hsu ?]. subst u.
    case: k'; first done.
    by move=> k /= [?] [/stepE].
  - move=> k IH [|k'] s s' /= [u] [/step_fun Hsu] Hu [u'] [/Hsu ?].
    { move=> ?. by subst. }
    subst. move=> /IH. by apply.
Qed.

Lemma not_colon_lam s x t : colon s x = lam t -> False.
Proof.
  elim: s x; [done| |done].
  move=> [?|??|?]; by eauto with nocore.
Qed.

Lemma measure_rect {X : Type} (f : X -> nat) (P : X -> Type) : 
  (forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
  exact: (well_founded_induction_type (Wf_nat.well_founded_lt_compat X f _ (fun _ _ => id)) P).
Qed.

Lemma inverse_simulation s t :
  clos_refl_trans step (colon s (lam (var 0))) (lam t) -> closed s ->
  exists t', eval s t'.
Proof.
  move=> /clos_refl_trans_pow [k] H Hs.
  suff : exists t', star L_facts.step s (lam t').
  { move=> [t' ?]. by exists (lam t'). }
  elim /(measure_rect id): k s t H Hs. rewrite /id.
  move=> [|k] IH s t. { by move=> /not_colon_lam. }
  move=> /[dup] /= - [s'] [/colon_progress] [s''] [].
  { move=> -> *. exists s''. by apply: starR. }
  move=> /[dup] /[dup] /cbv_step_L_step H0s /simulate_cbv_step H1s /cbv_step_closed H2s _.
  move=> HSk /[dup] /H0s {}H0s /[dup] /H1s /(_ (lam (var 0))) {}H1s /H2s {}H2s.
  move: H1s => /clos_trans_pow [k'].
  move: HSk => /iter_step_sub /[apply] /IH.
  move=> /(_ ltac:(lia) H2s) [t'] ?. exists t'.
  by apply: starC; eassumption.
Qed.

Lemma closed_colon {s u} : closed s -> closed u -> closed (colon s u).
Proof.
  elim: s u.
  - by move=> > /not_closed_var.
  - move=> s IH1 t IH2 u /closed_app /= [/[dup] Hs /IH1 {}IH1 /[dup] Ht /IH2 {}IH2] Hu.
    case: s IH1 Hs.
    + by move=> ?? /not_closed_var.
    + move=> > IH1 ?. apply: IH1.
      apply /closed_dcl. do ? constructor.
      * move: Ht => /closed_dcl /bound_cbv_cbn /bound_ren. apply. lia.
      * rewrite !simpl_term. move: Hu => /closed_dcl /bound_ren. apply. lia.
    + move=> ? IH1 /closed_dcl /boundE H' /=.
      apply: IH2. apply /closed_dcl. do ? constructor.
      * move: H' => /bound_cbv_cbn /bound_ren. apply.
        move=> [|?] /=; lia.
      * move: Hu => /closed_dcl /bound_ren. apply. lia.
  - move=> ? _ ? /closed_dcl /boundE /bound_cbv_cbn ? ? /=.
    apply: app_closed; first done.
    apply /closed_dcl. by constructor.
Qed.

Lemma closed'_colon {s} : closed s -> forall sigma, subst sigma (colon s (lam (var 0))) = colon s (lam (var 0)).
Proof.
  move=> Hs sigma. rewrite subst_closed; last done.
  by apply: (closed_colon Hs).
Qed.

End Argument.

Require Import Undecidability.Synthetic.Definitions.
Require Undecidability.TM.Reductions.L_to_mTM.
#[local] Unset Asymmetric Patterns.

(* note: currently HaltLclosed is defined in L_to_mTM *)
Theorem reduction : L_to_mTM.HaltLclosed ⪯ wCBNclosed.
Proof.
  exists (fun '(exist _ s Hs) => exist _ (Argument.colon s (lam (var 0))) (Argument.closed'_colon Hs)).
  move=> [s Hs]. split.
  - move=> [t] /= /[dup] [[_ []]] t' ->.
    move=> /eval_iff /= /Argument.simulation.
    move=> /(_ Hs (lam (var 0))) ?. exists (Argument.cbv_cbn t').
    apply: rt_trans; first by eassumption.
    apply: rt_step. by apply: stepLam.
  - move=> [t] /Argument.inverse_simulation. by apply.
Qed.
