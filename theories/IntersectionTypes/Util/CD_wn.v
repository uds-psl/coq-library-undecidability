(*
  Intersection Type Typability (type_assignment Gamma M t)
  implies Weak Normalization (wn M)
*)

Require Import
  Undecidability.IntersectionTypes.CD
  Undecidability.IntersectionTypes.Util.CD_facts
  Undecidability.IntersectionTypes.Util.CD_fundamental
  Undecidability.LambdaCalculus.Util.term_facts.

From Stdlib Require Import Relations.

Import L (term, var, app, lam).
Import Lambda.

From Stdlib Require Import ssreflect.

Set Default Goal Selector "!".

Module Admissible_wn.

Lemma neutal_wn_wn M : neutral wn M -> wn M.
Proof.
  suff: neutral wn M -> exists N, clos_refl_trans term step M N /\ neutral normal_form N.
  { move=> /[apply] - [N] [??]. exists N; [done|by apply: neutral_normal_form]. }
  elim. { move=> x. exists (var x). by split; [apply: rt_refl|constructor]. }
  move=> {}M N H1M [M'] [HMM' HM'] [N'] HNN' HN'.
  exists (app M' N'). split; [|by constructor].
  apply: (rt_trans _ _ _ (app M' N)).
  - by apply: rt_stepsAppL.
  - by apply: rt_stepsAppR.
Qed.

Lemma head_exp_step M N : head_exp wn M N -> step N M.
Proof.
  elim. { move=> *. by apply: stepSubst. }
  move=> *. by apply: stepAppL.
Qed.

Lemma step_wn M N : step M N -> wn N -> wn M.
Proof.
  move=> ? [???]. econstructor; [|eassumption].
  by apply: rt_trans; [apply: rt_step|]; eassumption.
Qed.

Lemma head_exp_wn M N : head_exp wn M N -> wn M -> wn N.
Proof.
  by move=> /head_exp_step /step_wn.
Qed.

Lemma wn_ren xi M : wn (ren xi M) -> wn M.
Proof.
  case=> N /steps_renE [?] [->] ? /normal_form_ren' /wn_intro. by apply.
Qed.

Lemma wn_lam M : wn M -> wn (lam M).
Proof.
  case=> N HMN ?. apply: (wn_intro (lam N)); [|by constructor].
  elim: HMN; by eauto using clos_refl_trans, step with nocore.
Qed.

Lemma wn_app_var M x : wn (app M (var x)) -> wn M.
Proof.
  case=> N /clos_rt_rt1n_iff.
  move E: (app M (var x)) => M' H. elim: H M E.
  { move=> ?? E H. case: H E; [done|done|..].
    - move=> > ? [] -> _. by econstructor; [apply: rt_refl|constructor].
    - move=> > ?? [] -> _. by econstructor; [apply: rt_refl|]. }
  move=> > [].
  - move=> > IH ?? [??]. subst.
    move: IH. rewrite subst_as_ren.
    by move=> /clos_rt_rt1n_iff /wn_intro /[apply] /wn_ren /wn_lam.
  - move=> > ?? IH ? [??]. subst.
    move: (IH _ eq_refl) => /[apply].
    by apply: step_wn.
  - move=> > H ? IH ? [??]. subst.
    by move=> /stepE in H.
  - done.
Qed.

Lemma Admissible_wn : Admissible wn.
Proof.
  constructor.
  - by apply: head_exp_wn.
  - by apply: neutal_wn_wn.
  - by apply: wn_app_var.
Qed.

End Admissible_wn.

(* consequence of fundamental theorem *)
Lemma weak_normalization {Gamma M t} : type_assignment Gamma M t -> wn M.
Proof.
  apply: fundamental. by apply: Admissible_wn.Admissible_wn.
Qed.
