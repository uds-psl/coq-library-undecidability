From Stdlib Require Import List PeanoNat Lia Relations.
Import ListNotations.

From Undecidability.L Require Import L.

From Undecidability.L Require Util.L_facts Prelim.ARS.
Import L_facts (step).
Require Import Undecidability.Shared.simulation.

From Stdlib Require Import ssreflect.

Unset Implicit Arguments.

Set Default Goal Selector "!".

#[local] Notation lams k M := (Nat.iter k lam M).
#[local] Notation apps M Ns := (fold_left app Ns M).

Lemma subst_apps s k t ts : subst (apps t ts) k s = apps (subst t k s) (map (fun u => subst u k s) ts).
Proof.
  elim: ts t; first done.
  move=> t' ts IH t /=. by rewrite IH.
Qed.

Lemma subst_lams n s k t : subst (lams n s) k t = lams n (subst s (n + k) t).
Proof.
  elim: n k; first done.
  move=> n IH k /=. by rewrite IH Nat.add_succ_r.
Qed.

Fixpoint substs k ts t :=
  match t with
  | var x => nth x (map var (seq 0 k) ++ ts) (var x)
  | app s t => app (substs k ts s) (substs k ts t)
  | lam s => lam (substs (S k) ts s)
  end.

Lemma substs_apps k ts s ss : substs k ts (apps s ss) = apps (substs k ts s) (map (substs k ts) ss).
Proof.
  elim: ss s; first done.
  move=> s' ss IH s /=. by rewrite IH.
Qed.

Lemma substs_nil k t : substs k [] t = t.
Proof.
  elim: t k.
  - move=> x k /=. rewrite app_nil_r map_nth.
    have [?|?] : x < k \/ x >= k by lia.
    + by rewrite seq_nth.
    + by rewrite nth_overflow ?length_seq.
  - move=> ? IH1 ? IH2 ? /=. by rewrite IH1 IH2.
  - move=> ? IH ? /=. by rewrite IH.
Qed.

Lemma substs_closed k ts t : closed t -> substs k ts t = t.
Proof.
  move=> /L_facts.closed_dcl.
  have : 0 <= k by lia.
  move: (0)=> n + H. elim: H k.
  - move=> > ? > ? /=. rewrite app_nth1.
    + rewrite length_map length_seq. lia.
    + by rewrite map_nth seq_nth; [lia|].
  - move=> > ? IH1 ? IH2 * /=.
    by rewrite IH1 ?IH2.
  - move=> > ? IH * /=. by rewrite IH; [lia|].
Qed.

Lemma substs_subst k t ts s : closed t -> Forall closed ts ->
  substs k ts (subst s (k + length ts) t) = substs k (ts ++ [t]) s.
Proof.
  move=> Ht Hts. elim: s k.
  - move=> x k /=.
    move E: (Nat.eqb x (k + length ts)) => [|].
    + move=> /Nat.eqb_eq in E. subst.
      rewrite app_assoc app_nth2 !length_app !length_map !length_seq; [lia|].
      rewrite Nat.sub_diag /=. by apply: substs_closed.
    + move=> /Nat.eqb_neq in E.
      rewrite /= !app_assoc.
      have [?|?] : x < k + length ts \/ x > k + length ts by lia.
      * rewrite (app_nth1 _ [t]); last done.
        by rewrite length_app length_map length_seq.
      * rewrite !nth_overflow; last done.
        all: rewrite !length_app length_map length_seq /=; lia.
  - move=> ? IH1 ? IH2 ? /=. by rewrite IH1 IH2.
  - move=> ? IH ? /=. by rewrite IH.
Qed.

Lemma eval_lam s t : lam s = t -> eval (lam s) t.
Proof.
  move=> <-. by constructor.
Qed.

Lemma t_steps_app_l s t1 t2 : clos_trans term step t1 t2 -> clos_trans term step (app s t1) (app s t2).
Proof.
  elim.
  - move=> > ?. apply: t_step. by apply: L_facts.stepAppR.
  - move=> *. apply: t_trans; by eassumption.
Qed.

Lemma t_steps_app_r s1 s2 t : clos_trans term step s1 s2 -> clos_trans term step (app s1 t) (app s2 t).
Proof.
  elim.
  - move=> > ?. apply: t_step. by apply: L_facts.stepAppL.
  - move=> *. apply: t_trans; by eassumption.
Qed.

Lemma rt_steps_app_l s t1 t2 : clos_refl_trans term step t1 t2 -> clos_refl_trans term step (app s t1) (app s t2).
Proof.
  elim.
  - move=> > ?. apply: rt_step. by apply: L_facts.stepAppR.
  - move=> *. by apply: rt_refl.
  - move=> *. apply: rt_trans; by eassumption.
Qed.

Lemma rt_steps_app_r s1 s2 t : clos_refl_trans term step s1 s2 -> clos_refl_trans term step (app s1 t) (app s2 t).
Proof.
  elim.
  - move=> > ?. apply: rt_step. by apply: L_facts.stepAppL.
  - move=> *. by apply: rt_refl.
  - move=> *. apply: rt_trans; by eassumption.
Qed.

Lemma rt_steps_apps_r s ts t :
  clos_refl_trans _ step s t -> clos_refl_trans _ step (apps s ts) (apps t ts).
Proof.
  elim: ts s t; first done.
  move=> ?? IH ??? /=. apply: IH.
  by apply: rt_steps_app_r.
Qed.

Lemma step_app' s t : eval t t -> step (app (lam s) t) (subst s 0 t).
Proof.
  move=> /L_facts.eval_iff [_] [?] ->. by constructor.
Qed.

Lemma steps_apps_lams n (ts : list term) s :
  n = length ts ->
  Forall (fun t' => eval t' t') ts ->
  Forall closed ts ->
  clos_refl_trans _ step (apps (lams n s) ts) (substs 0 (rev ts) s).
Proof.
  move=> -> H. elim: H s.
  - move=> ? /= *. rewrite substs_nil. by apply: rt_refl.
  - move=> t' {}ts H1t' Hts IH s /Forall_cons_iff [H2t'] /[dup] ? /IH {}IH.
    move: H1t' => /L_facts.eval_iff [_] [t'' ?]. subst.
    rewrite /=. apply: rt_trans.
    + apply: rt_steps_apps_r. apply: rt_trans.
      { apply: rt_step. by constructor. }
      rewrite subst_lams. by apply: rt_refl.
    + apply: rt_trans; first by apply IH.
      rewrite Nat.add_0_r -length_rev.
      rewrite substs_subst; [done|by apply: Forall_rev|].
      by apply: rt_refl.
Qed.

Lemma eval_rt_steps_subst s t1 t2 : eval t1 t2 -> clos_refl_trans _ step (app (lam s) t1) (subst s 0 t2).
Proof.
  move=> /L_facts.eval_iff [/ARS.star_clos_rt_iff ?] [?] ?. subst.
  apply: rt_trans.
  - apply: rt_steps_app_l. by eassumption.
  - apply: rt_step. by constructor.
Qed.

Lemma eval_rt_steps s t : eval s t -> clos_refl_trans term step s t.
Proof.
  move=> /L_facts.eval_iff [?] [?] ?. subst.
  by apply /ARS.star_clos_rt_iff.
Qed.

Lemma eval_rt_steps_eval s t u : eval s t -> clos_refl_trans _ step s u -> eval u t.
Proof.
  move=> /L_facts.eval_iff [+] [s'] ?. subst.
  move=> + /ARS.star_clos_rt_iff.
  move=> /L_facts.confluence /[apply] - [?] [H1 H2].
  apply /L_facts.eval_iff.
  have Hs' : L_facts.lambda (lam s') by eexists.
  split.
  - have := L_facts.lam_terminal Hs'.
    move: H1 H2 => []; first done.
    by move=> > + _ _ H => /H.
  - by eexists.
Qed.

Lemma rt_steps_eval_eval s t u : clos_refl_trans _ step s u -> eval u t -> eval s t.
Proof.
  move=> ? /L_facts.eval_iff [/ARS.star_clos_rt_iff ??].
  apply /L_facts.eval_iff. split; last done.
  apply /ARS.star_clos_rt_iff /rt_trans; by eassumption.
Qed.

Lemma eval_apps_lams n (ts : list term) s t :
  n = length ts ->
  Forall (fun t' => eval t' t') ts ->
  Forall closed ts ->
  eval (substs 0 (rev ts) s) t ->
  eval (apps (lams n s) ts) t.
Proof.
  move=> /steps_apps_lams /[apply] /[apply] H.
  apply: rt_steps_eval_eval. by apply: H.
Qed.

Lemma closed_rt_step {s t} : clos_refl_trans term step s t -> closed s -> closed t.
Proof.
  elim; by eauto using L_facts.closed_step.
Qed.

Lemma steps_stuck_eval s t : closed s -> clos_refl_trans term step s t -> stuck step t -> eval s t.
Proof.
  move=> /closed_rt_step Hs /[dup] /Hs H't Hst Ht.
  apply /L_facts.eval_iff. split.
  - by apply /ARS.star_clos_rt_iff.
  - by move: H't => /L_facts.comb_proc_red [[]|[? /Ht]].
Qed.

Lemma eval_steps_stuck s t : eval s t -> terminates step s.
Proof.
  move=> /L_facts.eval_iff [?] [?] ?. subst.
  eexists. split.
  - apply /ARS.star_clos_rt_iff. by eassumption.
  - move=> ? H. by inversion H.
Qed.
