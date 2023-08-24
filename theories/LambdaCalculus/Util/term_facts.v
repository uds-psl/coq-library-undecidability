(* Key definitions and properties of lambda-terms *)

From Undecidability Require L.L L.Util.L_facts.
Require Import Undecidability.LambdaCalculus.Lambda.
Require Import PeanoNat Lia List Relations.

Import L (term, var, app, lam).
Import L_facts (bound, closed_dcl, dclvar, dclApp, dcllam).

Require Import ssreflect.

Set Default Goal Selector "!".

Unset Implicit Arguments.

Fixpoint allfv (P : nat -> Prop) t := 
  match t with
  | var x => P x
  | app s t => allfv P s /\ allfv P t
  | lam t => allfv (scons True P) t
  end.

(* P-neutral term *)
Inductive neutral (P : term -> Prop) : term -> Prop :=
  | neutral_var x : neutral P (var x)
  | neutral_app M N : neutral P M -> P N -> neutral P (app M N).

Inductive normal_form : term -> Prop :=
  | normal_var x : normal_form (var x)
  | normal_abs M : normal_form M -> normal_form (lam M)
  | normal_form_app_var x N : normal_form N -> normal_form (app (var x) N)
  | normal_form_app_app M1 M2 N : normal_form (app M1 M2) -> normal_form N -> normal_form (app (app M1 M2) N).

Fixpoint term_size (M : term) :=
  match M with
  | var _ => 1
  | app M' N' => 1 + term_size M' + term_size N'
  | lam M' => 1 + term_size M'
  end.

#[local] Notation sn := (Acc (fun x y => step y x)).
#[local] Notation rt_steps := (clos_refl_trans _ step).
#[local] Notation t_steps := (clos_trans _ step).
#[local] Notation many_app M Ns := (fold_left app Ns M).

Lemma P_equal {X : Type} (P : X -> Prop) x1 x2 : P x1 -> x2 = x1 -> P x2.
Proof. congruence. Qed.

Lemma clos_trans_flip {X : Type} {R : X -> X -> Prop} {x y} : clos_trans _ R x y ->
  clos_trans _ (fun y x => R x y) y x.
Proof. by elim; eauto using clos_trans. Qed.

Lemma clos_refl_trans_flip {X : Type} {R : X -> X -> Prop} {x y} : clos_refl_trans _ R x y ->
  clos_refl_trans _ (fun y x => R x y) y x.
Proof. by elim; eauto using clos_refl_trans. Qed.

Lemma clos_rt_t' {X : Type} (R : X -> X -> Prop) x y z :
  clos_trans _ R x y -> clos_refl_trans _ R y z -> clos_trans _ R x z.
Proof. move=> H /clos_rt_rtn1_iff H'. elim: H' H; by eauto using clos_trans. Qed.

Lemma neutralE P M : neutral P M ->
  match M with
  | var _ => True
  | app M N => neutral P M /\ P N
  | lam _ => False
  end.
Proof. by case. Qed.

Lemma ext_ren_term xi1 xi2 t : (forall n, xi1 n = xi2 n) -> ren xi1 t = ren xi2 t.
Proof.
  elim: t xi1 xi2.
  - move=> > /= ?. by congr var.
  - move=> ? IH1 ? IH2 ?? Hxi /=. congr app; [by apply: IH1 | by apply: IH2].
  - move=> ? IH > Hxi /=. congr lam. apply: IH.
    case; first done. move=> ?. by congr S.
Qed.

Lemma ext_subst_term sigma1 sigma2 t : (forall n, sigma1 n = sigma2 n) ->
  subst sigma1 t = subst sigma2 t.
Proof.
  elim: t sigma1 sigma2.
  - by move=> > /= ?.
  - move=> ? IH1 ? IH2 ?? Hsigma /=. congr app; [by apply: IH1 | by apply: IH2].
  - move=> ? IH > Hsigma /=. congr lam. apply: IH.
    case; first done. move=> ?. by rewrite /= Hsigma.
Qed.

Lemma ren_ren_term xi1 xi2 t : ren xi2 (ren xi1 t) = ren (funcomp xi2 xi1) t.
Proof.
  elim: t xi1 xi2 => /=.
  - done.
  - move=> ? IH1 ? IH2 ??. by rewrite IH1 IH2.
  - move=> ? IH ??. rewrite IH.
    congr lam. apply: ext_ren_term. by case.
Qed.

Lemma ren_as_subst_term xi t : ren xi t = subst (funcomp var xi) t.
Proof.
  elim: t xi => /=.
  - done.
  - move=> ? IH1 ? IH2 ?. by rewrite IH1 IH2.
  - move=> ? IH ?. rewrite IH.
    congr lam. apply: ext_subst_term. by case.
Qed.

Lemma ren_subst_term xi sigma t : ren xi (subst sigma t) = subst (funcomp (ren xi) sigma) t.
Proof.
  elim: t xi sigma => /=.
  - done.
  - move=> ? IH1 ? IH2 ??. by rewrite IH1 IH2.
  - move=> ? IH ??. rewrite IH.
    congr lam. apply: ext_subst_term.
    case; first done. move=> ?. by rewrite /= !ren_ren_term.
Qed.

Lemma subst_ren_term xi sigma t : subst sigma (ren xi t) = subst (funcomp sigma xi) t.
Proof.
  elim: t xi sigma => /=.
  - done.
  - move=> ? IH1 ? IH2 ??. by rewrite IH1 IH2.
  - move=> ? IH ??. rewrite IH.
    congr lam. apply: ext_subst_term. by case.
Qed.

Lemma subst_subst_term sigma1 sigma2 t : subst sigma2 (subst sigma1 t) = subst (funcomp (subst sigma2) sigma1) t.
Proof.
  elim: t sigma1 sigma2 => /=.
  - done.
  - move=> ? IH1 ? IH2 ??. by rewrite IH1 IH2.
  - move=> ? IH ??. rewrite IH.
    congr lam. apply: ext_subst_term.
    case; first done. move=> ?.
    by rewrite /= !ren_subst_term !subst_ren_term.
Qed.

Lemma subst_var_term s : subst var s = s.
Proof.
  elim: s.
  - done.
  - move=> ? IH1 ? IH2 /=. by rewrite IH1 IH2.
  - move=> ? IH /=. congr lam. rewrite -[RHS]IH.
    apply: ext_subst_term. by case.
Qed.

Lemma ren_id_term s : ren id s = s.
Proof. by rewrite ren_as_subst_term subst_var_term. Qed.

Definition simpl_term := (ren_ren_term, ren_subst_term, subst_ren_term, subst_subst_term, subst_var_term, ren_id_term).

Lemma boundE k s : bound k s ->
  match s with
  | var n => k > n
  | app s t => bound k s /\ bound k t
  | lam s => bound (S k) s
  end.
Proof. by case. Qed.

Lemma bound_ext_subst_term {k sigma1 sigma2 s} : bound k s -> (forall n, n < k -> sigma1 n = sigma2 n) ->
  subst sigma1 s = subst sigma2 s.
Proof.
  elim: s k sigma1 sigma2.
  - move=> > /boundE /= ?. by apply.
  - move=> ? IH1 ? IH2 k sigma1 sigma2 /boundE + ? /=.
    move=> [/IH1] => /(_ sigma1 sigma2) ->; first done.
    by move=> /IH2 => /(_ sigma1 sigma2) ->.
  - move=> ? IH k sigma1 sigma2 /boundE /IH {}IH H /=. congr lam.
    apply: IH.
    move=> [|n]; first done.
    move=> /= ?. rewrite H; [lia|done].
Qed.

Lemma subst_closed {sigma t} : L.closed t -> subst sigma t = t.
Proof.
  move=> /closed_dcl /bound_ext_subst_term.
  rewrite -[RHS]subst_var_term. apply. lia.
Qed.

Lemma ren_closed {xi t} : L.closed t -> ren xi t = t.
Proof. rewrite ren_as_subst_term. by apply: subst_closed. Qed.

Lemma L_subst_Lambda_subst s k t :
  L.closed t -> L.subst s k t = subst (fun n => if Nat.eqb n k then t else var n) s.
Proof.
  move=> Ht. elim: s k.
  - done. 
  - move=> ? IH1 ? IH2 ? /=. by rewrite IH1 IH2.
  - move=> ? IH k /=. rewrite IH.
    congr lam. apply: ext_subst_term.
    move=> [|n] /=; first done.
    case: (Nat.eqb n k); last done.
    by rewrite (ren_closed Ht).
Qed.

Lemma bound_ren {k k' xi t} : bound k t -> (forall n, n < k -> xi n < k') -> bound k' (ren xi t).
Proof.
  elim: t k k' xi.
  - move=> > /boundE ? H /=. apply: dclvar. by apply: H.
  - move=> ? IH1 ? IH2 > /boundE + ? /=.
    move=> [/IH1 {}IH1 /IH2 {}IH2]. apply: dclApp; [by apply: IH1|by apply: IH2].
  - move=> ? IH > /boundE /IH {}IH H /=.
    apply: dcllam. apply: IH.
    move=> [|n] /=; [|have := H n]; lia.
Qed.

Lemma bound_subst {k k' sigma t} : bound k t -> (forall n, n < k -> bound k' (sigma n)) -> bound k' (subst sigma t).
Proof.
  elim: t k k' sigma.
  - move=> > /boundE ? H /=. by apply: H.
  - move=> ? IH1 ? IH2 > /boundE + ? /=.
    move=> [/IH1 {}IH1 /IH2 {}IH2]. apply: dclApp; [by apply: IH1|by apply: IH2].
  - move=> ? IH > /boundE /IH {}IH H /=.
    apply: dcllam. apply: IH.
    move=> [|n] /=.
    + move=> _. apply: dclvar. lia.
    + move=> ?. apply: bound_ren; [apply: H|]; lia.
Qed.

Lemma not_closed_var n : L.closed (var n) -> False.
Proof. move=> /(_ n (lam (var 0))) /=. by rewrite Nat.eqb_refl. Qed.

Lemma closed_I s : (forall k, L.subst s k (lam (var 0)) = s) -> L.closed s.
Proof.
  move=> H k u. elim: s k u {H}(H k).
  - move=> /=. move=> n k u. by case: (Nat.eqb n k).
  - by move=> ? IH1 ? IH2 k ? /= [/IH1 -> /IH2 ->].
  - by move=> ? IH k ? /= [/IH ->].
Qed.

Lemma snE M : sn M ->
  match M with
  | var x => True
  | app M N => sn M /\ sn N
  | lam M => sn M
  end.
Proof.
  elim. case.
  - done.
  - move=> M1 M2 IH1 IH2. split.
    + by constructor=> ? /(stepAppL _ _ M2) /IH2 [].
    + by constructor=> ? /(stepAppR M1) /IH2 [].
  - move=> M1 IH1 IH2. by constructor=> ? /stepLam /IH2.
Qed.

Lemma stepE M N : step M N ->
  match M with
  | var _ => False
  | app M1 M2 =>
    (exists M3, M1 = lam M3 /\ N = (subst (scons M2 var) M3)) \/
    (exists M1', step M1 M1' /\ N = app M1' M2) \/
    (exists M2', step M2 M2' /\ N = app M1 M2')
  | lam M => exists M', step M M' /\ N = lam M' 
  end.
Proof.
  case=> *.
  - left. by eexists.
  - right. left. eexists. by split; [eassumption|].
  - right. right. eexists. by split; [eassumption|].
  - eexists. by split; [eassumption|].
Qed.

Lemma normal_form_not_step {M} : normal_form M -> forall N, not (step M N).
Proof.
  elim.
  - by move=> > /stepE.
  - by move=> > _ IH ? /stepE [?] [/IH].
  - move=> > ? IH ? /stepE.
    by move=> [|[|]] [?] [] => [|/stepE|/IH].
  - move=> > _ IH1 _ IH2 ? /stepE.
    by move=> [|[|]] [?] [] => [|/IH1|/IH2].
Qed.

Lemma normal_formE M : normal_form M ->
  match M with
  | var _ => True
  | app M N =>
    match M with
    | var _ => normal_form N
    | app _ _ => normal_form M /\ normal_form N 
    | lam _ => False
    end
  | lam M => normal_form M
  end.
Proof. by case. Qed.

Lemma not_step_normal_form {M} : (forall N, not (step M N)) -> normal_form M.
Proof.
  rewrite /not. elim: M.
  - by do ? constructor.
  - move=> [?|M1 M2|?] IH1 N IH2 H; [..|exfalso].
    all: do ? constructor; by eauto using step.
  - do ? constructor. by eauto using step.
Qed.

Lemma step_dec M : (exists N, step M N) \/ (forall N, not (step M N)).
Proof.
  elim: M.
  - move=> ?. by right=> ? /stepE.
  - move=> M [[M' IH1]|IH1].
    { move=> ? _. left. eexists. apply: stepAppL. by eassumption. }
    move=> N [[N' IH2]|IH2].
    { left. eexists. apply: stepAppR. by eassumption. }
    case: M IH1.
    + move=> > IH1. by right=> ? /stepE [|[|]] [?] [] => [|/IH1|/IH2].
    + move=> > IH1. by right=> ? /stepE [|[|]] [?] [] => [|/IH1|/IH2].
    + move=> *. left. eexists. by apply: stepSubst.
  - move=> M [[??]|IH].
    + left. eexists. apply: stepLam. by eassumption.
    + by right=> ? /stepE [?] [/IH].
Qed.

Lemma normal_form_dec M : (normal_form M) \/ not (normal_form M).
Proof.
  case: (step_dec M).
  - move=> [N] /normal_form_not_step HMN. by right.
  - move=> /not_step_normal_form ?. by left.
Qed.

Lemma t_stepsAppL M M' N : t_steps M M' -> t_steps (app M N) (app M' N).
Proof. by elim; eauto using clos_trans, step. Qed.

Lemma t_stepsAppR M N N' : t_steps N N' -> t_steps (app M N) (app M N').
Proof. by elim; eauto using clos_trans, step. Qed.

Lemma t_stepsLam M M' : t_steps M M' -> t_steps (lam M) (lam M').
Proof. by elim; eauto using clos_trans, step. Qed.

Lemma rt_stepsAppL M M' N :rt_steps M M' -> rt_steps (app M N) (app M' N).
Proof. by elim; eauto using clos_refl_trans, step. Qed.

Lemma rt_stepsAppR M N N' : rt_steps N N' -> rt_steps (app M N) (app M N').
Proof. by elim; eauto using clos_refl_trans, step. Qed.

Lemma rt_stepsLam M M' : rt_steps M M' -> rt_steps (lam M) (lam M').
Proof. by elim; eauto using clos_refl_trans, step. Qed.

Lemma ren_step xi M M' : step M M' -> step (ren xi M) (ren xi M').
Proof.
  move=> H. elim: H xi; [|by eauto using step..].
  move=> > /=. apply: P_equal; [by apply: stepSubst|].
  rewrite !simpl_term. apply: ext_subst_term. by case.
Qed.

Lemma subst_step M N sigma : step M N ->
  step (subst sigma M) (subst sigma N).
Proof.
  move=> H. elim: H sigma; [|by eauto using step..].
  move=> > /=.
  apply: P_equal; [apply: stepSubst|].
  rewrite !simpl_term. apply: ext_subst_term=> - [|?]; [done|].
  by rewrite /= !simpl_term.
Qed.

Lemma ren_steps xi M M' : clos_refl_trans _ step M M' ->
  clos_refl_trans _ step (ren xi M) (ren xi M').
Proof. by elim; eauto using clos_refl_trans, ren_step. Qed.

Lemma subst_steps sigma sigma' M : (forall n, clos_refl_trans _ step (sigma n) (sigma' n)) ->
  clos_refl_trans _ step (subst sigma M) (subst sigma' M).
Proof.
  elim: M sigma sigma'.
  - move=> ???. by apply.
  - move=> * /=. apply: rt_trans; [apply: rt_stepsAppR|apply: rt_stepsAppL]; by auto.
  - move=> ? IH * /=. apply: rt_stepsLam. apply: IH.
    move=> [|?] /=; [by apply rt_refl|].
    by apply: ren_steps.
Qed.

(* weak normalization property *)
Inductive wn M : Prop :=
  | wn_intro N : clos_refl_trans term step M N -> normal_form N -> wn M.

Arguments wn_intro {M}.

Lemma allfv_trivial (P : nat -> Prop) t : (forall x, P x) -> allfv P t.
Proof.
  elim: t P=> /=; [by auto..|].
  move=> ? IH *. by apply: IH => - [|?].
Qed.

Lemma allfv_impl (P Q : nat -> Prop) t : 
  (forall x, P x -> Q x) -> allfv P t -> allfv Q t.
Proof.
  elim: t P Q => /=.
  - move=> >. by apply.
  - move=> ? IH1 ? IH2 > /[dup] /IH1 {}IH1 /IH2 {}IH2. tauto.
  - move=> > IH > H /=. apply: IH.
    by case.
Qed.

Lemma allfv_dec P M : (forall x, P x \/ not (P x)) -> allfv P M \/ not (allfv P M).
Proof.
  elim: M P=> /=.
  - done.
  - move=> s IH1 t IH2 ? /[dup] /IH1 {}IH1 /IH2 {}IH2. tauto.
  - move=> ? IH P H.
    case: (IH (scons True P)); [|by auto..].
    move=> [|?] /=; by auto.
Qed.

Lemma allfv_ren (P : nat -> Prop) xi t :
  allfv (funcomp P xi) t ->  allfv P (ren xi t).
Proof.
  elim: t P xi.
  - done.
  - move=> ? IH1 ? IH2 > /= [??]. by auto.
  - move=> ? IH > /= H. apply: IH.
    by apply: allfv_impl H => - [|?].
Qed.

Lemma allfv_subst (P : nat -> Prop) sigma t :
  allfv (fun x => allfv P (sigma x)) t ->  allfv P (subst sigma t).
Proof.
  elim: t P sigma.
  - done.
  - move=> ? IH1 ? IH2 > /= [??]. by auto.
  - move=> ? IH > /= H. apply: IH.
    apply: allfv_impl H => - [|?] /= H; [done|].
    apply: allfv_ren. by apply: allfv_impl H. 
Qed.

Lemma ext_allfv_subst_term sigma1 sigma2 t : allfv (fun x=> sigma1 x = sigma2 x) t ->
  subst sigma1 t = subst sigma2 t.
Proof.
  elim: t sigma1 sigma2.
  - by move=> > /= ?.
  - by move=> ? IH1 ? IH2 ?? /= [/IH1 -> /IH2 ->].
  - move=> ? IH > /= Hsigma. congr lam. apply: IH.
    apply: allfv_impl Hsigma.
    by move=> [|x] /= => [|->].
Qed.

Lemma ext_allfv_ren_term xi1 xi2 t : allfv (fun x=> xi1 x = xi2 x) t -> ren xi1 t = ren xi2 t.
Proof.
  move=> H. rewrite !ren_as_subst_term. apply: ext_allfv_subst_term.
  by apply: allfv_impl H => ? /= ->.
Qed.

Lemma stepSubst' s t u : u = subst (scons t var) s -> step (app (lam s) t) u.
Proof. move=> ->. by apply: stepSubst. Qed.

Lemma subst_as_ren M x : subst (scons (var x) var) M = ren (scons x id) M.
Proof.
  rewrite ren_as_subst_term /=. apply: ext_subst_term. by case.
Qed.

Lemma step_ren xi M N : step M N -> step (ren xi M) (ren xi N).
Proof.
  move=> H. elim: H xi.
  { move=> > /=.
    apply: stepSubst'.
    rewrite !simpl_term. apply: ext_subst_term.
    by case. }
  all: by eauto using step with nocore.
Qed.

Fact normal_form_ren xi M : 
  normal_form M -> normal_form (ren xi M).
Proof.
  move=> H. elim: H xi; cbn; by eauto using normal_form.
Qed.

Fact normal_form_ren' xi M : 
  normal_form (ren xi M) -> normal_form M.
Proof.
  elim: M xi=> /=.
  - by eauto using normal_form.
  - move=> [?|??|?] /= IH1 ? IH2 ? /normal_formE.
    + by eauto using normal_form.
    + move=> [??]. by eauto using normal_form.
    + done.
  - move=> ??? /normal_formE. by eauto using normal_form.
Qed.

Lemma step_renE xi M N : step (ren xi M) N -> exists N', N = ren xi N' /\ step M N'.
Proof.
  move E: (ren xi M) => M' H. elim: H xi M E.
  - move=> ??? [] //.
    move=> [] // ?? /= [<- <-]. eexists.
    split; first last. { by apply: stepSubst. }
    rewrite !simpl_term. apply: ext_subst_term.
    by case.
  - move=> > ? IH ? [] //= ?? [??]. subst.
    have [? [? ?]] := IH _ _ eq_refl. subst.
    eexists.
    split; first last. { apply: stepAppL. eassumption. }
    done.
  - move=> > ? IH ? [] //= ?? [??]. subst.
    have [? [? ?]] := IH _ _ eq_refl. subst.
    eexists.
    split; first last. { apply: stepAppR. eassumption. }
    done.
  - move=> > ? IH ? [] //= ? [?]. subst.
    have [? [? ?]] := IH _ _ eq_refl. subst.
    eexists.
    split; first last. { apply: stepLam. eassumption. }
    done.
Qed.

Lemma steps_renE xi M N : clos_refl_trans term step (ren xi M) N -> exists N', N = ren xi N' /\ clos_refl_trans term step M N'.
Proof.
  move E: (ren xi M) => M' /clos_rt_rt1n_iff H.
  elim: H xi M E.
  { move=> > <-. eexists. split;[done|]. by apply: rt_refl. }
  move=> > +++ > ?. subst. move=> /step_renE [?] [->] ? _.
  move=> /(_ _ _ eq_refl) [?] [->] ?.
  eexists. split; [done|].
  apply: rt_trans; [apply: rt_step|]; eassumption.
Qed.

Lemma term_size_many_app M Ns : term_size (many_app M Ns) = list_sum (map (fun N => S (term_size N)) Ns) + term_size M.
Proof.
  elim: Ns M.
  - done.
  - move=> ?? IH ? /=. rewrite IH /=. lia.
Qed.

Lemma neutral_normal_form M :
  neutral normal_form M -> normal_form M.
Proof.
  elim.
  - by constructor.
  - move=> > []; do ? constructor; by auto.
Qed.

Lemma normal_form_neutral M : normal_form M ->
  neutral normal_form M \/
  (exists N, M = lam N /\ normal_form N).
Proof.
  elim.
  - move=> >. left. by constructor.
  - move=> *. right. by do ? econstructor.
  - move=> *. left. by do ? constructor.
  - move=> > ? [?| [? [??]]]; [|done].
    left. by constructor.
Qed.

Lemma normal_form_app_neutral M N : normal_form (app M N) -> neutral normal_form (app M N).
Proof. by move=> > /normal_form_neutral [?|[?] [??]]. Qed.

Lemma neutral_impl (P Q : term -> Prop) M :
  (forall N, P N -> Q N) ->
  neutral P M -> neutral Q M.
Proof. move=> H. elim; by auto using neutral. Qed.

Lemma neutral_dec P M : (forall M, P M \/ not (P M)) ->
  neutral P M \/ not (neutral P M).
Proof.
  move=> H. elim: M.
  - left. by constructor.
  - move=> M [].
    + move=> ? N _. case: (H N).
      * left. by constructor.
      * move=> ?. by right => /neutralE [].
    + move=> *. by right => /neutralE [].
  - by right=> /neutralE.
Qed.

Lemma ren_many_app xi M Ns : ren xi (many_app M Ns) = many_app (ren xi M) (map (ren xi) Ns).
Proof. elim: Ns M; [done|]. move=> > IH ? /=. by rewrite IH. Qed.

Lemma subst_many_app sigma M Ns : subst sigma (many_app M Ns) = many_app (subst sigma M) (map (subst sigma) Ns).
Proof. elim: Ns M; [done|]. move=> > IH ? /=. by rewrite IH. Qed.

Module TermNotations.
(* strong normalization *)
Notation sn := (Acc (fun x y => step y x)).
(* reflexive, transite closure of step *)
Notation rt_steps := (clos_refl_trans _ step).
(* transite closure of step *)
Notation t_steps := (clos_trans _ step).
(* iterated term application *)
Notation many_app M Ns := (fold_left app Ns M).
End TermNotations.
