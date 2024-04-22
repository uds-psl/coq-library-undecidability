(* Key definitions and properties of lambda-terms *)

From Undecidability.L Require L Util.L_facts.
From Undecidability.LambdaCalculus Require Import Lambda Util.facts Util.confluence.
Require Import PeanoNat Lia List Relations.
Import ListNotations.

Import L (term, var, app, lam).
Import L_facts (bound, closed_dcl, dclvar, dclApp, dcllam).

Require Import ssreflect.

Set Default Goal Selector "!".

#[local] Unset Implicit Arguments.

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
#[local] Notation lams k M := (Nat.iter k lam M).

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

Lemma neutralE' (P : term -> Prop) M : neutral P M -> exists x Ms, M = many_app (var x) Ms /\ Forall P Ms.
Proof.
  elim.
  - move=> x. by exists x, [].
  - move=> {}M N ? [x] [Ms] [->] ??.
    exists x, (Ms ++ [N]). split.
    + by rewrite fold_left_app /=.
    + apply /Forall_app. split; first done.
      by constructor.
Qed.

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

Lemma allfv_impl (P Q : nat -> Prop) t : 
  (forall x, P x -> Q x) -> allfv P t -> allfv Q t.
Proof.
  elim: t P Q => /=.
  - move=> >. by apply.
  - move=> ? IH1 ? IH2 > /[dup] /IH1 {}IH1 /IH2 {}IH2. tauto.
  - move=> > IH > H /=. apply: IH.
    by case.
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

Lemma allfv_closed M : (forall P, allfv P M) -> closed M.
Proof.
  move=> HM sigma. rewrite -[RHS]subst_var_term.
  apply: ext_allfv_subst_term. by apply: HM.
Qed.

Lemma subst_closed sigma M : closed M -> subst sigma M = M.
Proof. by apply. Qed.

Lemma ren_closed xi M : closed M -> ren xi M = M.
Proof. rewrite ren_as_subst_term. by apply. Qed.

Lemma subst_L_closed {sigma t} : L.closed t -> subst sigma t = t.
Proof.
  move=> /closed_dcl /bound_ext_subst_term.
  rewrite -[RHS]subst_var_term. apply. lia.
Qed.

Lemma ren_L_closed {xi t} : L.closed t -> ren xi t = t.
Proof. rewrite ren_as_subst_term. by apply: subst_L_closed. Qed.

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
    by rewrite (ren_L_closed Ht).
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

Lemma allfv_allfv_impl (P Q : nat -> Prop) t : 
  allfv (fun x => P x -> Q x) t -> allfv P t -> allfv Q t.
Proof.
  elim: t P Q => /=.
  - move=> >. by apply.
  - move=> ? IH1 ? IH2 > [/IH1 {}IH1] /IH2 {}IH2.
    by move=> [/IH1] {}IH1 /IH2 {}IH2.
  - move=> ? > IH > H /=. apply: IH.
    apply: allfv_impl H. by case.
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

Lemma allfv_ren' (P : nat -> Prop) xi t :
  allfv P (ren xi t) -> allfv (funcomp P xi) t.
Proof.
  elim: t P xi.
  - done.
  - move=> ? IH1 ? IH2 > /= [??]. split.
    + by apply: IH1.
    + by apply: IH2.
  - move=> ? IH > /= /IH.
    by apply: allfv_impl => - [|?].
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

Lemma allfv_subst' (P : nat -> Prop) sigma t :
  allfv P (subst sigma t) -> allfv (fun x => allfv P (sigma x)) t.
Proof.
  elim: t P sigma.
  - done.
  - move=> ? IH1 ? IH2 > /= [??]. by auto.
  - move=> ? IH > /= /IH.
    apply: allfv_impl => - [|?] /=; [done|].
    move=> /allfv_ren'. by apply: allfv_impl.
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

Lemma normal_form_steps N M : normal_form N -> rt_steps N M -> N = M. 
Proof.
  move=> /normal_form_not_step H /clos_rt_rt1n_iff H'.
  case: H' H; first done.
  by move=> > + _ H => /H.
Qed.

Lemma ren_apps xi M Ns : ren xi (many_app M Ns) = many_app (ren xi M) (map (ren xi) Ns).
Proof.
  elim: Ns M; first done.
  move=> ?? IH M /=. by rewrite IH.
Qed.

Lemma subst_apps sigma M Ns : subst sigma (many_app M Ns) = many_app (subst sigma M) (map (subst sigma) Ns).
Proof.
  elim: Ns M; first done.
  move=> ?? IH M /=. by rewrite IH.
Qed.

Lemma allfv_step P M N : step M N -> allfv P M -> allfv P N.
Proof.
  move=> H. elim: H P.
  - move=> /= > [HM HN]. apply: allfv_subst.
    apply: allfv_impl HM. by case.
  - by move=> > ? IH ? /= [/IH ??].
  - by move=> > ? IH ? /= [? /IH ?].
  - move=> > ? IH ?. by apply: IH.
Qed.

Lemma allfv_steps P M N : rt_steps M N -> allfv P M -> allfv P N.
Proof.
  elim.
  - move=> > /allfv_step. by apply.
  - done.
  - by auto.
Qed.

Lemma allfv_apps P M Ms : allfv P M -> Forall (allfv P) Ms -> allfv P (many_app M Ms).
Proof.
  elim: Ms M; first done.
  move=> M' Ms IH M ? /Forall_cons_iff [? /IH] /=. by apply.
Qed.

Lemma allfv_lams P n M : allfv (Nat.iter n (scons True) P) M -> allfv P (lams n M).
Proof.
  elim: n P; first done.
  move=> n IH P.
  rewrite Nat.iter_succ_r.
  by apply: IH.
Qed.

Lemma steps_ren xi M N : rt_steps M N -> rt_steps (ren xi M) (ren xi N).
Proof.
  elim=> *.
  - apply: rt_step. by apply: step_ren.
  - by apply: rt_refl.
  - apply: rt_trans; by eassumption.
Qed.

Lemma steps_ren' xi M N : rt_steps (ren xi M) N -> exists N', N = ren xi N' /\ rt_steps M N'.
Proof.
  move=> /clos_rt_rtn1_iff. elim.
  - exists M. by split; [|apply: rt_refl].
  - move=> > H ? [?] [??]. subst.
    move: H=> /step_renE [?] [??]. subst.
    eexists. subst. split; first done.
    by apply: rt_trans; [|apply: rt_step]; eassumption.
Qed.

Lemma steps_subst sigma M N : rt_steps M N -> rt_steps (subst sigma M) (subst sigma N).
Proof.
  elim=> *.
  - apply: rt_step. by apply: subst_step.
  - by apply: rt_refl.
  - apply: rt_trans; by eassumption.
Qed.

Lemma stepsAppL N M M' : rt_steps M M' -> rt_steps (app M N) (app M' N).
Proof.
  elim=> *.
  - apply: rt_step. by apply: stepAppL.
  - by apply: rt_refl.
  - apply: rt_trans; by eassumption.
Qed.

Lemma stepsAppR N M M' : rt_steps M M' -> rt_steps (app N M) (app N M').
Proof.
  elim=> *.
  - apply: rt_step. by apply: stepAppR.
  - by apply: rt_refl.
  - apply: rt_trans; by eassumption.
Qed.

Lemma stepsLam M M' : rt_steps M M' -> rt_steps (lam M) (lam M').
Proof.
  elim=> *.
  - apply: rt_step. by apply: stepLam.
  - by apply: rt_refl.
  - apply: rt_trans; by eassumption.
Qed.

Lemma steps_subst' sigma sigma' M : (forall x, rt_steps (sigma x) (sigma' x)) -> rt_steps (subst sigma M) (subst sigma' M).
Proof.
  elim: M sigma sigma'.
  - move=> >. by apply.
  - move=> M IHM N IHN > H /=. apply: rt_trans.
    + apply: stepsAppL. apply IHM. by eassumption.
    + apply: stepsAppR. apply IHN. by eassumption.
  - move=> M IH > H /=. apply stepsLam. apply: IH.
    move=> [|x] /=; first by apply: rt_refl.
    apply: steps_ren. by apply: H.
Qed.

Lemma steps_subst'' sigma sigma' M M' : (forall x, rt_steps (sigma x) (sigma' x)) -> rt_steps M M' -> rt_steps (subst sigma M) (subst sigma' M').
Proof.
  move=> H /(steps_subst sigma'). apply: rt_trans. by apply: steps_subst'.
Qed.

Lemma stepAppsL M M' Ns : step M M' -> step (many_app M Ns) (many_app M' Ns).
Proof.
  move: M M'.
  elim: Ns; first done.
  move=> N Ns IH /= M M' H. apply: IH. by apply: stepAppL.
Qed.

Lemma stepsAppsL M M' Ns : rt_steps M M' -> rt_steps (many_app M Ns) (many_app M' Ns).
Proof.
  elim=> *.
  - apply: rt_step. by apply: stepAppsL.
  - apply: rt_refl.
  - apply: rt_trans; by eassumption.
Qed.

Lemma stepsAppsR M Ms M's : Forall2 rt_steps Ms M's -> rt_steps (many_app M Ms) (many_app M M's).
Proof.
  move=> H. elim: H M; first by apply: rt_refl.
  move=> > ?? IH M /=.
  apply: rt_trans.
  { apply: stepsAppsL. apply: stepsAppR. by eassumption. }
  by apply: IH.
Qed.

Lemma stepsLams k M M' : rt_steps M M' -> rt_steps (lams k M) (lams k M').
Proof.
  move=> ?. elim: k; first done.
  move=> *. rewrite /=. apply: stepsLam. by eassumption.
Qed.

Definition up (sigma: nat -> term) := scons (var 0) (funcomp (ren S) sigma).

Lemma subst_lams sigma k M : subst sigma (lams k M) = lams k (subst (Nat.iter k up sigma) M).
Proof.
  elim: k sigma M; first done.
  move=> k IH sigma M.
  rewrite !Nat.iter_succ_r /=.
  rewrite IH /=. congr (lams _ _).
  by rewrite -Nat.iter_succ_r /=.
Qed.

Lemma steps_refl M N : M = N -> rt_steps M N.
Proof.
  move=> <-. by apply: rt_refl.
Qed.

Lemma stepsReds M Ns : rt_steps (many_app (lams (length Ns) M) Ns) (subst (fold_left (fun sigma N => scons N sigma) Ns var) M).
Proof.
  suff: forall sigma, rt_steps (many_app (lams (length Ns) (subst (Nat.iter (length Ns) up sigma) M)) Ns) (subst (fold_left (fun sigma N => scons N sigma) Ns sigma) M).
  { move=> /(_ var) H. apply: rt_trans; [|by apply: H].
    apply: steps_refl. congr (many_app _ _). congr (lams _ _).
    rewrite -[LHS]subst_var_term. apply: ext_subst_term.
    elim: Ns {H}; first done.
    move=> N Ns IH [|x] /=; first done.
    by rewrite -IH. }
  elim: Ns M.
  - move=> ? sigma /=. by apply: rt_refl.
  - move=> N Ns IH M sigma /=.
    apply: rt_trans.
    + apply: stepsAppsL. apply: rt_step. by apply: stepSubst.
    + apply: rt_trans; [|by apply: IH]. apply: steps_refl.
      rewrite subst_lams. congr (many_app _ _). congr (lams _ _).
      rewrite subst_subst_term. apply: ext_subst_term.
      move: sigma {IH}. elim: Ns.
      { move=> sigma [|x] /=; first done.
        rewrite subst_ren_term. by apply: subst_var_term. }
      move=> n' Ns IH sigma [|x] /=; first done.
      by rewrite -IH subst_ren_term ren_subst_term /=.
Qed.

Lemma iter_up_lt k x sigma : x < k -> Nat.iter k up sigma x = var x.
Proof.
  elim: k sigma x.
  - lia.
  - move=> k IH sigma [|x] ? /=; first done.
    change (var (S x)) with (ren S (var x)).
    congr ren. apply: IH. lia.
Qed.

Lemma iter_up_ge k x sigma : x >= k -> Nat.iter k up sigma x = ren (fun y => k + y) (sigma (x - k)).
Proof.
  elim: k sigma x.
  - move=> *. by rewrite Nat.sub_0_r ren_id_term. 
  - move=> k IH sigma [|x] ? /=; first by lia.
    rewrite IH; first by lia.
    by rewrite ren_ren_term.
Qed.

Lemma iter_up_eq (x : nat) (sigma : nat -> term) :
  Nat.iter x up sigma x = ren (Nat.add x) (sigma 0).
Proof.
  by rewrite iter_up_ge ?Nat.sub_diag.
Qed.

Lemma apps_apps M M1s M2s : many_app (many_app M M1s) M2s = many_app M (M1s ++ M2s).
Proof.
  elim: M1s M; first done.
  move=> > + ?. by apply.
Qed.

Lemma lams_lams k1 k2 M : lams k1 (lams k2 M) = lams (k1 + k2) M.
Proof.
  elim: k1; first done.
  by move=> ? /= ->.
Qed.

Lemma stepsRed M N : rt_steps (app (lam M) N) (subst (scons N var) M).
Proof. apply: rt_step. by apply: stepSubst. Qed.

Lemma stepsReds' k (M : term) (Ns : list term) : length Ns = k ->
  rt_steps (many_app (lams k M) Ns) (subst (fold_left (fun sigma N => scons N sigma) Ns var) M).
Proof. move=> <-. by apply: stepsReds. Qed.

Lemma allfv_var (P : nat -> Prop) (x : nat) : P x -> allfv P (var x).
Proof. done. Qed.

Lemma allfv_app P M1 M2 : allfv P M1 -> allfv P M2 -> allfv P (app M1 M2).
Proof.
  move=> *. by split.
Qed.

Lemma apps_inj M Ms M's : many_app M Ms = many_app M M's -> Ms = M's.
Proof.
  elim /rev_ind: Ms M M's.
  - move=> ? [|??]; first done.
    move=> /(f_equal term_size) /=. rewrite term_size_many_app /=. lia.
  - move=> > IH ? M's. elim /rev_ind: M's.
    + move=> /(f_equal term_size) /=. rewrite term_size_many_app map_app list_sum_app /=. lia.
    + move=> ?? _. rewrite !fold_left_app /=.
      by move=> [] /IH <- <-.
Qed.

Lemma Forall2_steps_refl Ms : Forall2 rt_steps Ms Ms.
Proof.
  elim: Ms; first done.
  move=> *. constructor; last done.
  by apply: rt_refl.
Qed.

Lemma apps_last M Ms N : many_app M (Ms ++ [N]) = app (many_app M Ms) N.
Proof. by rewrite fold_left_app. Qed.

Lemma step_apps_varE x Ms M : step (many_app (var x) Ms) M -> exists M's, M = many_app (var x) M's /\ Forall2 rt_steps Ms M's.
Proof.
  move E: (many_app (var x) Ms) => M' H. elim: H Ms E.
  - move=> ?? Ms. elim /rev_ind: Ms; first done.
    move=> ? M's _. rewrite apps_last.
    move=> []. elim /rev_ind: M's; first done.
    move=> ?? _. by rewrite apps_last.
  - move=> > ? IH Ms. elim /rev_ind: Ms; first done.
    move=> ?? _. rewrite apps_last.
    move=> [??]. subst.
    move: (IH _ eq_refl) => [M's] [??]. subst.
    eexists. split; first by rewrite -apps_last.
    apply: Forall2_app; first done.
    by apply: Forall2_steps_refl.
  - move=> > ? IH Ms. elim /rev_ind: Ms; first done.
    move=> ? M's _. rewrite apps_last.
    move=> [??]. subst.
    eexists. split; first by rewrite -apps_last.
    apply: Forall2_app.
    + by apply: Forall2_steps_refl.
    + constructor; last done. by apply: rt_step.
  - move=> > ?? Ms. elim /rev_ind: Ms; first done.
    move=> > _. by rewrite apps_last.
Qed.

Lemma steps_apps_varE x Ms M's : rt_steps (many_app (var x) Ms) (many_app (var x) M's) -> Forall2 rt_steps Ms M's.
Proof.
  move E: (many_app (var x) Ms)=> M.
  move E': (many_app (var x) M's)=> M' /clos_rt_rt1n_iff H.
  elim: H Ms M's E E'.
  - move=> ? Ms M's <- /apps_inj <-.
    by apply: Forall2_steps_refl.
  - move=> > H ? IH > ??. subst.
    move: H => /step_apps_varE [M's] [?] H. subst.
    apply: Forall2_trans H (IH _ _ eq_refl eq_refl).
    move=> >. by apply: rt_trans.
Qed.

Lemma step_lamE M N : step (lam M) N -> match N with lam N' => step M N' | _ => False end.
Proof.
  intros H. by inversion H; subst.
Qed.

Lemma steps_lamE M N : rt_steps (lam M) N -> match N with lam N' => rt_steps M N' | _ => False end.
Proof.
  move E: (lam M) => M' /clos_rt_rt1n_iff H.
  elim: H M E.
  - move=> ?? <-. by apply: rt_refl.
  - move=> ? {}M M'' H _ IH ??. subst.
    move=> /step_lamE in H.
    move: M H IH=> [?|??|?]; [done..|].
    move=> ? /(_ _ eq_refl).
    move: M''=> [?|??|?]; [done..|].
    move=> ?. by apply: rt_trans; [apply: rt_step|]; eassumption.
Qed.

Lemma steps_lamsE k M N : rt_steps (lams k M) (lams k N) -> rt_steps M N.
Proof.
  elim: k; first done.
  by move=> k IH /= /steps_lamE /IH.
Qed.

Lemma steps_var_absurd (P : Prop) M x : allfv (fun y => y <> x) M -> rt_steps M (var x) -> P.
Proof.
  by move=> /allfv_steps /[apply].
Qed.

Lemma subst_lam sigma M : subst sigma (lam M) = lam (subst (up sigma) M).
Proof. done. Qed.

Lemma allfv_ren_lt i n M :
  i < n -> allfv (fun y : nat => y <> i) (ren (Nat.add n) M).
Proof.
  move=> ?. apply: allfv_ren. apply: allfv_trivial.
  move=> /=. lia.
Qed.

Module Confluence.
(* parallel reduction *)
Inductive par : term -> term -> Prop :=
  | par_var x : par (var x) (var x)
  | par_lam M M' : par M M' -> par (lam M) (lam M')
  | par_step M M' N N': par M M' -> par N N' -> par (app (lam M) N) (subst (scons N' var) M')
  | par_app M M' N N': par M M' -> par N N' -> par (app M N) (app M' N').

Lemma par_step' M M' N N' T : par M M' -> par N N' -> T = (subst (scons N' var) M') -> par (app (lam M) N) T.
Proof.
  intros ?? ->. now apply par_step.
Qed.

Lemma reflexive_par : reflexive term par.
Proof.
  intros M. now induction M; auto using par.
Qed.

Lemma inclusion_step_par : inclusion term step par.
Proof.
  intros M N H. now induction H; auto using par, reflexive_par.
Qed.

Lemma inclusion_par_steps : inclusion term par rt_steps.
Proof.
  intros M N H. induction H.
  - now apply rt_refl.
  - now apply stepsLam.
  - eapply rt_trans.
    + apply rt_step. now apply stepSubst.
    + apply steps_subst''; [|assumption].
      intros [|x]; [assumption|].
      apply rt_refl.
  - eapply rt_trans.
    + apply stepsAppL. eassumption.
    + apply stepsAppR. eassumption.
Qed.

Fixpoint rho (M : term) :=
  match M with
  | var x => var x
  | lam M => lam (rho M)
  | app (lam M) N => subst (scons (rho N) var) (rho M)
  | app M N => app (rho M) (rho N)
  end.

Lemma par_ren xi M M' : par M M' -> par (ren xi M) (ren xi M').
Proof.
  intros H. revert xi. induction H; intros xi; cbn.
  - now apply par_var.
  - now apply par_lam; auto.
  - eapply par_step'; [auto..|].
    rewrite ren_subst_term subst_ren_term.
    apply ext_subst_term. now intros [|x].
  - now apply par_app; auto.
Qed.

Lemma par_subst sigma sigma' M M' : (forall x, par (sigma x) (sigma' x)) -> par M M' -> par (subst sigma M) (subst sigma' M').
Proof.
  intros E H. revert sigma sigma' E.
  induction H as [x|M M' H IH|M M' N N' H1 IH1 H2 IH2|M M' N N' H1 IH1 H2 IH2].
  - intros ?? E. now apply E.
  - intros ?? E. cbn. apply par_lam. apply IH.
    intros [|x]; cbn.
    + now apply reflexive_par.
    + apply par_ren. now apply E.
  - intros ?? E. cbn. eapply (par_step' _ (subst (up sigma') M') _ (subst sigma' N')).
    + apply IH1. intros [|x]; cbn.
      * apply reflexive_par.
      * apply par_ren. apply E.
    + apply IH2. apply E.
    + rewrite !subst_subst_term. apply ext_subst_term. intros [|x]; cbn.
      * easy.
      * now rewrite subst_ren_term subst_var_term.
  - intros ?? E. cbn. apply par_app.
    + now apply IH1.
    + now apply IH2.
Qed.

Lemma tak_fun_par_rho : tak_fun term par rho.
Proof.
  intros M N H.
  induction H as [x|M M' H IH|M M' N N' H1 IH1 H2 IH2|M M' N N' H1 IH1 H2 IH2]; cbn.
  - now apply par_var.
  - now apply par_lam.
  - apply par_subst; [|assumption].
    intros [|x]; [assumption|].
    apply reflexive_par.
  - destruct M.
    + now apply par_app.
    + now apply par_app.
    + inversion H1. subst. apply par_step; [|assumption].
      inversion IH1. now subst.
Qed.
End Confluence.

Lemma confluence_step: confluent step.
Proof.
  eapply TMT.
  - apply Confluence.inclusion_step_par.
  - apply Confluence.inclusion_par_steps.
  - apply Confluence.reflexive_par.
  - apply Confluence.tak_fun_par_rho.
Qed.

Lemma steps_nf_elim {P : Prop} {M M' N : term} : normal_form N -> rt_steps M M' -> (rt_steps M' N -> P) -> rt_steps M N -> P.
Proof.
  move=> HN /confluence_step HM H /HM [N'] [H'] H''. apply: H.
  apply: rt_trans; first by eassumption.
  move: H'' HN => /clos_rt_rt1n_iff [].
  - move=> *. by apply: rt_refl.
  - by move=> > /normal_form_not_step.
Qed.

Lemma steps_var_elim {P : Prop} {M M' : term} {x : nat} : rt_steps M M' -> (rt_steps M' (var x) -> P) -> rt_steps M (var x) -> P.
Proof.
  apply: steps_nf_elim. by do 2 constructor.
Qed.

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
