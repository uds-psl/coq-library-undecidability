(*
  facts about the simplty typed lambda-calculus
*)

From Stdlib Require Import Lia List Relations PeanoNat.
Import ListNotations.

Require Undecidability.L.L.
Import L (term, var, app, lam).

From Undecidability.LambdaCalculus Require Import Lambda HOMatching Util.facts Util.term_facts.
From Stdlib Require Import ssreflect ssrbool.

#[local] Unset Implicit Arguments.

Set Default Goal Selector "!".

#[local] Notation lams k M := (Nat.iter k lam M).
#[local] Notation apps M Ns := (fold_left app Ns M).
#[local] Notation arrs ss t := (fold_right arr t ss).
#[local] Notation steps := (clos_refl_trans _ step).

Fixpoint ty_size (t : ty) : nat :=
  match t with
  | atom => 1
  | arr s t => 1 + ty_size s + ty_size t
  end.

Lemma ty_size_arrs ss B : ty_size (arrs ss B) = list_sum (map (fun s => 1 + ty_size s) ss) + ty_size B.
Proof.
  elim: ss; first done.
  move=> ?? IH /=. rewrite IH /=. lia.
Qed.

Lemma arrs_inj s1s s2s t : arrs s1s t = arrs s2s t -> s1s = s2s.
Proof.
  elim: s1s s2s.
  - move=> [|??]; first done.
    move=> /= /(f_equal ty_size) /=. rewrite ty_size_arrs. lia.
  - move=> ?? IH [|??].
    + move=> /= /(f_equal ty_size) /=. rewrite ty_size_arrs. lia.
    + by move=> [<-] /IH <-.
Qed.

Lemma arrs_arrs s1s s2s t : arrs s1s (arrs s2s t) = arrs (s1s ++ s2s) t.
Proof.
  by rewrite fold_right_app.
Qed.

Inductive stlc_app_spec (Gamma : list ty) (t : ty) (M N : term) : Prop :=
  | stlc_app_spec_intro s : stlc Gamma M (arr s t) -> stlc Gamma N s -> stlc_app_spec Gamma t M N.
Inductive stlc_lam_spec (Gamma : list ty) (t : ty) (M : term) : Prop :=
  | stlc_lam_spec_intro s' t' : t = arr s' t' -> stlc (cons s' Gamma) M t' -> stlc_lam_spec Gamma t M.

Lemma stlcE Gamma M t : stlc Gamma M t ->
  match M with
  | var x => nth_error Gamma x = Some t
  | app M N => stlc_app_spec Gamma t M N
  | lam M => stlc_lam_spec Gamma t M
  end.
Proof. case; [|econstructor..]; by eauto. Qed.

Lemma stlc_appsE Gamma M Ns t : stlc Gamma (apps M Ns) t ->
  exists ss, Forall2 (stlc Gamma) Ns ss /\ stlc Gamma M (arrs ss t).
Proof.
  elim: Ns M t.
  - move=> M t /= ?. by exists [].
  - move=> N Ns IH M t /= /IH [ss] [?].
    move=> /stlcE [] s *. exists (s :: ss). by split; [constructor|].
Qed.

Lemma stlc_lamsE Gamma M ss B : stlc Gamma (lams (length ss) M) (arrs ss B) -> stlc (rev ss ++ Gamma) M B.
Proof.
  elim: ss Gamma; first done.
  move=> ?? IH ? /= /stlcE [] ?? [<- <-] /IH.
  by rewrite -app_assoc.
Qed.

Lemma stlc_lamsE' Gamma M n ss B : n = length ss -> stlc Gamma (lams n M) (arrs ss B) -> stlc (rev ss ++ Gamma) M B.
Proof. move=> ->. by apply: stlc_lamsE. Qed.

Lemma stlc_allfv_ren Gamma Delta xi M t : allfv (fun x => forall s, nth_error Gamma x = Some s -> nth_error Delta (xi x) = Some s) M ->
  stlc Gamma M t -> stlc Delta (ren xi M) t.
Proof.
  move=> + H. elim: H xi Delta.
  - move=> > ? > /= H. constructor. by apply: H.
  - move=> > ? IH1 ? IH2 > /= [] /IH1 {}IH1 /IH2 {}IH2.
    econstructor; by eassumption.
  - move=> > ? IH > /= H. constructor.
    apply: IH. by apply: allfv_impl H => - [|?] /=.
Qed.

Lemma stlc_ren Gamma Delta xi M t : (forall x s, nth_error Gamma x = Some s -> nth_error Delta (xi x) = Some s) ->
  stlc Gamma M t -> stlc Delta (ren xi M) t.
Proof.
  move=> ?. apply: stlc_allfv_ren. by apply: allfv_trivial.
Qed.

(* typing is preserved under substitutions *)
Theorem stlc_subst {Gamma Delta M t} sigma :
  stlc Gamma M t ->
  (forall n s, nth_error Gamma n = Some s -> stlc Delta (sigma n) s) ->
  stlc Delta (subst sigma M) t.
Proof.
  move=> H. elim: H Delta sigma.
  - move=> > ??? H /=. by apply: H.
  - move=> > ? IH1 ? IH2 > H /=. econstructor.
    + by apply: IH1.
    + by apply: IH2.
  - move=> > ? IH > H /=. constructor.
    apply: IH=> - [|n] /=.
    + move=> ? [<-]. by constructor.
    + move=> ? /H ?. by apply: stlc_ren; last by eassumption.
Qed.

Lemma stlc_step Gamma M N t : step M N -> stlc Gamma M t -> stlc Gamma N t.
Proof.
  move=> H. elim: H Gamma t.
  - move=> > /stlcE [] ? /stlcE [] ?? [<- <-] H1 H2.
    apply: stlc_subst; first by eassumption.
    move=> [|?] ? /=.
    + by move=> [<-].
    + by apply: stlc_var.
  - move=> > ? IH > /stlcE [] ? /IH ??. by apply: stlc_app; eassumption.
  - move=> > ? IH > /stlcE [] ?? /IH ?. by apply: stlc_app; eassumption.
  - move=> > ? IH > /stlcE [] ?? -> /IH ?. by constructor.
Qed.

(* subject reduction *)
Lemma stlc_steps Gamma M N t : steps M N -> stlc Gamma M t -> stlc Gamma N t.
Proof.
  by elim=> >; [apply: stlc_step|auto..].
Qed.

Lemma stlc_allfv_not_None Gamma M t :
  stlc Gamma M t ->
  allfv (fun x => nth_error Gamma x <> None) M.
Proof.
  elim.
  - by move=> > /= ->.
  - by move=> > /=.
  - move=> > /= ?. by apply: allfv_impl => -[|?].
Qed.

Lemma stlc_lams Gamma k M ss t : length ss = k -> stlc (rev ss ++ Gamma) M t -> stlc Gamma (lams k M) (arrs ss t).
Proof.
  elim: k ss Gamma t; first by case.
  move=> k IH [|? ss] Gamma t /=; first done.
  move=> [/IH]. rewrite -app_assoc=> /[apply]. by apply: stlc_lam.
Qed.

Lemma stlc_apps Gamma M Ms ss t : stlc Gamma M (arrs ss t) -> Forall2 (stlc Gamma) Ms ss -> stlc Gamma (apps M Ms) t.
Proof.
  move=> + H. elim: H M t; first done.
  move=> M' s' {}Ms {}ss ?? IH M t /= H. apply IH.
  by apply: stlc_app; first eassumption.
Qed.

Lemma stlc_closed M t : stlc [] M t -> forall P, allfv P M.
Proof.
  move=> /stlc_allfv_not_None H ?. apply: allfv_impl H. by case.
Qed.

Lemma ext_stlc_subst_term {Gamma M A sigma1 sigma2} : (forall x, nth_error Gamma x <> None -> sigma1 x = sigma2 x) -> stlc Gamma M A -> subst sigma1 M = subst sigma2 M.
Proof.
  move=> H' /stlc_allfv_not_None H. apply: ext_allfv_subst_term. by apply: allfv_impl H.
Qed.

Module Fundamental.

Definition Arr (P Q : term -> Prop) (M : term) := forall N, P N -> Q (app M N).

#[local] Notation all P l := (fold_right and True (map P l)).

Fixpoint interp (P : term -> Prop) (M : term) (s : ty) : Prop :=
  match s with
  | atom => P M
  | arr s t => Arr (fun N => interp P N s) (fun N => interp P N t) M
  end.

(* P-compatible head expansion *)
Inductive head_exp (P : term -> Prop) : term -> term -> Prop :=
  | head_exp_lam M N : P N -> head_exp P (subst (scons N var) M) (app (lam M) N)
  | head_exp_app M M' N : head_exp P M M' -> P N -> head_exp P (app M N) (app M' N).

Record Saturated (Q P : term -> Prop) :=
  { Saturated_incl : forall M, P M -> Q M;
    Saturated_neutral : forall M, neutral Q M -> P M }.

Arguments Saturated_incl {Q P}.
Arguments Saturated_neutral {Q P}.

Record Admissible (P : term -> Prop) :=
  { Admissible_head_exp M N : head_exp P M N -> P M -> P N;
    Admissible_neutral M : neutral P M -> P M;
    Admissible_app_var M x : P (app M (var x)) -> P M }.

Lemma head_expE (P : term -> Prop) M N : head_exp P M N ->
  match N with
  | var _ => False
  | app N1 N2 =>
      (exists N1', N1 = lam N1' /\ M = (subst (scons N2 var) N1') /\ P N2) \/
      (exists M1, M = app M1 N2 /\ head_exp P M1 N1 /\ P N2) 
  | lam _ => False
  end.
Proof.
  case=> *; [left|right]; by do ? econstructor.
Qed.

Lemma Admissible_Saturated_interp {P} : Admissible P -> forall t, Saturated P (fun M => interp P M t).
Proof.
  move=> HP. elim.
  { constructor=> ?.
    - done.
    - by apply: (Admissible_neutral P HP). }
  move=> s IHs t IHt. constructor=> M /= HM.
  - have /HM : interp P (var 0) s.
    { apply: (Saturated_neutral IHs). by constructor. }
    move=> /(Saturated_incl IHt). by apply: (Admissible_app_var P HP).
  - move=> N /(Saturated_incl IHs) ?.
    apply: (Saturated_neutral IHt). by constructor.
Qed.

Lemma interp_head_exp {P : term -> Prop} {M N t} : Admissible P ->
  head_exp P M N -> interp P M t -> interp P N t.
Proof.
  move=> HP. have HQ := Admissible_Saturated_interp HP. elim: t M N.
  { move=> *. apply: (Admissible_head_exp _ HP); eassumption. }
  move=> s IH t IH' M N /= ? IH'' N' Hs.
  apply: IH'. { constructor; [|apply: (Saturated_incl (HQ _))]; eassumption. }
  by apply: IH''.
Qed.

Definition satis (P : term -> Prop) (Gamma : list ty) M t :=
  forall sigma, (forall i s, nth_error Gamma i = Some s -> interp P (sigma i) s) ->
  interp P (subst sigma M) t.

Arguments satis P Gamma M !t /.

Lemma satisI P Gamma M t : Admissible P -> stlc Gamma M t -> satis P Gamma M t.
Proof.
  move=> HP. have HQ := Admissible_Saturated_interp HP. elim.
  - move=> > + sigma H => /H. apply.
  - move=> > ? IH1 ? IH2 sigma H /=. apply: (IH1 sigma H). by apply IH2.
  - move=> > ? IH sigma H /= N HN. apply: (interp_head_exp HP).
    + apply: head_exp_lam. apply: (Saturated_incl (HQ _)). by eassumption.
    + rewrite subst_subst_term. apply: IH=> - [|i] /=.
      * by move=> ? [<-].
      * move=> ? /H. by rewrite subst_ren_term subst_var_term.
Qed.

(* fundamental theorem for admissible predicates *)
Theorem fundamental (P : term -> Prop) Gamma M t : Admissible P ->
  stlc Gamma M t -> P M.
Proof.
  move=> /[dup] HP /satisI /[apply] /(_ var).
  rewrite subst_var_term.
  have HQ := Admissible_Saturated_interp HP.
  move=> H. apply: (Saturated_incl (HQ _)).
  apply: H=> i *. have : neutral P (var i) by constructor.
  by apply: (Saturated_neutral (HQ _)).
Qed.

End Fundamental.

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

Lemma head_exp_step M N : Fundamental.head_exp wn M N -> step N M.
Proof.
  elim. { move=> *. by apply: stepSubst. }
  move=> *. by apply: stepAppL.
Qed.

Lemma step_wn M N : step M N -> wn N -> wn M.
Proof.
  move=> ? [???]. econstructor; [|eassumption].
  by apply: rt_trans; [apply: rt_step|]; eassumption.
Qed.

Lemma head_exp_wn M N : Fundamental.head_exp wn M N -> wn M -> wn N.
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

Lemma Admissible_wn : Fundamental.Admissible wn.
Proof.
  constructor.
  - by apply: head_exp_wn.
  - by apply: neutal_wn_wn.
  - by apply: wn_app_var.
Qed.

End Admissible_wn.

(* weak normalization property of stlc *)
Lemma stlc_wn Gamma M t : stlc Gamma M t -> wn M.
Proof.
  apply: Fundamental.fundamental.
  by apply: Admissible_wn.Admissible_wn.
Qed.
