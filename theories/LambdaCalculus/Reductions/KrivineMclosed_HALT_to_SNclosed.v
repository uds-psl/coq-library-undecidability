(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  Reduction from:
    Krivine machine halting for closed terms (KrivineMclosed_HALT)
  to:
    Strong normalization for closed lambda-terms (SNclosed)
*)

Require Undecidability.L.L.
From Undecidability.LambdaCalculus Require Import Krivine Lambda Util.Krivine_facts.
Require Import Undecidability.LambdaCalculus.Util.term_facts.
Require Import Undecidability.Shared.simulation.
Require Import Relations List.

Import L (term, var, app, lam).
Import ListNotations TermNotations.

Require Import ssreflect.

Set Default Goal Selector "!".

Lemma t_step' {X : Type} (R : X -> X -> Prop) x y z :
  R x y -> clos_refl_trans _ R y z -> clos_trans _ R x z.
Proof.
  move=> H /clos_rt_rt1n_iff H'.
  elim: H' x H; by eauto using clos_trans.
Qed.

Lemma rt_step' {X : Type} (R : X -> X -> Prop) x y z :
  R x y -> clos_refl_trans _ R y z -> clos_refl_trans _ R x z.
Proof. by eauto using clos_refl_trans. Qed.

(* left-most outer-most call-by-name reduction on closed terms *)
Inductive step' : term -> term -> Prop :=
  | step'Lam s t    : normal_form s -> normal_form t -> step' (app (lam s) t) (subst (scons t (fun x => var x)) s)
  | step'App s s' t : normal_form t -> step' s s' -> step' (app s t) (app s' t).

#[local] Notation steps' := (clos_trans _ step').

Lemma step'E M N : step' M N ->
  match M with
  | var _ => False
  | app M1 M2 => normal_form M2 /\
    match M1 with
    | var _ => False
    | app _ _ => exists M', step' M1 M'
    | lam M3 => normal_form M3 /\ N = (subst (scons M2 var) M3)
    end
  | lam _ => False
  end.
Proof.
  case; [tauto|case].
  - move=> > _ H. inversion H.
  - move=> *. split; [|eexists]; eassumption.
  - move=> > _ H. inversion H.
Qed.

Lemma step'_step_det M N : step' M N -> forall N', step M N' -> N = N'.
Proof.
  elim.
  - move=> {}M {}N HM HN N'.
    move E: (app (lam M) N) => M' H. case: H E.
    + congruence.
    + move=> > /normal_form_not_step H [] ??. subst.
      case: H. by constructor.
    + move=> > /normal_form_not_step H [] ??. by subst.
    + done.
  - move=> M1 M2 {}N HN HM1M2 HM1 N'.
    move E: (app M1 N) => M' H. case: H E.
    + move=> > [] ??. subst.
      by move=> /step'E in HM1M2.
    + move=> > H [] ??. subst. congr app.
      by apply: HM1.
    + move=> > /normal_form_not_step ? [] ??. by subst.
    + done.
Qed.

Lemma step'_step M N : step' M N -> step M N.
Proof.
  elim=> *.
  - by apply: stepSubst.
  - by apply: stepAppL.
Qed.

Lemma step'_det M N N' : step' M N -> step' M N' -> N = N'.
Proof.
  move=> /step'_step_det H /step'_step. by apply: H.
Qed.

Lemma step'_uc : uniformly_confluent step'.
Proof.
  move=> ??? /step'_det /[apply] <-. by left.
Qed.

#[local] Notation I := (lam (var 0)).

(* all encodings get I as a final argument to ensure redex uniqueness *)
#[local] Notation call Ns := (lam (many_app (var 0) (Ns ++ [var 0]))).

Fixpoint enc_nat (n : nat) : term :=
  match n with
  | 0 => lam (lam (call [var 2]))
  | S n => lam (lam (call [var 1; enc_nat n]))
  end.

Fixpoint enc_term (M : term) :=
  match M with
  | var x => lam (lam (lam (call [var 3; enc_nat x])))
  | app M N => lam (lam (lam (call [var 2; enc_term M; enc_term N])))
  | lam M => lam (lam (lam (call [var 1; enc_term M])))
  end.

Definition enc_list {X : Type} (f : X -> term) :=
  fix rec (l : list X) :=
    match l with
    | nil => lam (lam (call [var 2]))
    | cons x l => lam (lam (call [var 1; f x; rec l]))
    end.

Fixpoint enc_eterm (P : eterm) :=
  match P with
  | closure Ps M => lam (call [var 1; enc_list enc_eterm Ps; enc_term M])
  end.

Lemma normal_form_enc_nat n : normal_form (enc_nat n).
Proof. elim: n; by do ? constructor. Qed.

#[local] Hint Resolve normal_form_enc_nat : core.

Lemma normal_form_enc_term M : normal_form (enc_term M).
Proof. elim: M; by do ? constructor. Qed.

#[local] Hint Resolve normal_form_enc_term : core.

Lemma normal_form_enc_list {X: Type} (f : X -> term) l : (forall x, normal_form (f x)) -> normal_form (enc_list f l).
Proof. move=> Hf. elim: l; by do ? constructor. Qed.

Lemma normal_form_enc_eterm P : normal_form (enc_eterm P).
Proof.
  elim /Krivine_facts.eterm_ind': P.
  move=> ?? H /=. do ? constructor; [|done].
  elim: H; by do ? constructor.
Qed.

#[local] Hint Resolve normal_form_enc_eterm : core.

Lemma normal_form_enc_eterms Ps : normal_form (enc_list enc_eterm Ps).
Proof. by apply: normal_form_enc_list. Qed.

#[local] Hint Resolve normal_form_enc_eterms : core.

Lemma ren_enc_nat xi n : ren xi (enc_nat n) = enc_nat n.
Proof. elim: n xi; cbn; congruence. Qed.

Lemma subst_enc_nat sigma n : subst sigma (enc_nat n) = enc_nat n.
Proof. elim: n sigma; cbn; congruence. Qed.

Lemma ren_enc_term xi M : ren xi (enc_term M) = enc_term M.
Proof. elim: M xi; intros; cbn; rewrite ?ren_enc_nat; congruence. Qed.

Lemma subst_enc_term sigma M : subst sigma (enc_term M) = enc_term M.
Proof. elim: M sigma; intros; cbn; rewrite ?subst_enc_nat; congruence. Qed.

Lemma ren_enc_list {X: Type} (f : X -> term) xi l : (Forall (fun x => forall xi, ren xi (f x) = f x) l) ->
  ren xi (enc_list f l) = enc_list f l.
Proof. move=> H. elim: H xi; cbn; congruence. Qed.

Lemma subst_enc_list {X: Type} (f : X -> term) sigma l : (Forall (fun x => forall sigma, subst sigma (f x) = f x) l) ->
  subst sigma (enc_list f l) = enc_list f l.
Proof. move=> H. elim: H sigma; cbn; congruence. Qed.

Lemma ren_enc_eterm xi P : ren xi (enc_eterm P) = enc_eterm P.
Proof.
  elim /Krivine_facts.eterm_ind': P xi.
  move=> Ps t IH xi /=.
  do ? congr lam. do ? congr app.
  - by apply: ren_enc_list.
  - by apply: ren_enc_term.
Qed.

Lemma subst_enc_eterm sigma P : subst sigma (enc_eterm P) = enc_eterm P.
Proof.
  elim /Krivine_facts.eterm_ind': P sigma.
  move=> Ps t IH xi /=.
  do ? congr lam. do ? congr app.
  - by apply: subst_enc_list.
  - by apply: subst_enc_term.
Qed.

Lemma ren_enc_eterms xi l : ren xi (enc_list enc_eterm l) = enc_list enc_eterm l.
Proof. apply: ren_enc_list. apply /Forall_forall=> *. by apply: ren_enc_eterm. Qed.

Lemma subst_enc_eterms sigma l : subst sigma (enc_list enc_eterm l) = enc_list enc_eterm l.
Proof. apply: subst_enc_list. apply /Forall_forall=> *. by apply: subst_enc_eterm. Qed.

Definition subst_enc := (
  subst_enc_eterms, subst_enc_eterm, subst_enc_term, subst_enc_nat,
  ren_enc_eterms, ren_enc_eterm, ren_enc_term, ren_enc_nat).

Definition enc_halt_cbn_var0 :=
  (* ts ctx rec *)
  lam (lam (lam (
    call [var 2;
      I; (* nil case *)
      lam (lam (call [var 2; lam (lam (call [var 7; var 9; var 2; var 1; var 7]))])) (* cons case *)
    ]))).

Definition enc_halt_cbn_varS :=
  (* ts ctx x rec *)
  lam (lam (lam (lam (
    call [var 3;
      I; (* nil case *)
      lam (lam (call [var 4; var 7; var 1; lam (lam (lam (call [var 3; var 9]))); var 4])) (* cons case *)
    ])))).

Definition enc_halt_cbn_app :=
  (* ts ctx s t rec *)
  lam (lam (lam (lam (lam (
    call [var 1; lam (lam (call [var 1; lam (call [var 1; var 9; var 7]); var 8])); var 4; var 3; var 1]
    ))))).

Definition enc_halt_cbn_lam :=
  (* ts ctx s rec *)
  lam (lam (lam (lam (
    call [var 4;
      (* nil case *)
      I;
      (* cons case *)
      lam (lam (call [var 4; var 1; lam (lam (call [var 1; var 5; var 9])); var 5; var 4]))
    ])))).

Lemma enc_halt_cbn_var0_spec ts ctx t ctx' rec :
  normal_form rec ->
  (forall xi, ren xi rec = rec) ->
  (forall sigma, subst sigma rec = rec) ->
  clos_refl_trans _ step'
    (many_app enc_halt_cbn_var0 [enc_list enc_eterm ts; enc_list enc_eterm ((closure ctx t)::ctx'); rec; I])
    (many_app rec [enc_list enc_eterm ts; enc_list enc_eterm ctx; enc_term t; rec; I]).
Proof.
  move=> H1r H2r H3r.
  do ? (apply: rt_step'; [by do ? constructor|]; rewrite /= ?subst_enc ?H2r ?H3r).
  by apply: rt_refl.
Qed.

Lemma enc_halt_cbn_varS_spec ts P ctx x rec : 
  normal_form rec ->
  (forall xi, ren xi rec = rec) ->
  (forall sigma, subst sigma rec = rec) ->
  clos_refl_trans _ step'
    (many_app enc_halt_cbn_varS [enc_list enc_eterm ts; enc_list enc_eterm (P::ctx); enc_nat x; rec; I])
    (many_app rec [enc_list enc_eterm ts; enc_list enc_eterm ctx; enc_term (var x); rec; I]).
Proof.
  move=> H1r H2r H3r.
  do ? (apply: rt_step'; [by do ? constructor|]; rewrite /= ?subst_enc ?H2r ?H3r).
  by apply: rt_refl.
Qed.

Lemma enc_halt_cbn_app_spec ts ctx s t rec : 
  normal_form rec ->
  (forall xi, ren xi rec = rec) ->
  (forall sigma, subst sigma rec = rec) ->
  clos_refl_trans _ step'
    (many_app enc_halt_cbn_app [enc_list enc_eterm ts; enc_list enc_eterm ctx; enc_term s; enc_term t; rec; I])
    (many_app rec [enc_list enc_eterm ((closure ctx t)::ts); enc_list enc_eterm ctx; enc_term s; rec; I]).
Proof.
  move=> H1r H2r H3r.
  do ? (apply: rt_step'; [by do ? constructor|]; rewrite /= ?subst_enc ?H2r ?H3r).
  by apply: rt_refl.
Qed.

Lemma enc_halt_cbn_lam_spec ts ctx s t rec : 
  normal_form rec ->
  (forall xi, ren xi rec = rec) ->
  (forall sigma, subst sigma rec = rec) ->
  clos_refl_trans _ step'
    (many_app enc_halt_cbn_lam [enc_list enc_eterm (t::ts); enc_list enc_eterm ctx; enc_term s; rec; I])
    (many_app rec [enc_list enc_eterm ts; enc_list enc_eterm (t::ctx); enc_term s; rec; I]).
Proof.
  move=> H1r H2r H3r.
  do ? (apply: rt_step'; [by do ? constructor|]; rewrite /= ?subst_enc ?H2r ?H3r).
  by apply: rt_refl.
Qed.

Lemma enc_halt_cbn_lam_spec' ctx s rec : 
  normal_form rec ->
  (forall xi, ren xi rec = rec) ->
  (forall sigma, subst sigma rec = rec) ->
  clos_refl_trans _ step'
    (many_app enc_halt_cbn_lam [enc_list enc_eterm nil; enc_list enc_eterm ctx; enc_term s; rec; I])
    I.
Proof.
  move=> H1r H2r H3r.
  do ? (apply: rt_step'; [by do ? constructor|]; rewrite /= ?subst_enc ?H2r ?H3r).
  by apply: rt_refl.
Qed.

Definition enc_halt_cbn : term :=
  (* ts ctx t rec *)
  lam (lam (lam (lam (
    call [var 2 (*t*);
      (* var case *)
      lam (call [var 1;
        (* var 0 case *)
        call [enc_halt_cbn_var0; var 7 (*ts*); var 6 (*ctx*); var 4 (*rec*)];
        (* var (S x) case *)
        lam (call [enc_halt_cbn_varS; var 8 (*ts*); var 7 (*ctx*); var 1 (*x*); var 5 (*rec*)])
        ]);
      (* app case *)
      lam (lam (call [enc_halt_cbn_app; var 7 (*ts*); var 6 (*ctx*); var 2 (*s*); var 1 (*t*); var 4 (*rec*)]));
      (* lam case *)
      lam (call [enc_halt_cbn_lam; var 6 (*ts*); var 5 (*ctx*); var 1 (*s*); var 3 (*rec*)])
      ])))).

Lemma normal_form_enc_halt_cbn_var0 : normal_form enc_halt_cbn_var0.
Proof. by do ? constructor. Qed.

Lemma normal_form_enc_halt_cbn_varS : normal_form enc_halt_cbn_varS.
Proof. by do ? constructor. Qed.

Lemma normal_form_enc_halt_cbn_app : normal_form enc_halt_cbn_app.
Proof. by do ? constructor. Qed.

Lemma normal_form_enc_halt_cbn_lam : normal_form enc_halt_cbn_lam.
Proof. by do ? constructor. Qed.

Lemma ren_enc_halt_cbn xi : ren xi enc_halt_cbn = enc_halt_cbn.
Proof. done. Qed.

Lemma subst_enc_halt_cbn sigma : subst sigma enc_halt_cbn = enc_halt_cbn.
Proof. done. Qed.

Lemma subst_enc_halt_cbn_var0 sigma : subst sigma enc_halt_cbn_var0 = enc_halt_cbn_var0.
Proof. done. Qed.

Lemma subst_enc_halt_cbn_varS sigma : subst sigma enc_halt_cbn_varS = enc_halt_cbn_varS.
Proof. done. Qed.

Lemma subst_enc_halt_cbn_app sigma : subst sigma enc_halt_cbn_app = enc_halt_cbn_app.
Proof. done. Qed.

Lemma subst_enc_enc_halt_cbn_lam sigma : subst sigma enc_halt_cbn_lam = enc_halt_cbn_lam.
Proof. done. Qed.

Definition simpl_term := (
  subst_enc,
  subst_enc_halt_cbn_var0, subst_enc_halt_cbn_varS, subst_enc_halt_cbn_app, subst_enc_enc_halt_cbn_lam).

#[local] Hint Resolve
  normal_form_enc_halt_cbn_var0
  normal_form_enc_halt_cbn_varS
  normal_form_enc_halt_cbn_app
  normal_form_enc_halt_cbn_lam
    : core.

Opaque enc_halt_cbn_var0 enc_halt_cbn_varS enc_halt_cbn_app enc_halt_cbn_lam.
Opaque enc_eterm enc_list.

#[local] Notation enc_state ts ctx t :=
  (many_app enc_halt_cbn [enc_list enc_eterm ts; enc_list enc_eterm ctx; enc_term t; enc_halt_cbn; I]).

Inductive sync : (list eterm * list eterm * term) -> term -> Prop :=
  sync_intro ts ctx t : sync (ts, ctx, t) (enc_state ts ctx t).

Lemma syncE X X' : sync X X' ->
  match X with
  | (ts, ctx, t) => X' = many_app enc_halt_cbn [enc_list enc_eterm ts; enc_list enc_eterm ctx; enc_term t; enc_halt_cbn; I]
  end.
Proof. by case. Qed.

Lemma Krivine_step_dec X : (exists Y, Krivine_step X Y) \/ (stuck Krivine_step X).
Proof.
  move: X => [[ts ctx] t].
  move: t => [[|?]|??|?].
  - move: ctx => [|[??]?].
    + right. move=> ? H. by inversion H.
    + left. eexists. by constructor.
  - move: ctx=> [|??].
    + right. move=> ? H. by inversion H.
    + left. eexists. by constructor.
  - left. eexists. by constructor.
  - move: ts => [|??].
    + right. move=> ? H. by inversion H.
    + left. eexists. by constructor.
Qed.

Lemma Krivine_step_steps' X Y X' :
  Krivine_step X Y ->
  sync X X' ->
  exists Y', steps' X' Y' /\ sync Y Y'.
Proof.
  have := subst_enc_halt_cbn.
  have := ren_enc_halt_cbn.
  move E: enc_halt_cbn => rec.
  have H'rec : normal_form rec by (rewrite -E; do ? constructor).
  move=> H1rec H2rec.
  case=> > /syncE ->; eexists; (split; [|by apply: sync_intro]); rewrite !E.
  all: rewrite -[l in steps' (many_app l _) _]E /enc_halt_cbn.
  - do ? ((apply: rt_step' || apply: t_step'); [by do ? constructor|]; rewrite /= ?simpl_term ?H1rec ?H2rec).
    by apply: enc_halt_cbn_var0_spec.
  - do ? ((apply: rt_step' || apply: t_step'); [by do ? constructor|]; rewrite /= ?simpl_term ?H1rec ?H2rec).
    by apply: enc_halt_cbn_varS_spec.
  - do ? ((apply: rt_step' || apply: t_step'); [by do ? constructor|]; rewrite /= ?simpl_term ?H1rec ?H2rec).
    by apply: enc_halt_cbn_app_spec.
  - do ? ((apply: rt_step' || apply: t_step'); [by do ? constructor|]; rewrite /= ?simpl_term ?H1rec ?H2rec).
    by apply: enc_halt_cbn_lam_spec.
Qed.

Lemma subst_enc_state ts ctx t sigma : subst sigma (enc_state ts ctx t) = enc_state ts ctx t.
Proof. by rewrite /= ?simpl_term. Qed.

Lemma halt_cbn_rt_step' ts ctx t :
  halt_cbn ts ctx t -> clos_refl_trans _ step' (enc_state ts ctx t) I.
Proof.
  move=> /halt_cbn_Krivine_step.
  move=> [ctx'] [t'] /(clos_refl_trans_transport Krivine_step_steps' (sync_intro _ _ _)) [?] [/syncE] -> ?.
  apply: rt_trans; [eassumption|].
  have := subst_enc_halt_cbn.
  have := ren_enc_halt_cbn.
  move E: enc_halt_cbn => rec.
  have H'rec : normal_form rec by (rewrite -E; do ? constructor).
  move=> H1rec H2rec.
  rewrite -[l in many_app l _]E /enc_halt_cbn.
  do ? (apply: rt_step'; [by do ? constructor|]; rewrite /= ?simpl_term ?H1rec ?H2rec).
  by apply: enc_halt_cbn_lam_spec'.
Qed.

Lemma step'_step_SN t : clos_refl_trans _ step' t I -> Acc (fun x y => step y x) t.
Proof.
  move E: (I) => t' /clos_rt_rt1n_iff H. elim: H E.
  - move=> ? <-. constructor. move=> ?.
    move E: (I) => ? H. exfalso. case: H E=> //.
    by move=> > [].
  - move=> > /step'_step_det H _ IH ?. subst. constructor.
    move=> ? /H <-. by apply: IH.
Qed.

Lemma step'_dec s : (exists t, step' s t) \/ not (exists t, step' s t).
Proof.
  elim: s.
  - move=> ?. right. by move=> [?] /step'E.
  - move=> [?|s1 s2|{}s] IHs {}t _.
    + right. by move=> [?] /step'E [].
    + have [?|?] := normal_form_dec t; first last.
      { right. move=> [?] /step'E. tauto. }
      move: IHs => [[?] IHs|IHs].
      * left. eexists. constructor; eassumption.
      * right. by move=> [?] /step'E [?] /IHs.
    + have [?|?] := normal_form_dec t; first last.
      { right. move=> [?] /step'E. tauto. }
      have [?|?] := normal_form_dec s; first last.
      { right. move=> [?] /step'E. tauto. }
      left. eexists. by constructor.
  - move=> ??. right. by move=> [?] /step'E.
Qed.

Lemma SN_terminates_step' t : Acc (fun x y => step y x) t -> terminates step' t.
Proof.
  elim=> {}t _ IH. case: (step'_dec t).
  - move=> [t'] /[dup] H /step'_step /IH [?] [??].
    eexists. split; [|eassumption].
    apply: rt_trans; [apply: rt_step|]; eassumption.
  - move=> H. exists t. split; [apply: rt_refl|].
    move=> ??. apply: H. eexists. eassumption.
Qed.

Require Import Undecidability.Synthetic.Definitions.

(* reduction from Krivine machine halting to strong normalization *)
Theorem reduction : KrivineMclosed_HALT ⪯ SNclosed.
Proof.
  exists (fun '(exist _ t _) => exist _ _ (subst_enc_state nil nil t)).
  move=> [t Ht] /=. split.
  - move=> ?. apply: step'_step_SN. by apply: halt_cbn_rt_step'.
  - move=> /SN_terminates_step'.
    move=> /(terminates_reflection step'_uc Krivine_step_steps' Krivine_step_dec (sync_intro _ _ _)).
    move=> [[[ts' ctx'] t']] [].
    move=> /Krivine_step_halt_cbn'. apply; [by constructor|].
    split; [|done].
    apply /L_facts.closed_dcl. apply: term_facts.closed_I=> k.
    by rewrite term_facts.L_subst_Lambda_subst; [|apply: Ht].
Qed.
