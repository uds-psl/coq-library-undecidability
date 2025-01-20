(*
  Intersection Type Typability (type_assignment Gamma M t)
  implies P M for any admissible predicate P
*)

Require Import Undecidability.IntersectionTypes.CD Undecidability.IntersectionTypes.Util.CD_facts.
Require Import Undecidability.LambdaCalculus.Util.term_facts.
From Stdlib Require Import List.

Import L (term, var, app, lam).
Import Lambda (scons, funcomp, ren, subst).

From Stdlib Require Import ssreflect.

Set Default Goal Selector "!".

#[local] Unset Implicit Arguments.

Definition Arr (P Q : term -> Prop) (M : term) := forall N, P N -> Q (app M N).

#[local] Notation all P l := (fold_right and True (map P l)).

Fixpoint interp (P : term -> Prop) (M : term) (s : sty) : Prop :=
  match s with
  | atom a => P M
  | arr s phi t => Arr (fun N => (interp P N s /\ all (interp P N) phi)) (fun N => interp P N t) M
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

Lemma Forall_all {X : Type} {P : X -> Prop} l : Forall P l <-> all P l.
Proof.
  elim: l. { done. }
  move=> ?? IH. split.
  - by move=> /Forall_cons_iff [? /IH].
  - move=> [? ?]. constructor; first done. by apply /IH.
Qed.

Lemma Admissible_Saturated_interp {P} : Admissible P -> forall t, Saturated P (fun M => interp P M t).
Proof.
  move=> HP. elim /sty_ind'.
  { move=> x. constructor=> ?.
    - done.
    - by apply: (Admissible_neutral P HP). }
  move=> s phi t IHs IHphi IHt. constructor=> M /= HM.
  - have /HM : interp P (var 0) s /\ all (interp P (var 0)) phi.
    { split. 
      - apply: (Saturated_neutral IHs). by constructor.
      - apply /Forall_all. apply: Forall_impl IHphi=> ?.
        move=> /Saturated_neutral. apply. by constructor. }
    move=> /(Saturated_incl IHt). by apply: (Admissible_app_var P HP).
  - move=> N [+ _] => /(Saturated_incl IHs) ?.
    apply: (Saturated_neutral IHt). by constructor.
Qed.

Lemma interp_head_exp {P : term -> Prop} {M N t} : Admissible P ->
  head_exp P M N -> interp P M t -> interp P N t.
Proof.
  move=> HP. have HQ := Admissible_Saturated_interp HP. elim: t M N.
  { move=> *. apply: (Admissible_head_exp _ HP); eassumption. }
  move=> s ? phi t IH M N /= ? IH' N' [Hs Hphi].
  apply: IH. { constructor; [|apply: (Saturated_incl (HQ _))]; eassumption. }
  by apply: IH'.
Qed.

Definition satis (P : term -> Prop) (Gamma : list ty) M t :=
  forall sigma, (forall i s phi, nth_error Gamma i = Some (s, phi) -> interp P (sigma i) s /\ (Forall (interp P (sigma i)) phi)) ->
  interp P (subst sigma M) t.

Arguments satis P Gamma M !t /.

Lemma satisI P Gamma M t : Admissible P -> type_assignment Gamma M t -> satis P Gamma M t.
Proof.
  move=> HP. have HQ := Admissible_Saturated_interp HP.
  elim: M Gamma t.
  - move=> a > /type_assignmentE [] s phi Ha H.
    move=> sigma /(_ a _ _ Ha) [] /=.
    case: H. { by move=> <-. }
    by move=> + _ /Forall_forall {}H => /H.
  - move=> ? IH1 ? IH2 ?? /type_assignmentE [] s phi /IH1 /= {}IH1 /IH2 {}IH3 Hphi.
    move=> sigma Hsigma /=. apply: (IH1 sigma Hsigma). split.
    { by apply: IH3. }
    apply /Forall_all. apply: Forall_impl Hphi => ? /IH2. by apply.
  - move=> ? IH1 ? [?|s phi t] /type_assignmentE; first done.
    move=> /IH1 {}IH1 sigma HGamma /=.
    move=> N [Hs Hphi]. apply: (interp_head_exp HP).
    { apply: head_exp_lam. by apply: (Saturated_incl (HQ s)). }
    rewrite subst_subst_term. apply: IH1=> - [|i].
    + move=> /= ?? [<- <-]. by split; [|apply /Forall_all].
    + move=> ?? /HGamma => - [Hs' Hphi'] /=. by rewrite !simpl_term.
Qed.

(* fundamental theorem for admissible predicates *)
Theorem fundamental (P : term -> Prop) Gamma M t : Admissible P ->
  type_assignment Gamma M t -> P M.
Proof.
  move=> /[dup] HP /satisI /[apply] /(_ var).
  rewrite subst_var_term.
  have HQ := Admissible_Saturated_interp HP.
  move=> H. apply: (Saturated_incl (HQ _)).
  apply: H=> i *. have : neutral P (var i) by constructor.
  by split; [|apply /Forall_forall]=> *; apply: (Saturated_neutral (HQ _)).
Qed.
