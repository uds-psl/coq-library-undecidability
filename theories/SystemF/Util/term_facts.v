(* 
  Author(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax Undecidability.SystemF.Autosubst.unscoped.
Import UnscopedNotations.
From Undecidability.SystemF.Util Require Import Facts poly_type_facts pure_term_facts.

From Stdlib Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

Lemma subst_term_up_term_term_var {σ t}: subst_term σ (up_term_term var) t = subst_term σ var t.
Proof. apply: ext_term; [done | by case]. Qed.

Lemma subst_term_up_term_poly_type {σ τ t}: subst_term (up_term_poly_type σ) τ t = subst_term σ τ t.
Proof. 
  apply: ext_term; last done. 
  move=> ?. by rewrite /up_term_poly_type /funcomp /= ren_poly_type_id. 
Qed.

Lemma subst_term_up_poly_type_term_var {σ t}: subst_term σ (up_poly_type_term var) t = subst_term σ var t.
Proof. apply: ext_term; [done | by case]. Qed.

Lemma subst_term_poly_var_var {P} : subst_term poly_var var P = P.
Proof. by apply: idSubst_term. Qed.

Lemma subst_term_ren_term {σ σ' ξ ξ' P} : subst_term σ σ' (ren_term ξ ξ' P) = subst_term (ξ >> σ) (ξ' >> σ') P.
Proof. by apply: compRenSubst_term. Qed.

(* weaker, axiom-free replacement for asimpl; use: rewrite ?term_norm *)
Definition term_norm := (@subst_term_up_term_term_var, @subst_term_up_term_poly_type, @subst_term_up_poly_type_term_var, @subst_term_ren_term).

(* P is in head form if P = x A1 .. An *)
Inductive head_form : term -> Prop :=
  | head_form_var {x} : head_form (var x)
  | head_form_app {P Q} : head_form P -> normal_form Q -> head_form (app P Q)
  | head_form_ty_app {P t} : head_form P -> head_form (ty_app P t)
with normal_form : term -> Prop :=
  | normal_form_head_form {P} : head_form P -> normal_form P
  | normal_form_abs {s P} : normal_form P -> normal_form (abs s P)
  | normal_form_ty_abs {P} : normal_form P -> normal_form (ty_abs P).

(* mutual induction on head_form, normal_form *)
Scheme normal_form_ind' := Induction for normal_form Sort Prop
  with head_form_ind' := Induction for head_form Sort Prop.

Fact normal_form_ren_term {ζ ξ P} : 
  normal_form P -> normal_form (ren_term ζ ξ P).
Proof.
  move=> H. move: P H ζ ξ.
  apply: (normal_form_ind' 
    (fun P _ => forall ζ ξ, normal_form (ren_term ζ ξ P)) 
    (fun P _ => forall ζ ξ, head_form (ren_term ζ ξ P)));
      by eauto using normal_form, head_form.
Qed.

Fact head_form_ren_term {ζ ξ P} : 
  head_form P -> head_form (ren_term ζ ξ P).
Proof.
  move=> H. move: P H ζ ξ.
  apply: (head_form_ind' 
    (fun P _ => forall ζ ξ, normal_form (ren_term ζ ξ P)) 
    (fun P _ => forall ζ ξ, head_form (ren_term ζ ξ P)));
      by eauto using normal_form, head_form.
Qed.

(* type annotation erasure *)
Fixpoint erase (P: term) : pure_term :=
  match P with
  | var x => pure_var x
  | app P Q => pure_app (erase P) (erase Q)
  | abs _ P => pure_abs (erase P)
  | ty_app P _ => erase P
  | ty_abs P => erase P
  end.
  
Fact erase_subst_term_var {P σ} : erase (subst_term σ var P) = erase P.
Proof. 
  elim: P σ; move=> /= *; rewrite ?subst_term_up_term_term_var ?subst_term_up_poly_type_term_var; by congruence.
Qed.

(* COMPOUND term CONSTRUCTION *)
(* many_app P [Q1 .. Qn] = P Q1 .. Qn *)
Definition many_app (P: term) (Qs: list term) :=
  fold_left app Qs P.

(* many_app P [t1 .. tn] = P t1 .. tn *)
Definition many_ty_app (P: term) (ts: list poly_type) :=
  fold_left ty_app ts P.

(* many_ty_abs n P = Λ .. Λ t *)
Definition many_ty_abs (n: nat) (P: term) :=
  Nat.iter n ty_abs P.

Fact many_app_app {P Qs Qs'} : many_app P (Qs ++ Qs') = many_app (many_app P Qs) Qs'.
Proof. by rewrite /many_app fold_left_app. Qed.

Fact many_ty_app_app {P ts ts'} : many_ty_app P (ts ++ ts') = many_ty_app (many_ty_app P ts) ts'.
Proof. by rewrite /many_ty_app fold_left_app. Qed.

(* many_app M [N1 .. Nn] = M N1 .. Nn *)
Definition many_pure_app (M: pure_term) (Ns: list pure_term) :=
  fold_left pure_app Ns M.

Fact many_pure_app_app {M Ns Ns'} : 
  many_pure_app M (Ns ++ Ns') = many_pure_app (many_pure_app M Ns) Ns'.
Proof. by rewrite /many_pure_app fold_left_app. Qed.

Definition many_pure_term_abs (n: nat) (M: pure_term) :=
  Nat.iter n pure_abs M.

(* either a term or a type *)
Inductive argument : Type :=
  | argument_term : term -> argument
  | argument_poly_type : poly_type -> argument.

(* many_app P [A1 .. An] = P A1 .. An *)
Definition many_argument_app (P: term) (As: list argument) :=
  fold_left 
    (fun P A => 
      match A with
      | argument_term Q => app P Q
      | argument_poly_type t => ty_app P t
      end) 
    As P.

Fact many_argument_app_app {P As As'} : many_argument_app P (As ++ As') = many_argument_app (many_argument_app P As) As'.
Proof. by rewrite /many_argument_app fold_left_app. Qed.

(* a head form is a many_argument_app on a head variable *)
Lemma many_argument_appI {P} : head_form P -> 
  exists x As, P = many_argument_app (var x) As /\ Forall (fun A => if A is argument_term Q then normal_form Q else True) As.
Proof.
  elim.
  - move=> x. by exists x, [].
  - move=> {}P Q _ [x] [As] [-> HAs] ?. exists x, (As ++ [argument_term Q]).
    constructor; first by rewrite many_argument_app_app.
    rewrite Forall_app. constructor; [done | by constructor].
  - move=> {}P t _ [x] [As] [-> HAs]. exists x, (As ++ [argument_poly_type t]).
    constructor; first by rewrite many_argument_app_app.
    rewrite Forall_app. constructor; [done | by constructor].
Qed.

Fact erase_many_ty_abs {n P} : erase (many_ty_abs n P) = erase P.
Proof. elim: n => /= *; by congruence. Qed.

Fact erase_many_ty_app {ts P} : erase (many_ty_app P ts) = erase P.
Proof. elim: ts P; [done | by move=> > + ? /= => ->]. Qed.

Lemma erase_ren_term_id {ξ P} : erase (ren_term ξ id P) = erase P.
Proof.
  elim: P ξ.
  - done.
  - by move=> ? + ? + ? /= => -> ->.
  - move=> ? ? IH ? /=.
    under extRen_term => [? | ?] do [| rewrite /upRen_term_term up_ren_id].
    by rewrite IH.
  - by move=> ? + ? ? /= => ->.
  - by move=> ? + ? /= => ->.
Qed.

Fixpoint term_size (P: term) :=
  match P with
  | var _ => 1
  | app P Q => 1 + term_size P + term_size Q
  | abs _ P => 1 + term_size P
  | ty_app P _ => 1 + term_size P
  | ty_abs P => 1 + term_size P
  end.

Lemma term_size_pos (P: term) : term_size P = S (term_size P - 1).
Proof. case: P => /= *; by lia. Qed.

Fact term_size_ren_term {ζ ξ P} : term_size (ren_term ζ ξ P) = term_size P.
Proof. elim: P ζ ξ => /=; by congruence. Qed.

Lemma term_size_many_app_le P Qs : term_size P <= term_size (many_app P Qs).
Proof.
  elim: Qs P; first by move=> /=; lia.
  move=> Q Qs + P => /(_ (app P Q)) /=. by lia.
Qed.

Lemma many_argument_app_map_argument_poly_type {P ts} :
  many_argument_app P (map argument_poly_type ts) = many_ty_app P ts.
Proof. elim: ts P; [done | move=> /= *; by congruence]. Qed.

Lemma many_argument_app_map_argument_term {P Qs} :
  many_argument_app P (map argument_term Qs) = many_app P Qs.
Proof. elim: Qs P; [done | move=> /= *; by congruence]. Qed. 

Lemma normal_form_many_app {P Qs} : normal_form (many_app P Qs) -> normal_form P /\ Forall normal_form Qs.
Proof.
  elim /rev_ind: Qs P; first by (move=> *; constructor).
  move=> Q Qs IH P. rewrite many_app_app /=. 
  move H1P': (app _ _) => P' H2P'. case: H2P' H1P'; [|done|done].
  move=> ? []; [done| |done]. move=> ? ? /normal_form_head_form + + [? ?]. subst.
  move=> /IH [? ?] ?. constructor; first done.
  apply /Forall_app. constructor; first done.
  by constructor.
Qed.

(* evaluates propositional predicate P on all free variables *)
Fixpoint allfv_term (p: nat -> Prop) (P: term) :=
  match P with
  | var x => p x
  | app P Q => allfv_term p P /\ allfv_term p Q
  | abs _ P => allfv_term (scons True p) P
  | ty_app P _ => allfv_term p P
  | ty_abs P => allfv_term p P
  end.

Lemma allfv_term_impl {p1 p2: nat -> Prop} {P}: 
  (forall x, p1 x -> p2 x) -> allfv_term p1 P -> allfv_term p2 P.
Proof.
  elim: P p1 p2.
  - move=> >. by apply.
  - by move=> ? IH1 ? IH2 > /= /[dup] [/IH1 {}IH1 /IH2 {}IH2] [/IH1 ? /IH2 ?].
  - move=> > IH > H /=. apply: IH. by case.
  - move=> > IH > H /=. by apply: IH.
  - move=> > IH > H /=. by apply: IH.
Qed.

Lemma allfv_pure_term_erase {p P}:
  allfv_pure_term p (erase P) -> allfv_term p P.
Proof.
  elim: P p; [ done | | | done | done ].
  - by move=> ? IH1 ? IH2 > /= [/IH1 ? /IH2 ?].
  - by move=> > IH > /= /IH.
Qed.

Lemma erase_ren_term {ξ σ P} : erase (ren_term σ ξ P) = ren_pure_term ξ (erase P).
Proof.
  elim: P ξ σ.
  - done.
  - by move=> ? + ? + ? ? /= => -> ->.
  - by move=> ? ? + ? ? /= => ->.
  - done.
  - by move=> ? + ? ? /= => ->.
Qed.
