(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  Problem(s):
    Weak call-by-name leftmost outermost normalization for closed lambda-terms (wCBNclosed)
    Strong normalization for closed lambda-terms (SNclosed)

  Literature:
    [1] Plotkin, Gordon.
    "Call-by-name, call-by-value and the λ-calculus."
    Theoretical computer science 1.2 (1975): 125-159.
*)

Require Undecidability.L.L.
Import L (term, var, app, lam).

Require Import Relation_Operators.

(* function composition *)
Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y) :=
  fun x => g (f x).

Arguments funcomp {X Y Z} (g f) /.

(* stream cons *)
Definition scons {X : Type} (x : X) (xi : nat -> X) :=
  fun n => match n with | 0 => x | S n => xi n end.

(* parallel term renaming *)
Fixpoint ren (xi : nat -> nat) (t : term) : term  :=
  match t with
  | var x => var (xi x)
  | app s t => app (ren xi s) (ren xi t)
  | lam t => lam (ren (scons 0 (funcomp S xi)) t)
  end.

(* parallel term substitution *)
Fixpoint subst (sigma: nat -> term) (s: term) : term :=
  match s with
  | var n => sigma n
  | app s t => app (subst sigma s) (subst sigma t)
  | lam s => lam (subst (scons (var 0) (funcomp (ren S) sigma)) s)
  end.

Notation closed t := (forall (sigma: nat -> term), subst sigma t = t).

(* beta-reduction *)
Inductive step : term -> term -> Prop :=
  | stepSubst s t   : step (app (lam s) t) (subst (scons t var) s)
  | stepAppL s s' t : step s s' -> step (app s t) (app s' t)
  | stepAppR s t t' : step t t' -> step (app s t) (app s t')
  | stepLam s s'    : step s s' -> step (lam s) (lam s').

(* strong normalization of closed lambda-terms *)
Definition SNclosed : { s : term | closed s } -> Prop :=
  fun '(exist _ s _) => Acc (fun x y => step y x) s.

(* left-most outer-most call-by-name reduction on closed labda-terms *)
Inductive wCBN_step : term -> term -> Prop :=
  | wCBN_stepSubst s t  : wCBN_step (app (lam s) t) (subst (scons t var) s)
  | wCBN_stepApp s s' t : wCBN_step s s' -> wCBN_step (app s t) (app s' t).

(* weak call-by-name leftmost outermost normalization of closed lambda-terms *)
Definition wCBNclosed : { s : term | closed s } -> Prop :=
  fun '(exist _ s _) => exists t, clos_refl_trans term wCBN_step s (lam t).
