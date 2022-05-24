(*
  Problem(s):
    Weak call-by-name leftmost outermost normalization (wCBN)
    Weak call-by-name leftmost outermost normalization for closed terms (wCBNclosed)

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
Definition scons {X: Type} (x : X) (xi : nat -> X) :=
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

(* left-most outer-most call-by-name reduction *)
Inductive step : term -> term -> Prop :=
  | stepLam s t    : step (app (lam s) t) (subst (scons t var) s)
  | stepApp s s' t : step s s' -> step (app s t) (app s' t).

(* weak call-by-name leftmost outermost normalization *)
Definition wCBN : term -> Prop :=
  fun s => exists t, clos_refl_trans term step s t /\ forall u, not (step t u).

(* weak call-by-name leftmost outermost normalization of closed terms *)
Definition wCBNclosed : { s : term | forall sigma, subst sigma s = s } -> Prop :=
  fun '(exist _ s _) => exists t, clos_refl_trans term step s (lam t).
