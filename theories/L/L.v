(** * Halting problem for the call-by-value lambda-calculus HaltL  *)

(* * The call-by-value lambda calculus L *)

(* ** Syntax   *)

(* The terms of L are the terms of the full lambda-calculus, using de Bruijn encoding  *)
Inductive term : Type :=
| var (n : nat) : term
| app (s : term) (t : term) : term
| lam (s : term).

(* We define a simple, capturing substitution operation *)
Fixpoint subst (s : term) (k : nat) (u : term) :=
  match s with
      | var n => if Nat.eqb n k then u else var n
      | app s t => app (subst s k u) (subst t k u)
      | lam s => lam (subst s (S k) u)
  end.

(* ** Evaluation   *)

(* Big-step evaluation is weak (no evaluations below abstractions) and call-by-value (arguments are fully evaluated when pased) *)
Inductive eval : term -> term -> Prop :=
| eval_abs s : eval (lam s) (lam s)
| eval_app s u t t' v :
    eval s (lam u) -> eval t t' -> eval (subst u 0 t') v -> eval (app s t) v.

(* The L-halting problem  *)
Definition HaltL (s : term) := exists t, eval s t.

(* Scott encoding of natural numbers  *)
Fixpoint nat_enc (n : nat) := 
  match n with
  | 0 => lam (lam (var 1))
  | S n => lam (lam (app (var 0) (nat_enc n)))
  end.

(* ** L-computable relations  *)

Require Import Vector.

Definition L_computable {k} (R : Vector.t nat k -> nat -> Prop) := 
  exists s, forall v : Vector.t nat k, forall m,
        R v m <->
        eval (Vector.fold_left (fun s n => app s (nat_enc n)) s v) (nat_enc m).
