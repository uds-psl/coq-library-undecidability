(*
  Author(s):
    Andrej Dudenhefner (TU Dortmund University, Germany)

  Problem(s):
    Higher-Order Matching wrt. beta-equivalence (HOMbeta)

  Literature:
  [1] Loader, Ralph. "Higher order β-matching is undecidable." Logic Journal of the IGPL 11.1 (2003): 51-68.
*)

Require Import List Relation_Operators.

Require Undecidability.L.L Undecidability.LambdaCalculus.Lambda.

(* lambda-term syntax *)
Import L (term, var, app, lam).

(* beta-reduction (strong call-by-name reduction) *)
Import Lambda (step).

(* simple types with a single atom *)
Inductive ty : Type :=
  | atom (* type variable *)
  | arr (s t : ty). (* function type *)

(*
  simply typed lambda-calculus with a single atom
  "stlc Gamma M s" means that in the type environment Gamma the term M is assigned the type s
*)
Inductive stlc (Gamma : list ty) : term -> ty -> Prop :=
  | stlc_var x t : nth_error Gamma x = Some t -> stlc Gamma (var x) t
  | stlc_app M N s t : stlc Gamma M (arr s t) -> stlc Gamma N s -> stlc Gamma (app M N) t
  | stlc_lam M s t : stlc (cons s Gamma) M t -> stlc Gamma (lam M) (arr s t).

(* Higher-Order Matching wrt. beta-equivalence *)
Definition HOMbeta : { '(s, t, F, N) : (ty * ty * term * term) | stlc nil F (arr s t) /\ stlc nil N t } -> Prop :=
  (* given simply typed terms F : s -> t and N : t *)
  fun '(exist _ (s, t, F, N) _) =>
    (* is there a simply typed term M : s such that F A is beta-equivalent to B? *)
    exists (M : term), stlc nil M s /\ clos_refl_sym_trans term step (app F M) N.
