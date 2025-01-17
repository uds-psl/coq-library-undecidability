(* 
  Problem(s):
    System F Type Checking (SysF_TC)
    System F Typability (SysF_TYP)
    System F Inhabitation (SysF_INH)
*)

(*
  Literature:
  [1] Andrej Dudenhefner and Jakob Rehof. 
      "A Simpler Undecidability Proof for System F Inhabitation." 
      24th International Conference on Types for Proofs and Programs (TYPES 2018). 
      Schloss Dagstuhl-Leibniz-Zentrum fuer Informatik, 2019.
  [2] Joe B. Wells.
      "Typability and type checking in the second-order lambda-calculus are equivalent and undecidable." 
      Proceedings Ninth Annual IEEE Symposium on Logic In Computer Science. 
      IEEE, 1994.
*)

From Stdlib Require Import List.

(* pure lambda-terms M, N, .. *)
Inductive pure_term : Type :=
  | pure_var : nat -> pure_term 
  | pure_app : pure_term -> pure_term -> pure_term 
  | pure_abs : pure_term -> pure_term.

(* polymorphic types s, t, ..*)
Inductive poly_type : Type :=
  | poly_var : nat -> poly_type 
  | poly_arr : poly_type -> poly_type -> poly_type 
  | poly_abs : poly_type -> poly_type.

(* system F type environments *)
Definition environment := list poly_type.

(* function composition *)
Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y) :=
  fun x => g (f x).

(* stream cons *)
Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with | 0 => x | S n => xi n end.

(* polymorphic type variable renaming *)
Fixpoint ren_poly_type (xi : nat -> nat) (s : poly_type) : poly_type  :=
  match s return poly_type with
  | poly_var x => poly_var (xi x)
  | poly_arr s t => poly_arr (ren_poly_type xi s) (ren_poly_type xi t)
  | poly_abs s => poly_abs (ren_poly_type (scons 0 (funcomp S xi)) s)
  end.

(* polymorphic type variable substitution *)
Fixpoint subst_poly_type (sigma : nat -> poly_type) (s : poly_type) : poly_type  :=
  match s return poly_type with
  | poly_var s => sigma s
  | poly_arr s t => poly_arr (subst_poly_type sigma s) (subst_poly_type sigma t)
  | poly_abs s => poly_abs (subst_poly_type (scons (poly_var 0) (funcomp (ren_poly_type S) sigma)) s)
  end.

(* 
  Curry-style System F Type Assignment predicate 
  Γ ⊢ M : τ is (type_assignment Γ M τ) 
*)
Inductive type_assignment : environment -> pure_term -> poly_type -> Prop :=
| type_assignment_var {Gamma x t} : 
    nth_error Gamma x = Some t -> 
    type_assignment Gamma (pure_var x) t
| type_assignment_app {Gamma M N s t} :
    type_assignment Gamma M (poly_arr s t) -> type_assignment Gamma N s -> 
    type_assignment Gamma (pure_app M N) t
| type_assignment_abs {Gamma M s t} :
    type_assignment (s :: Gamma) M t -> 
    type_assignment Gamma (pure_abs M) (poly_arr s t)
| type_assignment_inst {Gamma M s t} :
    type_assignment Gamma M (poly_abs s) -> 
    type_assignment Gamma M (subst_poly_type (scons t poly_var) s)
| type_assignment_gen {Gamma M s} :
    type_assignment (map (ren_poly_type S) Gamma) M s -> 
    type_assignment Gamma M (poly_abs s).

(* System F Type Checking *)
Definition SysF_TC : environment * pure_term * poly_type -> Prop :=
  fun '(Gamma, M, t) => type_assignment Gamma M t.

(* System F Typability *)
Definition SysF_TYP : pure_term -> Prop :=
  fun M => exists Gamma t, type_assignment Gamma M t.

(* System F Inhabitation *)
Definition SysF_INH : environment * poly_type -> Prop :=
  fun '(Gamma, t) => exists M, type_assignment Gamma M t.
