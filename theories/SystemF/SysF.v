Require Import List.

(** pure lambda-terms M, N, .. *)
Inductive pure_term : Type :=
  | pure_var : nat -> pure_term 
  | pure_app : pure_term -> pure_term -> pure_term 
  | pure_abs : pure_term -> pure_term.

(** polymorphic types s, t, ..*)
Inductive poly_type : Type :=
  | poly_var : nat -> poly_type 
  | poly_arr : poly_type -> poly_type -> poly_type 
  | poly_abs : poly_type -> poly_type.

(** system F terms P, Q, .. *)
Inductive term : Type :=
  | var : nat -> term  
  | app : term -> term -> term  
  | abs : poly_type -> term -> term  
  | ty_app : term -> poly_type -> term  
  | ty_abs : term -> term.

(** system F type environments *)
Definition environment := list poly_type.

(** function composition *)
Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y) :=
  fun x => g (f x).

(** stream cons *)
Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with | 0 => x | S n => xi n end.

Fixpoint ren_poly_type (xi : nat -> nat) (s : poly_type) : poly_type  :=
  match s return poly_type with
  | poly_var x => poly_var (xi x)
  | poly_arr s t => poly_arr (ren_poly_type xi s) (ren_poly_type xi t)
  | poly_abs s => poly_abs (ren_poly_type (scons 0 (funcomp S xi)) s)
  end.

Fixpoint subst_poly_type (sigma : nat -> poly_type) (s : poly_type) : poly_type  :=
  match s return poly_type with
  | poly_var s => sigma s
  | poly_arr s t => poly_arr (subst_poly_type sigma s) (subst_poly_type sigma t)
  | poly_abs s => poly_abs (subst_poly_type (scons (poly_var 0) (funcomp (ren_poly_type S) sigma)) s)
  end.

(** system F type derivability predicate *)
Inductive typing : environment -> term -> poly_type -> Prop :=
  | typing_var {Gamma x t} : 
      nth_error Gamma x = Some t -> typing Gamma (var x) t
  | typing_app {Gamma P Q s t} :
      typing Gamma P (poly_arr s t) -> typing Gamma Q s -> typing Gamma (app P Q) t
  | typing_abs {Gamma P s t} :
      typing (s :: Gamma) P t -> typing Gamma (abs s P) (poly_arr s t)
  | typing_ty_app {Gamma P s t} :
      typing Gamma P (poly_abs s) -> typing Gamma (ty_app P t) (subst_poly_type (scons t poly_var) s)
  | typing_ty_abs {Gamma P s} :
      typing (map (ren_poly_type S) Gamma) P s -> typing Gamma (ty_abs P) (poly_abs s).

(** type annotation erasure *)
Fixpoint erase (P: term) : pure_term :=
  match P with
  | var x => pure_var x
  | app P Q => pure_app (erase P) (erase Q)
  | abs _ P => pure_abs (erase P)
  | ty_app P _ => erase P
  | ty_abs P => erase P
  end.

(** System F Type Checking *)
Definition SysF_TC : environment * pure_term * poly_type -> Prop :=
  fun '(Gamma, M, t) => exists P, erase P = M /\ typing Gamma P t.

(** System F Typability *)
Definition SysF_TYP : pure_term -> Prop :=
  fun M => exists Gamma P t, erase P = M /\ typing Gamma P t.

(** System F Inhabitation *)
Definition SysF_INH : environment * poly_type -> Prop :=
  fun '(Gamma, t) => exists P, typing Gamma P t.
