(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  Problem(s):
    Intersection Type Type Checking  (CD_TC)
    Intersection Type Typability (CD_TYP)
    Intersection Type Inhabitation (CD_INH)

  Literature:
    [1] Coppo, Mario, and Mariangiola Dezani-Ciancaglini.
        "An extension of the basic functionality theory for the lambda-calculus."
        Notre Dame journal of formal logic 21.4 (1980): 685-693.
*)

Require Undecidability.L.L.
Require Import List.
Import L (term, var, app, lam).

(* strict types are of shape: a | (s1 /\ s2 /\ .. /\ sn -> t) *)
Inductive sty : Type :=
  | atom : nat -> sty
  | arr : sty -> list sty -> sty -> sty.

(* a type is a (non-empty) list of strict types *)
Notation ty := (sty * list sty)%type.

(* Coppo-Dezani Intersection Type System *)
Inductive type_assignment (Gamma : list ty) : term -> sty -> Prop :=
  | type_assignment_var x s phi t :
      nth_error Gamma x = Some (s, phi) ->
      In t (s::phi) ->
      type_assignment Gamma (var x) t
  | type_assignment_app M N s phi t :
      type_assignment Gamma M (arr s phi t) ->
      type_assignment Gamma N s ->
      Forall (type_assignment Gamma N) phi ->
      type_assignment Gamma (app M N) t
  | type_assignment_arr M s phi t :
      type_assignment ((s, phi) :: Gamma) M t ->
      type_assignment Gamma (lam M) (arr s phi t).

(* Intersection Type Type Checking *)
Definition CD_TC : (list ty) * term * sty -> Prop :=
  fun '(Gamma, M, t) => type_assignment Gamma M t.

(* Intersection Type Typability *)
Definition CD_TYP : term -> Prop :=
  fun M => exists Gamma t, type_assignment Gamma M t.

(* Intersection Type Inhabitation *)
Definition CD_INH : (list ty) * sty -> Prop :=
  fun '(Gamma, t) => exists M, type_assignment Gamma M t.
