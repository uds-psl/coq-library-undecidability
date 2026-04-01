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
From Stdlib Require Import List.
Import L (term, var, app, lam).

#[local] Unset Elimination Schemes.

(* strict types are of shape: a | (s1 /\ s2 /\ .. /\ sn -> t) *)
Inductive sty : Type :=
  | atom : nat -> sty
  | arr : sty -> list sty -> sty -> sty.

Section strong_sty_eliminators.

  (* DLW: these are unused ATM but might eventually
          be useful later on ... I let them here *)

  Fact sty_ind (P : sty -> Prop) :
       (forall n, P (atom n))
    -> (forall t1 (_ : P t1) l (_ : forall t, In t l -> P t) t2 (_ : P t2), P (arr t1 l t2))
    -> forall t, P t.
  Proof.
    intros H1 H2.
    refine (fix loop t := _).
    destruct t as [ n | t1 l t2 ].
    + apply H1.
    + apply H2.
      1,3: apply loop.
      clear t1 t2.
      intros t.
      induction l as [ | x l IH ].
      * intros [].
      * intros [ <- | ].
        - apply loop.
        - now apply IH.
  Qed.

  Local Fact sty_In_wf : well_founded (fun s t => match t with 
                  | arr t1 l t2 => s = t1 \/ In s l \/ s = t2 
                  | _ => False
                  end).
  Proof.
    intros t.
    induction t as [ n | t1 IH1 l IHl t2 IH2 ]
      using sty_ind; constructor.
    + intros ? [].
    + intros ? [ -> | [ | -> ] ]; auto.
  Qed.

  Fact sty_rect (P : sty -> Type) :
      (forall n, P (atom n))
   -> (forall t1 (_ : P t1) l (_ : forall t, In t l -> P t) t2 (_ : P t2), P (arr t1 l t2))
   -> (forall t, P t).
  Proof.
    intros ? ? t.
    induction t as [ [] ] using (well_founded_induction_type sty_In_wf); auto.
  Qed.

End strong_sty_eliminators.

Definition sty_rec (P : _ -> Set) := sty_rect P.

#[global] Register Scheme sty_rect as rect_dep for sty.
#[global] Register Scheme sty_rec as rec_dep for sty.
#[global] Register Scheme sty_ind as ind_dep for sty.

(* a type is a (non-empty) list of strict types *)
Abbreviation ty := (sty * list sty)%type.

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

#[local] Set Elimination Schemes.

(* Intersection Type Type Checking *)
Definition CD_TC : (list ty) * term * sty -> Prop :=
  fun '(Gamma, M, t) => type_assignment Gamma M t.

(* Intersection Type Typability *)
Definition CD_TYP : term -> Prop :=
  fun M => exists Gamma t, type_assignment Gamma M t.

(* Intersection Type Inhabitation *)
Definition CD_INH : (list ty) * sty -> Prop :=
  fun '(Gamma, t) => exists M, type_assignment Gamma M t.
