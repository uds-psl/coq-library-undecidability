(* Version: 23.04. *)

(** * Preliminaries by Autosubst *)

(** ** Axiomatic Assumptions
    For our development, we have to extend Coq with _functional extensionality_.
*)

(* ** Functional Extensionality
    We import the axiom from the Coq Standard Library and derive a utility tactic to make the assumption practically usable.
*)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Program.Tactics.

Tactic Notation "nointr" tactic(t) :=
  let m := fresh "marker" in
  pose (m := tt);
  t; revert_until m; clear m.

Ltac fext := nointr repeat (
  match goal with
    [ |- ?x = ?y ] =>
    (refine (@functional_extensionality_dep _ _ _ _ _) ||
     refine (@forall_extensionality _ _ _ _) ||
     refine (@forall_extensionalityP _ _ _ _) ||
     refine (@forall_extensionalityS _ _ _ _)); intro
  end).

(* ** Propositional Extensionality
    We state the axiom of _propositional extensionality_ directly and use it to prove _proof irrelevance_.
*)
Axiom pext : forall P Q : Prop, (P <-> Q) -> (P = Q).

Lemma pi {P : Prop} (p q : P) : p = q.
Proof.
  assert (P = True) by (apply pext; tauto). subst. now destruct p,q.
Qed.



(* **** Functor Instances *)

Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y)  :=
  fun x => g (f x).


(* **** Vector Instance *)
Require Export Vector.

Definition vec_ext {A B n} {f g : A -> B} :
  (forall x, f x = g x) -> forall xs : Vector.t A n, Vector.map f xs = Vector.map g xs.
  intros H. induction xs. reflexivity.
  cbn. f_equal. apply H. apply IHxs.
Defined.

Definition vec_id {A n} { f : A -> A} :
  (forall x, f x = x) -> forall xs : Vector.t A n, Vector.map f xs = xs.
Proof.
  intros H. induction xs. reflexivity.
  cbn. rewrite H. rewrite IHxs; eauto.
Defined.

Definition vec_comp {A B C n} {f: A -> B} {g: B -> C} {h} :
  (forall x, (funcomp  g f) x = h x) -> forall xs : Vector.t A n, map g (map f xs) = map h xs.
Proof.
  induction xs. reflexivity.
  cbn. rewrite <- H. f_equal. apply IHxs.
Defined.

(* **** List Instance *)
Require Export List.

Definition list_ext {A B} {f g : A -> B} :
  (forall x, f x = g x) -> forall xs,  map f xs = map g xs.
  intros H. induction xs. reflexivity.
  cbn. f_equal. apply H. apply IHxs.
Defined.

Definition list_id {A}  { f : A -> A} :
  (forall x, f x = x) -> forall xs, List.map f xs = xs.
Proof.
  intros H. induction xs. reflexivity.
  cbn. rewrite H. rewrite IHxs; eauto.
Defined.

Definition list_comp {A B C} {f: A -> B} {g: B -> C} {h} :
  (forall x, (funcomp  g f) x = h x) -> forall xs, map g (map f xs) = map h xs.
Proof.
  induction xs. reflexivity.
  cbn. rewrite <- H. f_equal. apply IHxs.
Defined.



(* **** Prod Instance *)

Definition prod_map {A B C D} (f : A -> C) (g : B -> D) (p : A * B) :
  C * D.
Proof.
  destruct p. split. auto. auto.
Defined.

Definition prod_id {A B} {f : A -> A} {g : B -> B} :
  (forall x, f x = x) -> (forall x, g x = x) -> forall p, prod_map f g p = p.
Proof.
  intros. destruct p. cbn. f_equal; auto.
Defined.

Definition prod_ext {A B C D} {f f' : A -> C} {g g': B -> D} :
  (forall x, f x = f' x) -> (forall x, g x = g' x) -> forall p, prod_map f g p = prod_map f' g' p.
Proof.
  intros. destruct p. cbn. f_equal; auto.
Defined.

Definition prod_comp {A B C D E F} {f1 : A -> C} {g1 : C -> E} { h1} {f2: B -> D} {g2: D -> F} {h2}:
  (forall x, (funcomp  g1 f1) x = h1 x) -> (forall x, (funcomp g2 f2) x = h2 x) -> forall p, prod_map g1 g2 (prod_map f1 f2 p) = prod_map h1 h2 p.
Proof.
  intros. destruct p. cbn. f_equal; auto.
  now rewrite <- H. now rewrite <- H0.
Defined.


(* **** Function Instance *)

Definition cod X A:  Type :=  X -> A.

Definition cod_map {X} {A B} (f : A -> B) (p : X -> A) :
  X -> B.
Proof. eauto. Defined.

(* Requires functional extensionality. *)
Definition cod_id {X} {A} {f : A -> A} :
  (forall x, f x = x) -> forall (p: X -> A), cod_map f p = p.
Proof. intros H p. unfold cod_map. fext. congruence. Defined.

Definition cod_ext {X} {A B} {f f' : A -> B} :
  (forall x, f x = f' x) -> forall (p: X -> A), cod_map f p = cod_map f' p.
Proof. intros H p. unfold cod_map. fext. congruence. Defined.

Definition cod_ext' {X} {A B} {f f' : A -> B} (p : X -> A) :
  (forall x, f (p x) = f' (p x)) -> cod_map f p = cod_map f' p.
Proof. intros H. unfold cod_map. fext. congruence. Defined.

Definition cod_comp {X} {A B C} {f : A -> B} {g : B -> C} {h} :
  (forall x, (funcomp g f) x =  h x) -> forall (p: X -> _), cod_map g (cod_map f p) = cod_map h p.
Proof. intros H p. unfold cod_map. fext. intros x. now rewrite <- H. Defined.

Hint Rewrite in_map_iff : FunctorInstances.
