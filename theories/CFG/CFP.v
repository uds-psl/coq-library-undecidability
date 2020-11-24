Require Import List.
Import ListNotations.

Definition stack (X : Type) := list (list X * list X).

(* ** Post Grammars *)

(* Post Grammar Derivability 
  A Post Grammar is a context-free grammar 
  with one non-terminal a
  and rules a => xay, where x and y are words over terminals *)
Fixpoint sigma {X: Type} (a : X) (A : stack X) :=
  match A with
    nil => [a]
  | (x, y) :: A => x ++ (sigma a A) ++ y
  end.

(* The Context-free Post Grammar Palindrome Problem is
  given a Post grammar to determine whether
  it contains a palindrome of length more than one. *)
Definition CFPP : stack nat * nat -> Prop :=
  fun '(R, a) => exists (A : stack nat), 
    incl A R /\ A <> [] /\ sigma a A = rev (sigma a A).

(* The Context-free Post Grammar Intersection Problem is
  given two Post grammars to determine whether 
  their intersection is not empty. *)
Definition CFPI : stack nat * stack nat * nat -> Prop :=
  fun '(R1, R2, a) => exists (A1 A2 : stack nat), 
    incl A1 R1 /\ incl A2 R2 /\ A1 <> [] /\ A2 <> [] /\ sigma a A1 = sigma a A2.
