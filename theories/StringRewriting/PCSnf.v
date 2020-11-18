Require Import List.
Require Import Undecidability.PCP.PCP.

(** A string is a list of symbols. *)
Definition string X := list X.

Notation "x / y" := (x, y).

(** A string rewriting system SRS is a list of rules x / y 
  such that x rewrites to y. *)
Definition SRS X := list (string X * string X).

(** If u / v is a rewriting rule, then u ++ x rewrites to x ++ u. *)
Inductive der {X : Type} (R : SRS X) : string X -> string X -> Prop :=
  derB x u v : In (u / v) R -> der R (u ++ x) (x ++ v).
(** rewt is the reflexive, transitive closure of rew. *)
Inductive derv {X : Type} (R : SRS X) : string X -> string X -> Prop :=
  derR z : derv R z z
| derS x y z : der R x y -> derv R y z -> derv R x z.

(** String rewriting PCSnf is
  given a Post canonical system in normal form R and two strings x and y,
  determine whether x rewrites to y in R. *)
Definition PCSnf : SRS nat * string nat * string nat -> Prop :=
  fun '(R, x, y) => derv R x y.
