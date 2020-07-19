Require Import Undecidability.PCP.PCP Undecidability.Shared.Prelim.

(** A string is a list of symbols. *)
Definition string X := list X.

Notation "x / y" := (x, y).

(** A string rewriting system SRS is a list of rules x / y 
  such that x rewrites to y. *)
Definition SRS X := list (string X * string X).

(** If u / v is a rewriting rule, then x ++ u ++ y rewrites to x ++ v ++ y. *)
Inductive rew {X : Type} (R : SRS X) : string X -> string X -> Prop :=
  rewB x y u v : In (u / v) R -> rew R (x ++ u ++ y) (x ++ v ++ y).
(** rewt is the reflexive, transitive closure of rew. *)
Inductive rewt {X : Type} (R : SRS X) : string X -> string X -> Prop :=
  rewR z : rewt R z z
| rewS x y z : rew R x y -> rewt R y z -> rewt R x z.

(** String rewriting SR is
  given a string rewriting system R and two strings x and y,
  determine whether x rewrites to y in R. *)
Definition SR : SRS nat * string nat * string nat -> Prop :=
  fun '(R, x, y) => rewt R x y.

(** String rewriting with a halting symbol SRH is
  given a string rewriting system R, a string x and a symbol a,
  determine whether x rewrites in R to some y that contains a. *)
Definition SRH : SRS nat * string nat * nat -> Prop :=
  fun '(R, x, a) => exists y, rewt R x y /\ In a y.
