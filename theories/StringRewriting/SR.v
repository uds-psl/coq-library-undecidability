Require Import List.
(* why is this import here? *)
Require Import Undecidability.PCP.PCP.

(* A string is a list of symbols. *)
Definition string X := list X.

Module RuleNotation.
Notation "x / y" := (x, y).
End RuleNotation.
Import RuleNotation.

(* A string rewriting system SRS is a list of rules x / y 
  such that x rewrites to y. *)
Definition SRS X := list (string X * string X).

(* If u / v is a rewriting rule, then x ++ u ++ y rewrites to x ++ v ++ y. *)
Inductive rew {X : Type} (R : SRS X) : string X -> string X -> Prop :=
  rewB x y u v : In (u / v) R -> rew R (x ++ u ++ y) (x ++ v ++ y).
(* rewt is the reflexive, transitive closure of rew. *)
Inductive rewt {X : Type} (R : SRS X) : string X -> string X -> Prop :=
  rewR z : rewt R z z
| rewS x y z : rew R x y -> rewt R y z -> rewt R x z.

(* String rewriting SR is
  given a string rewriting system R and two strings x and y,
  determine whether x rewrites to y in R. *)
Definition SR : SRS nat * string nat * string nat -> Prop :=
  fun '(R, x, y) => rewt R x y.

Definition swap {X Y} : X * Y -> Y * X := fun '(x,y) => (y,x).

(* Thue system reachability TSR is
  given a string rewriting system R and two strings x and y,
  determine whether x is equivalent to y in R. *)
Definition TSR : SRS nat * string nat * string nat -> Prop :=
    fun '(R, x, y) => rewt (R ++ map swap R) x y.
