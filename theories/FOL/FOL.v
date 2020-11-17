(** * First-Order Logic *)

From Undecidability.FOL.Utils Require Import FOL_facts Deduction Semantics Kripke.
 
(** ** Syntax as defined in Utils/FOL_facts.v 

Inductive term : Type :=
  V (v : var) | P (p : par)
| t_f : bool -> term -> term
| t_e : term. 

Inductive logic := frag | full.

Inductive form : logic -> Type :=
| Pr {b} : term -> term -> form b
| Q {b} : form b
| Fal : form full
| Impl {b} : form b -> form b -> form b
| All {b} : var -> form b -> form b.
*)