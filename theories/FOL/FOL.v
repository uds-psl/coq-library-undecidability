(** * First-Order Logic *)

From Undecidability.FOL.Util Require Import FOL_facts Deduction Semantics Kripke.
 
(** ** Syntax as defined in Util/FOL_facts.v 

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

Notation "FOL*_prv_intu" := (@prv intu frag nil).
Notation "FOL*_valid" := (@valid frag).
Definition FOL_satis := @satis full.
Definition FOL_valid_intu := (@kvalid full).
Definition FOL_prv_intu := @prv intu full nil.
Definition FOL_prv_class := @prv class full nil.
Definition FOL_satis_intu := @ksatis full.
