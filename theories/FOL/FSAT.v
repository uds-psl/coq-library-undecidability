From Undecidability.FOL.Util Require Import Syntax FullTarski sig_bin.
Require Import Undecidability.Synthetic.DecidabilityFacts.
Import Vector.VectorNotations.
Require Import List.
 
(* ** Syntax as defined in Util/Syntax.v 

 Inductive term  : Type :=
  | var : nat -> term
  | func : forall (f : syms), vec term (ar_syms f) -> term.

  Inductive falsity_flag := falsity_off | falsity_on.

  Inductive form : falsity_flag -> Type :=
  | falsity : form falsity_on
  | atom {b} : forall (P : preds), vec term (ar_preds P) -> form b
  | bin {b} : binop -> form b -> form b -> form b
  | quant {b} : quantop -> form b -> form b.    
*)

(* ** List of decision problems concerning finite satisfiability *)

Existing Instance falsity_on.

Definition listable X :=
  exists L, forall x : X, List.In x L.

Definition FSAT (phi : form) :=
  exists D (I : interp D) rho, listable D -> discrete D -> decidable (X := D*D) (fun '(x, y) => i_atom (P:=tt) ([x; y])) -> rho ⊨ phi.
