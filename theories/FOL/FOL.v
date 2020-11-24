(* * First-Order Logic *)

From Undecidability.FOL.Util Require Import Syntax Deduction Tarski Kripke.
 
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

(* ** Instantiation to signature with 1 constant, 2 unary functions, 1 prop constant, 1 binary relation *)

Inductive syms_func := s_f : bool -> syms_func | s_e.

Instance sig_func : funcs_signature :=
  {| syms := syms_func; ar_syms := fun f => if f then 1 else 0 |}.

Inductive syms_pred := sPr | sQ.

Instance sig_pred : preds_signature :=
  {| preds := syms_pred; ar_preds := fun P => if P then 2 else 0 |}.

(* ** List of decision problems concerning validity, satisfiability and provability *)

(* Provability and validity of minimal logic without falsity *)
Notation "FOL*_prv_intu" := (@prv _ _ falsity_off intu nil).
Notation "FOL*_valid" := (@valid _ _ falsity_off).

(* Validity of formulas with falsity in Tarski semantics *)
Definition FOL_valid := @valid _ _ falsity_on.

(* Satisfiability of formulas with falsity in Tarski semantics *)
Definition FOL_satis := @satis _ _ falsity_on.

(* Validity of formulas with falsity in Kripke semantics *)
Definition FOL_valid_intu := @kvalid _ _ falsity_on.

(* Satisfiability of formulas with falsity in Kripke semantics *)
Definition FOL_satis_intu := @ksatis _ _ falsity_on.

(* Provability of formulas with falsity in ND with explosion *)
Definition FOL_prv_intu := @prv _ _ falsity_on intu nil.

(* Provability of formulas with falsity in ND with explosion and Peirce's law *)
Definition FOL_prv_class := @prv _ _ falsity_on class nil.
