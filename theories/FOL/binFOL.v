(* * First-Order Logic in binary signature *)

Require Import Undecidability.FOL.Util.Syntax.
Require Import Undecidability.FOL.Util.sig_bin.
Require Import Undecidability.FOL.Util.FullTarski.
Require Import Undecidability.FOL.Util.FullDeduction.


(* ** List of decision problems concerning validity, satisfiability and provability *)

(* Validity of formulas with falsity in Tarski semantics *)
Definition binFOL_valid := @valid _ _ falsity_on.

(* Provability of formulas with falsity in ND with explosion *)
Definition binFOL_prv_intu := @prv _ _ falsity_on intu nil.
