
From Undecidability.TM Require Export Util.Prelim Util.TM_facts.

(* We add these three symbols the alphabets of every machine. [START] is the first symbol of the encoding and [STOP] is always the right-most symbol. [UNKNOWN] is always ignored (it serves as the default symbol for the alphabet-lift, see [ChangeAlphabet]). *)
Inductive boundary : Type :=
| START   : boundary
| STOP    : boundary
| UNKNOWN : boundary.

(* Declare discreteness of [boundary] *)
#[global]
Instance boundary_eq : eq_dec boundary.
Proof. unfold dec. decide equality. Defined. (* because definition *)

(* Declare finiteness of [boundary] *)
#[global]
Instance boundary_fin : finTypeC (EqType boundary).
Proof. split with (enum := [START; STOP; UNKNOWN]). cbn. intros []; cbn; reflexivity. Defined. (* because definition *)

(* Because every machine is defined on an alphabet [Σ^+], the notation adds the discreteness and finiteness constructors, to cast [Σ^+ : finType]. *)
Notation "sig '^+'" := (FinType (EqType (boundary + sig) % type)) (at level 0) : type_scope.
