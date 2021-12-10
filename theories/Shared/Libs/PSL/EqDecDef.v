Set Implicit Arguments. 
Unset Strict Implicit.
Unset Printing Records.
Unset Printing Implicit Defensive.

Definition dec (X: Prop) : Type := {X} + {~ X}.

Coercion dec2bool P (d: dec P) := if d then true else false.

Existing Class dec.

Notation "'eq_dec' X" := (forall x y : X, dec (x=y)) (at level 70).

Structure eqType :=
  EqType {
      eqType_X :> Type;
      eqType_dec : eq_dec eqType_X
    }.

Arguments EqType X {_} : rename.

Canonical Structure eqType_CS X (A: eq_dec X) := EqType X.

#[global]
Existing Instance eqType_dec.

(* Print the base type of [eqType] in the Canonical Structure. *)
Arguments eqType_CS (X) {_}.

Definition Dec (X: Prop) (d: dec X) : dec X := d.
Arguments Dec X {d}.
