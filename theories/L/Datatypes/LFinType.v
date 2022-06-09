From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L Require Import Datatypes.LNat Datatypes.LBool.

Import Nat.
Require Export Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypes.

(* *** Encoding finite types *)
(* This is not an instance because we only want it for very specific types. *)
Definition registered_finType `{X : finType} : registered X.
Proof.
  eapply (registerAs index).
  intros x y H. now apply injective_index.
Defined. (*because registerAs*)

Definition finType_eqb {X:finType} (x y : X) :=
  Nat.eqb (index x) (index y).

Lemma finType_eqb_reflect (X:finType) (x y:X) : reflect (x = y) (finType_eqb x y).
Proof.
  unfold finType_eqb. destruct (Nat.eqb_spec (index x) (index y));constructor.
  -now apply injective_index.
  -congruence.
Qed.

Section finType_eqb.
  Local Existing Instance registered_finType.

  Global Instance term_index (F:finType): computable (@index F).
  Proof.
    apply cast_computable.
  Qed.

  Local Instance eqbFinType_inst (X:finType): eqbClass finType_eqb (X:=X).
  Proof.
    intros ? ?. eapply finType_eqb_reflect. 
  Qed.
  Import Nat.

  Global Instance term_eqbFinType (X:finType): computable (finType_eqb (X:=X)).
  Proof.
    extract.
  Qed.

End finType_eqb.
