From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L Require Import Datatypes.LNat.

Require Export PslBase.FiniteTypes.FinTypes.

(** *** Encoding finite types *)
(* This is not an instance because we only want it for very specific types. *)
Definition registered_finType `{X : finType} : registered X.
Proof.
  eapply (registerAs index).
  intros x y H. now apply injective_index.
Defined.

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

  Global Instance term_index (F:finType): computableTime' (@index F) (fun _ _=> (1, tt)).
  Proof.
    apply cast_computableTime.
  Qed.

  Global Instance term_finType_eqb (X:finType) : computableTime' (finType_eqb (X:=X)) (fun x _ => (1,fun y _ => (17 * Init.Nat.min (index x) (index y) + 17,tt))).
  Proof.
    extract.
    solverec.
  Qed.
End finType_eqb.
