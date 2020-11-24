From Undecidability.Shared.Libs.PSL Require Import FinTypes.

(* * Completeness Lemmas for lists of basic types *)

Lemma bool_enum_ok x:
  count  [true; false] x = 1.
Proof.
  simpl. dec; destruct x; congruence.
Qed.

Lemma unit_enum_ok x:
  count [tt] x = 1.
Proof.
  simpl. destruct x; dec; congruence.
Qed.

Lemma Empty_set_enum_ok (x: Empty_set):
  count nil x = 1.
Proof.
  tauto.
Qed.

Lemma True_enum_ok x:
  count [I] x = 1.
Proof.
  simpl; dec;  destruct x; congruence.
Qed.

Lemma False_enum_ok (x: False):
  count nil x = 1.
Proof.
  tauto.
Qed.

(* ** Declaration of finTypeCs for base types as instances of the type class *)

Instance finTypeC_Empty_set: finTypeC (EqType Empty_set).
Proof.
  econstructor. eapply Empty_set_enum_ok.
Defined.

Instance finTypeC_bool: finTypeC (EqType bool).
Proof.
  econstructor. apply bool_enum_ok.
Defined.

Instance finTypeC_unit: finTypeC (EqType unit).
Proof. econstructor. apply unit_enum_ok.
Defined.

(* Instance finTypeC_empty : finTypeC (EqType emptu *)
(* Proof. *)
(*   econstructor. apply Empty_set_enum_ok. *)
(* Defined. *)

Instance finTypeC_True : finTypeC (EqType True).
Proof.
  econstructor. apply True_enum_ok.
Defined.

Instance  finTypeC_False : finTypeC (EqType False).
Proof.
  econstructor. apply False_enum_ok.
Defined.
