Require Import Lia.
Require Export Psatz Arith.
Require Export RelationClasses Morphisms.

(* Congruence Lemmatas over nat*)
#[global]
Instance add_le_mono : Proper (le ==> le ==> le) plus.
Proof. repeat intro. now apply Nat.add_le_mono. Qed.

#[global]
Instance mult_le_mono : Proper (le ==> le ==> le) mult.
Proof. repeat intro. now apply Nat.mul_le_mono. Qed.

#[global]
Instance max_le_mono : Proper (le ==> le ==> le) max.
Proof. repeat intro. repeat eapply Nat.max_case_strong;lia. Qed.

#[global]
Instance max'_le_mono : Proper (le ==> le ==> le) Init.Nat.max.
Proof. repeat intro. repeat eapply Nat.max_case_strong;lia. Qed.

#[global]
Instance S_le_mono : Proper (le ==> le) S.
Proof. repeat intro. lia. Qed.

