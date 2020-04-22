From smpl Require Import Smpl.
Require Import Omega.
Require Export Psatz Arith.
Require Export RelationClasses Morphisms.

(* Congruence Lemmatas over nat*)
Instance add_le_mono : Proper (le ==> le ==> le) plus.
Proof. repeat intro. now apply Nat.add_le_mono. Qed.

Instance mult_le_mono : Proper (le ==> le ==> le) mult.
Proof. repeat intro. now apply Nat.mul_le_mono. Qed.

Instance max_le_mono : Proper (le ==> le ==> le) max.
Proof. repeat intro. repeat eapply Nat.max_case_strong;omega. Qed.

Instance max'_le_mono : Proper (le ==> le ==> le) Init.Nat.max.
Proof. repeat intro. repeat eapply Nat.max_case_strong;omega. Qed.

Instance S_le_mono : Proper (le ==> le) S.
Proof. repeat intro. omega. Qed.

