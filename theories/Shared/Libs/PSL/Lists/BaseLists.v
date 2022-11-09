From Undecidability.Shared.Libs.PSL Require Export Prelim EqDec.

Export List.ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).
Notation "| A |" := (length A) (at level 65).

#[export] Hint Extern 4 => 
match goal with
|[ H: ?x el nil |- _ ] => destruct H
end : core.

(* ** Lists *)

(* *** Duplicate-free lists *)
Notation dupfree := List.NoDup.

Definition undup {X : eqType} (A : list X) : list X :=
  nodup (@eqType_dec X) A.

Create HintDb list.

(* Register additional simplification rules with autorewrite / simpl_list *)
(* Print Rewrite HintDb list. *)
Global Hint Rewrite <- app_assoc : list.
Global Hint Rewrite rev_app_distr map_app prod_length : list.

(* *** Decisions for lists *)

#[global]
Instance list_in_dec X (x : X) (A : list X) :  
  eq_dec X -> dec (x el A).
Proof.
  intros D. apply in_dec. exact D.
Qed.

(* *** Membership

We use the following lemmas from Coq's standard library List.
- [in_eq :  x el x::A]
- [in_nil :  ~ x el nil]
- [in_cons :  x el A -> x el y::A]
- [in_or_app :  x el A \/ x el B -> x el A++B]
- [in_app_iff :  x el A++B <-> x el A \/ x el B]
- [in_map_iff :  y el map f A <-> exists x, f x = y /\ x el A]
*)

(* TODO put into list db *)
#[export] Hint Resolve in_eq in_nil in_cons in_or_app : core.

(* *** Inclusion

We use the following lemmas from Coq's standard library List.
- [incl_refl :  A <<= A]
- [incl_tl :  A <<= B -> A <<= x::B]
- [incl_cons : x el B -> A <<= B -> x::A <<= B]
- [incl_appl : A <<= B -> A <<= B++C]
- [incl_appr : A <<= C -> A <<= B++C]
- [incl_app : A <<= C -> B <<= C -> A++B <<= C]
*)

#[export] Hint Resolve incl_refl incl_tl incl_cons incl_appl incl_appr incl_app incl_nil_l : core.
