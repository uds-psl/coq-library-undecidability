Require Import List.
Import ListNotations.
Require Import Arith Lia.

Require Import ssreflect ssrbool ssrfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Maximal Implicit Insertion.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

Section ForallNorm.

Variable T : Type.
Variable P : T -> Prop.

Lemma Forall_singletonP {a} : Forall P [a] <-> P a.
Proof. rewrite Forall_cons_iff Forall_nil_iff. by tauto. Qed.

(* use: rewrite ? Forall_norm *)
Definition Forall_norm := (@Forall_app, @Forall_singletonP, @Forall_cons_iff, @Forall_nil_iff).

End ForallNorm.
