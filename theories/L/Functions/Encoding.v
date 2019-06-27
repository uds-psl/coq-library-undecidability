From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Export LNat LTerm LProd.

(** ** Extracted encoding of natural numbers *)

Instance term_nat_enc : computableTime' nat_enc (fun n _ => (n * 14 + 12,tt)).
Proof.
  extract. solverec.
Qed.

(** ** Extracted term encoding *)

Instance term_term_enc : computableTime' term_enc (fun s _ => (size s * 30,tt)).
Proof.
  extract. solverec.
Qed.

(* (** ** Extracted tuple encoding *) *)

(* Instance term_prod_enc X Y (R1:registered X) (R2:registered Y): computable (@prod_enc X Y R1 R2). *)
(* Proof. *)
(*   unfold prod_enc. cbn. extract. *)
(* Qed. *)

Definition prod_enc' {X Y} (enc_x : X -> term) (enc_y : Y -> term) : X * Y -> term :=
  fix f w := let '(x,y) := w in
             lam (var 0 (enc_x x) (enc_y y)).

Lemma enc_prod_eq {X Y} {H__x:registered X} {H__y : registered Y}:
  @enc (X*Y) _ = prod_enc' (@enc _ H__x) (@enc _ H__y).
Proof.
  unfold enc. destruct H__x, H__y. reflexivity.
Qed.

Instance term_prod_enc' {X Y} {H__x : registered X} {H__Y : registered Y}:
  computableTime' (@prod_enc' X Y) (fun _ t__X => (1,fun _ t__Y => (1,fun w _ => (let '(x,y):= w in  fst (t__X x tt) + fst (t__Y y tt) + 15,tt)))).
Proof.
  extract. solverec.
Qed.
