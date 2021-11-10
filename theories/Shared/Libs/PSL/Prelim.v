(* * Base Library for ICL

   - Version: 3 October 2016
   - Author: Gert Smolka, Saarland University
   - Acknowlegments: Sigurd Schneider, Dominik Kirst, Yannick Forster, Fabian Kunze, Maximilian Wuttke
 *)

Require Export Bool Lia List Setoid Morphisms Arith.
From Undecidability.Shared.Libs.PSL Require Export Tactics.

Global Set Implicit Arguments. 
Global Unset Strict Implicit.
Global Unset Printing Records.
Global Unset Printing Implicit Defensive.

#[export] Hint Extern 4 => exact _ : core.  (* makes auto use type class inference *)

(* De Morgan laws *)

Lemma DM_or (X Y : Prop) :
  ~ (X \/ Y) <-> ~ X /\ ~ Y.
Proof.
  tauto.
Qed.

Lemma DM_exists X (p : X -> Prop) :
  ~ (exists x, p x) <-> forall x, ~ p x.
Proof.
  firstorder.
Qed.

(* ** Boolean propositions and decisions *)

Coercion is_true : bool >-> Sortclass.

Lemma bool_Prop_true b :
  b = true -> b.
Proof.
  intros A. rewrite A. reflexivity.
Qed.

Lemma bool_Prop_false b :
  b = false -> ~ b.
Proof.
  intros A. rewrite A. cbn. intros H. congruence.
Qed.

Lemma bool_Prop_true' (b : bool) :
  b -> b = true.
Proof.
  intros A. cbv in A. destruct b; tauto.
Qed.

Lemma bool_Prop_false' (b : bool) :
  ~ b -> b = false.
Proof.
  intros A. cbv in A. destruct b; tauto.
Qed.


#[export] Hint Resolve bool_Prop_true bool_Prop_false : core.
#[export] Hint Resolve bool_Prop_true' bool_Prop_false' : core.


Definition bool2nat := fun b : bool => if b then 1 else 0.
Definition nat2bool := fun n : nat => match n with 0 => false | _ => true end.
(* Coercion nat2bool : nat >-> bool. *)
Lemma bool_nat (b : bool) :
  1 = bool2nat b -> b.
Proof. intros; cbv in *. destruct b. auto. congruence. Qed.
Lemma nat_bool (b : bool) :
  b = nat2bool 1 -> b.
Proof. intros; cbv in *. destruct b. auto. congruence. Qed.
#[export] Hint Resolve bool_nat nat_bool : core.

Ltac simpl_coerce :=
  match goal with
  | [ H: False |- _ ] => destruct H
  | [ H: ~ is_true true |- _ ] => destruct H; congruence
  | [ H: is_true false |- _ ] => congruence
  end.


Ltac simpl_congruence :=
  match goal with
  | [ H : 0 = S _ |- _] => congruence
  | [ H : S _ = 0 |- _] => congruence
  | [ H : S _ = 0 |- _] => congruence
  | [ H : true = false |- _] => congruence
  | [ H : false = true |- _] => congruence
  end.

#[export] Hint Extern 1 => simpl_coerce : core.
#[export] Hint Extern 1 => simpl_congruence : core.
