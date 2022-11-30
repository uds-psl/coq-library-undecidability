Set Implicit Arguments.

Ltac inv H := inversion H; subst; clear H.

Definition dec (X: Prop) : Type := {X} + {~ X}.

Existing Class dec.

Definition Dec (X: Prop) (d: dec X) : dec X := d.
Arguments Dec X {d}.

Lemma Dec_auto (X: Prop) (d: dec X) :
  X -> (if Dec X then true else false) = true.
Proof.
  destruct d as [A|A]; cbn; intuition congruence.
Qed.

Tactic Notation "decide" constr(p) := 
  destruct (Dec p).
Tactic Notation "decide" constr(p) "as" simple_intropattern(i) := 
  destruct (Dec p) as i.
Tactic Notation "decide" "_" :=
  destruct (Dec _).

(* Propagation rules for decisions *)

#[export] Instance True_dec : dec True.
Proof. unfold dec; tauto. Qed.

#[export] Instance False_dec : dec False.
Proof. unfold dec; tauto. Qed.

#[export] Instance impl_dec (X Y : Prop) : dec X -> dec Y -> dec (X -> Y).
Proof. unfold dec; tauto. Qed.

#[export] Instance and_dec (X Y : Prop) : dec X -> dec Y -> dec (X /\ Y).
Proof. unfold dec; tauto. Qed.

#[export] Instance or_dec (X Y : Prop) : dec X -> dec Y -> dec (X \/ Y).
Proof. unfold dec; tauto. Qed.

(* Coq standard modules make "not" and "iff" opaque for type class inference, 
   can be seen with Print HintDb typeclass_instances. *)

#[export] Instance not_dec (X : Prop) : dec X -> dec (~ X).
Proof. unfold not. exact _. Qed.

#[export] Instance iff_dec (X Y : Prop) : dec X -> dec Y -> dec (X <-> Y).
Proof. unfold iff. exact _. Qed.

(* Discrete types *)

Notation "'eq_dec' X" := (forall x y : X, dec (x=y)) (at level 70).

#[export] Instance unit_eq_dec : eq_dec unit.
Proof. unfold dec. decide equality. Qed.

#[export] Instance bool_eq_dec : eq_dec bool.
Proof. unfold dec. decide equality. Defined.

#[export] Instance nat_eq_dec : eq_dec nat.
Proof. unfold dec. decide equality. Defined.

#[export] Instance prod_eq_dec X Y :  
  eq_dec X -> eq_dec Y -> eq_dec (X * Y).
Proof. unfold dec. decide equality. Defined.

#[export] Instance list_eq_dec X : eq_dec X -> eq_dec (list X).
Proof. unfold dec. decide equality. Defined.

#[export] Instance sum_eq_dec X Y : eq_dec X -> eq_dec Y -> eq_dec (X + Y).
Proof. unfold dec. decide equality. Defined.

#[export] Instance option_eq_dec X : eq_dec X -> eq_dec (option X).
Proof. unfold dec. decide equality. Defined.

#[export] Instance Empty_set_eq_dec : eq_dec Empty_set.
Proof. unfold dec. decide equality. Qed.

#[export] Instance True_eq_dec : eq_dec True.
Proof. intros x y. destruct x,y. now left. Qed.

#[export] Instance False_eq_dec : eq_dec False.
Proof. intros []. Qed.
