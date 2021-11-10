Set Implicit Arguments.

#[export] Hint Extern 4 => exact _ : core.

Ltac inv H := inversion H; subst; clear H.

Definition dec (X: Prop) : Type := {X} + {~ X}.

Coercion dec2bool P (d: dec P) := if d then true else false.
Definition is_true (b : bool) := b = true.

Existing Class dec.

Definition Dec (X: Prop) (d: dec X) : dec X := d.
Arguments Dec X {d}.

Lemma Dec_reflect (X: Prop) (d: dec X) :
  is_true (Dec X) <-> X.
Proof.
  destruct d as [A|A]; cbv in *; intuition congruence.
Qed.

Lemma Dec_auto (X: Prop) (d: dec X) :
  X -> is_true (Dec X).
Proof.
  destruct d as [A|A]; cbn; intuition congruence.
Qed.

(* Lemma Dec_auto_not (X: Prop) (d: dec X) : *)
(*   ~ X -> ~ Dec X. *)
(* Proof. *)
(*   destruct d as [A|A]; cbn; tauto. *)
(* Qed. *)

(* Hint Resolve Dec_auto Dec_auto_not : core. *)
#[export] Hint Extern 4 =>  (* Improves type class inference *)
match goal with
  | [  |- dec ((fun _ => _) _) ] => cbn
end : typeclass_instances.

Tactic Notation "decide" constr(p) := 
  destruct (Dec p).
Tactic Notation "decide" constr(p) "as" simple_intropattern(i) := 
  destruct (Dec p) as i.
Tactic Notation "decide" "_" :=
  destruct (Dec _).

Lemma Dec_true P {H : dec P} : dec2bool (Dec P) = true -> P.
Proof.
  decide P; cbv in *; firstorder.
  congruence.
Qed.

Lemma Dec_false P {H : dec P} : dec2bool (Dec P) = false -> ~P.
Proof.
  decide P; cbv in *; firstorder.
  congruence.
Qed.

#[export] Hint Extern 4 =>
match goal with
  [ H : dec2bool (Dec ?P) = true  |- _ ] => apply Dec_true in  H
| [ H : dec2bool (Dec ?P) = true |- _ ] => apply Dec_false in H
end : core.

(* Decided propositions behave classically *)

Lemma dec_DN X : 
  dec X -> ~~ X -> X.
Proof. 
  unfold dec; tauto. 
Qed.

Lemma dec_DM_and X Y :  
  dec X -> dec Y -> ~ (X /\ Y) -> ~ X \/ ~ Y.
Proof. 
  unfold dec; tauto. 
Qed.

Lemma dec_DM_impl X Y :  
  dec X -> dec Y -> ~ (X -> Y) -> X /\ ~ Y.
Proof. 
  unfold dec; tauto. 
Qed.

(* Propagation rules for decisions *)

Fact dec_transfer P Q :
  P <-> Q -> dec P -> dec Q.
Proof.
  unfold dec. tauto.
Qed.

#[global]
Instance True_dec :
  dec True.
Proof. 
  unfold dec; tauto. 
Qed.

#[global]
Instance False_dec :
  dec False.
Proof. 
  unfold dec; tauto. 
Qed.

#[global]
Instance impl_dec (X Y : Prop) :  
  dec X -> dec Y -> dec (X -> Y).
Proof. 
  unfold dec; tauto. 
Qed.

#[global]
Instance and_dec (X Y : Prop) :  
  dec X -> dec Y -> dec (X /\ Y).
Proof. 
  unfold dec; tauto. 
Qed.

#[global]
Instance or_dec (X Y : Prop) : 
  dec X -> dec Y -> dec (X \/ Y).
Proof. 
  unfold dec; tauto. 
Qed.

(* Coq standard modules make "not" and "iff" opaque for type class inference, 
   can be seen with Print HintDb typeclass_instances. *)

#[global]
Instance not_dec (X : Prop) : 
  dec X -> dec (~ X).
Proof. 
  unfold not. auto.
Qed.

#[global]
Instance iff_dec (X Y : Prop) : 
  dec X -> dec Y -> dec (X <-> Y).
Proof. 
  unfold iff. auto.
Qed.

(* Discrete types *)

Notation "'eq_dec' X" := (forall x y : X, dec (x=y)) (at level 70).

Structure eqType := EqType {
  eqType_X :> Type;
  eqType_dec : eq_dec eqType_X }.

Arguments EqType X {_} : rename.

Canonical Structure eqType_CS X (A: eq_dec X) := EqType X.

#[global]
Existing Instance eqType_dec.

#[global]
Instance unit_eq_dec :
  eq_dec unit.
Proof.
  unfold dec. decide equality. 
Qed.

#[global]
Instance bool_eq_dec : 
  eq_dec bool.
Proof.
  unfold dec. decide equality. 
Defined.

#[global]
Instance nat_eq_dec : 
  eq_dec nat.
Proof.
  unfold dec. decide equality.
Defined.

#[global]
Instance prod_eq_dec X Y :  
  eq_dec X -> eq_dec Y -> eq_dec (X * Y).
Proof.
  unfold dec. decide equality. 
Defined.

#[global]
Instance list_eq_dec X :  
  eq_dec X -> eq_dec (list X).
Proof.
  unfold dec. decide equality. 
Defined.

#[global]
Instance sum_eq_dec X Y :  
  eq_dec X -> eq_dec Y -> eq_dec (X + Y).
Proof.
  unfold dec. decide equality. 
Defined.

#[global]
Instance option_eq_dec X :
  eq_dec X -> eq_dec (option X).
Proof.
  unfold dec. decide equality.
Defined.

#[global]
Instance Empty_set_eq_dec:
  eq_dec Empty_set.
Proof.
  unfold dec. decide equality.
Qed.

#[global]
Instance True_eq_dec:
  eq_dec True.
Proof.
  intros x y. destruct x,y. now left.
Qed.

#[global]
Instance False_eq_dec:
  eq_dec False.
Proof.
  intros [].
Qed.
