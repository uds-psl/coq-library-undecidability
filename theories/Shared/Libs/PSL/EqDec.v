From Undecidability.Shared.Libs.PSL Require Import Prelim.

(* * Decidable predicates *)


Definition dec (X: Prop) : Type := {X} + {~ X}.

Coercion dec2bool P (d: dec P) := if d then true else false.

Existing Class dec.

Definition Dec (X: Prop) (d: dec X) : dec X := d.
Arguments Dec X {d}.

Lemma Dec_reflect (X: Prop) (d: dec X) :
  Dec X <-> X.
Proof.
  destruct d as [A|A]; cbv; firstorder congruence.
Qed.

Notation Decb X := (dec2bool (Dec X)).

Lemma Dec_reflect_eq (X Y: Prop) (d: dec X) (e: dec Y) :
 Decb X = Decb Y <->  (X <-> Y).
Proof.
  destruct d as [D|D], e as [E|E]; cbn; intuition congruence.
Qed.

Lemma Dec_auto (X: Prop) (d: dec X) :
  X -> Dec X.
Proof.
  destruct d as [A|A]; cbn; intuition congruence.
Qed.

Lemma Dec_auto_not (X: Prop) (d: dec X) :
  ~ X -> ~ Dec X.
Proof.
  destruct d as [A|A]; cbn; intuition congruence.
Qed.

Hint Resolve Dec_auto Dec_auto_not : core.
Hint Extern 4 =>  (* Improves type class inference *)
match goal with
  | [  |- dec ((fun _ => _) _) ] => cbn
end : typeclass_instances.

Tactic Notation "decide" constr(p) := 
  destruct (Dec p).
Tactic Notation "decide" constr(p) "as" simple_intropattern(i) := 
  destruct (Dec p) as i.
Tactic Notation "decide" "_" :=
  destruct (Dec _).
Tactic Notation "have" constr(E) := let X := fresh "E" in decide E as [X|X]; subst; try congruence; try lia; clear X.

Lemma Dec_true P {H : dec P} : dec2bool (Dec P) = true -> P.
Proof.
  decide P; cbv in *; firstorder.
Qed.

Lemma Dec_false P {H : dec P} : dec2bool (Dec P) = false -> ~P.
Proof.
  decide P; cbv in *; firstorder.
Qed.

Lemma Dec_true' (P : Prop) (d : dec P) : P -> Decb P = true.
Proof. intros H. decide P; cbn; tauto. Qed.

Lemma Dec_false' (P : Prop) (d : dec P) : (~ P) -> Decb P = false.
Proof. intros H. decide P; cbn; tauto. Qed.

Hint Extern 4 =>
match goal with
  [ H : dec2bool (Dec ?P) = true  |- _ ] => apply Dec_true in  H
| [ H : dec2bool (Dec ?P) = false |- _ ] => apply Dec_false in H
| [ |- dec2bool (Dec ?P) = true] => apply Dec_true'
| [ |- dec2bool (Dec ?P) = false] => apply Dec_false'
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
Defined.

Instance bool_dec (b: bool) :
  dec b.
Proof. 
  unfold dec. destruct b; cbn; auto. 
Defined.

Instance True_dec :
  dec True.
Proof. 
  unfold dec; tauto. 
Defined.

Instance False_dec :
  dec False.
Proof. 
  unfold dec; tauto. 
Defined.

Instance impl_dec (X Y : Prop) :  
  dec X -> dec Y -> dec (X -> Y).
Proof. 
  unfold dec; tauto. 
Defined.

Instance and_dec (X Y : Prop) :  
  dec X -> dec Y -> dec (X /\ Y).
Proof. 
  unfold dec; tauto. 
Defined.

Instance or_dec (X Y : Prop) : 
  dec X -> dec Y -> dec (X \/ Y).
Proof. 
  unfold dec; tauto. 
Defined.

(* Coq standard modules make "not" and "iff" opaque for type class inference, 
   can be seen with Print HintDb typeclass_instances. *)

Instance not_dec (X : Prop) : 
  dec X -> dec (~ X).
Proof. 
  unfold not. auto.
Defined.

Instance iff_dec (X Y : Prop) : 
  dec X -> dec Y -> dec (X <-> Y).
Proof. 
  unfold iff. auto.
Defined.

(* ** Discrete types *)

Notation "'eq_dec' X" := (forall x y : X, dec (x=y)) (at level 70).

Structure eqType :=
  EqType {
      eqType_X :> Type;
      eqType_dec : eq_dec eqType_X
    }.

Arguments EqType X {_} : rename.

Canonical Structure eqType_CS X (A: eq_dec X) := EqType X.

Existing Instance eqType_dec.

(* Print the base type of [eqType] in the Canonical Structure. *)
Arguments eqType_CS (X) {_}.

Instance unit_eq_dec :
  eq_dec unit.
Proof.
  unfold dec. decide equality. 
Defined.

Instance bool_eq_dec : 
  eq_dec bool.
Proof.
  unfold dec. decide equality. 
Defined.

Instance nat_eq_dec : 
  eq_dec nat.
Proof.
  unfold dec. decide equality.
Defined.

Instance prod_eq_dec X Y :  
  eq_dec X -> eq_dec Y -> eq_dec (X * Y).
Proof.
  unfold dec. decide equality. 
Defined.

Instance list_eq_dec X :  
  eq_dec X -> eq_dec (list X).
Proof.
  unfold dec. decide equality. 
Defined.

Instance sum_eq_dec X Y :  
  eq_dec X -> eq_dec Y -> eq_dec (X + Y).
Proof.
  unfold dec. decide equality. 
Defined.

Instance option_eq_dec X :
  eq_dec X -> eq_dec (option X).
Proof.
  unfold dec. decide equality.
Defined.

Instance Empty_set_eq_dec:
  eq_dec Empty_set.
Proof.
  unfold dec. decide equality.
Defined.

Instance True_eq_dec:
  eq_dec True.
Proof.
  intros x y. destruct x,y. now left.
Defined.

Instance False_eq_dec:
  eq_dec False.
Proof.
  intros [].
Defined.
