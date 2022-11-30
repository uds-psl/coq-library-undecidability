From Undecidability.Shared.Libs.PSL Require Import Prelim.
From Undecidability.Shared.Libs.PSL Require Export EqDecDef.

(* * Decidable predicates *)

Lemma Dec_reflect (X: Prop) (d: dec X) :
  Dec X <-> X.
Proof.
  destruct d as [A|A]; cbv; firstorder congruence.
Qed.

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
Tactic Notation "have" constr(E) := let X := fresh "E" in decide E as [X|X]; subst; try congruence; try lia; clear X.

(* Propagation rules for decisions *)

Fact dec_transfer P Q :
  P <-> Q -> dec P -> dec Q.
Proof.
  unfold dec. tauto.
Defined.

#[export]
Instance bool_dec (b: bool) :
  dec b.
Proof. 
  unfold dec. now destruct b; [left|right]. 
Defined.

#[export]
Instance True_dec :
  dec True.
Proof. 
  unfold dec; tauto. 
Defined.

#[export]
Instance False_dec :
  dec False.
Proof. 
  unfold dec; tauto. 
Defined.

#[export]
Instance impl_dec (X Y : Prop) :  
  dec X -> dec Y -> dec (X -> Y).
Proof. 
  unfold dec; tauto. 
Defined.

#[export]
Instance and_dec (X Y : Prop) :  
  dec X -> dec Y -> dec (X /\ Y).
Proof. 
  unfold dec; tauto. 
Defined.

#[export]
Instance or_dec (X Y : Prop) : 
  dec X -> dec Y -> dec (X \/ Y).
Proof. 
  unfold dec; tauto. 
Defined.

(* Coq standard modules make "not" and "iff" opaque for type class inference, 
   can be seen with Print HintDb typeclass_instances. *)

#[export]
Instance not_dec (X : Prop) : 
  dec X -> dec (~ X).
Proof. 
  unfold not. exact _.
Defined.

#[export]
Instance iff_dec (X Y : Prop) : 
  dec X -> dec Y -> dec (X <-> Y).
Proof. 
  unfold iff. exact _.
Defined.

#[export]
Instance nat_le_dec (x y : nat) : dec (x <= y) := 
  Compare_dec.le_dec x y.

(* ** Discrete types *)

#[export]
Instance unit_eq_dec :
  eq_dec unit.
Proof.
  unfold dec. decide equality. 
Defined.

#[export]
Instance bool_eq_dec : 
  eq_dec bool.
Proof.
  unfold dec. decide equality. 
Defined.

#[export]
Instance nat_eq_dec : 
  eq_dec nat.
Proof.
  unfold dec. decide equality.
Defined.

#[export]
Instance prod_eq_dec X Y :  
  eq_dec X -> eq_dec Y -> eq_dec (X * Y).
Proof.
  unfold dec. decide equality. 
Defined.

#[export]
Instance list_eq_dec X :  
  eq_dec X -> eq_dec (list X).
Proof.
  unfold dec. decide equality. 
Defined.

#[export]
Instance sum_eq_dec X Y :  
  eq_dec X -> eq_dec Y -> eq_dec (X + Y).
Proof.
  unfold dec. decide equality. 
Defined.

#[export]
Instance option_eq_dec X :
  eq_dec X -> eq_dec (option X).
Proof.
  unfold dec. decide equality.
Defined.

#[export]
Instance Empty_set_eq_dec:
  eq_dec Empty_set.
Proof.
  unfold dec. decide equality.
Defined.

#[export]
Instance True_eq_dec:
  eq_dec True.
Proof.
  intros x y. destruct x,y. now left.
Defined.

#[export]
Instance False_eq_dec:
  eq_dec False.
Proof.
  intros [].
Defined.
