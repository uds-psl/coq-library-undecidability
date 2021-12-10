From Undecidability.Shared.Libs.PSL Require Export EqDecDef.

Set Implicit Arguments. 
Unset Strict Implicit.
Unset Printing Records.
Unset Printing Implicit Defensive.

(* This function counts the number of occurences of an element in a given list and returns the result *)
Fixpoint count (X: Type) `{eq_dec X}  (A: list  X) (x:  X) {struct A} : nat :=
  match A with
  | nil => O
  | cons y A' =>  if Dec (x=y) then S(count A' x) else count A' x end.


(* * Definition of finite Types *)

Class finTypeC  (type:eqType) : Type :=
  FinTypeC {
      enum: list type;
      enum_ok: forall x: type, count enum x = 1
  }.

Structure finType : Type :=
  FinType
    {
      type:> eqType;
      class: finTypeC type
    }.

Arguments FinType type {class}.
#[global]
Existing Instance class | 0.


(* This is a hack to work-around a problem with a class of hacks *)
#[export] Hint Extern 5 (finTypeC (EqType ?x)) => unfold x : typeclass_instances.

Canonical Structure finType_CS (X : Type) {p : eq_dec X} {class : finTypeC (EqType X)} : finType := FinType (EqType X).

(* Print the base type of [finType] in the Canonical Structure. *)
Arguments finType_CS (X) {_ _}.