(** * Inhabited types *)

(* Author: Maximilian Wuttke *)


From Undecidability.Shared.Libs.PSL Require Prelim.
From Coq.Vectors Require Import Vector Fin.
From Undecidability.Shared.Libs.PSL Require Import FiniteTypes.FinTypes.

Class inhabitedC (X : Type) :=
    {
      default : X;
    }.

Instance inhabited_unit : inhabitedC unit.
Proof. do 2 constructor. Defined.

Instance inhabited_True : inhabitedC True.
Proof. do 2 constructor. Defined.

Instance inhabited_inl (A B : Type) (inh_a : inhabitedC A) : inhabitedC (A + B).
Proof. constructor. left. apply default. Defined.

Instance inhabited_inr (A B : Type) (inh_B : inhabitedC B) : inhabitedC (A + B).
Proof. constructor. right. apply default. Defined.

Instance inhabited_option (A : Type) : inhabitedC (option A).
Proof. constructor. right. Defined.

Instance inhabited_bool : inhabitedC bool.
Proof. do 2 constructor. Defined.

Instance inhabited_list (A : Type) : inhabitedC (list A).
Proof. do 2 constructor. Defined.

Instance inhabited_vector (A : Type) (n : nat) (inh_A : inhabitedC A) : inhabitedC (Vector.t A n).
Proof. constructor. eapply VectorDef.const. apply default. Defined.

Instance inhabited_fin (n : nat) : inhabitedC (Fin.t (S n)).
Proof. repeat constructor. Defined.

Instance inhabited_nat : inhabitedC nat.
Proof. do 2 constructor. Defined.

Instance inhabited_prod (A B : Type) : inhabitedC A -> inhabitedC B -> inhabitedC (A*B).
Proof. intros ia ib. do 2 constructor; apply default. Defined.

Instance inhabited_arrow (A B : Type) : inhabitedC B -> inhabitedC (A -> B).
Proof. intros. constructor. intros _. apply default. Defined.

Instance inhabited_arrow_empty (B : Type) : inhabitedC (Empty_set -> B).
Proof. intros. constructor. apply Empty_set_rect. Defined.

Instance inhabited_arrow_sum (A B C : Type) : inhabitedC (A->C) -> inhabitedC (B->C) -> inhabitedC (A+B->C).
Proof. intros iac ibc. constructor. intros [?|?]. now apply iac. now apply ibc. Defined.

Instance inhabited_arrow_prod (A B C : Type) : inhabitedC (A->B) -> inhabitedC (A->C) -> inhabitedC (A->B*C).
Proof. intros iab iac. constructor. intros a. constructor. now apply iab. now apply iac. Defined.


(** Derive inhabitedC instances, if an instance of this type is a hypothesis *)
Hint Extern 10 => match goal with
                | [ H : ?X |- inhabitedC ?X ] => now econstructor
                end : typeclass_instances.
(*
Section Test.
  Variable lie : False.
  Compute default : False.
  Variable somebool : bool.
  (* This should prefer the instance, not the variable. *)
  Compute default : bool.
End Test.
*)
