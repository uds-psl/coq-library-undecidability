(** * Synthetic Computability *)
(** ** Decidability, enumerability, reductions *)

(* a decision problem on a domain X is mechanized by a predicate P : X -> Prop *)
  
(* (complement P) is the complement decision problem of P *)
Definition complement {X} (P : X -> Prop) := fun x : X => ~ P x.
(* (reflects b P) means that 
   provability of the proposition P coincides with b being true *)
Definition reflects (b : bool) (P : Prop) := P <-> b = true.

(* (decider f P) means that
   the function f from the domain X of the predicate P to Booleans pointwise reflects P *)
Definition decider {X} (f : X -> bool) (P : X -> Prop) : Prop :=
  forall x, reflects (f x) (P x).
(* (decidable P) means that
   there exists a (total, computable, Boolean) decider f of P *)
Definition decidable {X} (P : X -> Prop) : Prop :=
  exists f : X -> bool, decider f P.

(* (enumerator f P) means that
   the function f is a surjection from the natural numbers to the positive instances of P *)
Definition enumerator {X} (f : nat -> option X) (P : X -> Prop) : Prop :=
  forall x, P x <-> exists n, f n = Some x.
(* (enumerable P) means that 
   there exists a (onto the positive instances of P) enumerator f of P *)
Definition enumerable {X} (P : X -> Prop) : Prop :=
  exists f : nat -> option X, enumerator f P.

(* (semi_decider f P) means that 
   the function f from the domain X of the predicate P to Boolean sequences pointwise reflects P
   with respect to Boolean sequence satisfiability *)
Definition semi_decider {X} (f : X -> nat -> bool) (P : X -> Prop) : Prop :=
  forall x, P x <-> exists n, f x n = true.
(* (semi_decidable P) means that 
   there exists a (computable, to Boolean sequences) semi-decider f of P *)
Definition semi_decidable {X} (P : X -> Prop) : Prop :=
  exists f : X -> nat -> bool, semi_decider f P.

(* (reduction f P Q) means that f many-one reduces P to Q, that is
   for the function f from the domain X of P to the domain Y of Q
   P pointwise coincides with Q ∘ f *)
Definition reduction {X Y} (f : X -> Y) (P : X -> Prop) (Q : Y -> Prop) :=
  forall x, P x <-> Q (f x).
(* (reduces P Q) means that
   there exists a (total, computable, many-one) reduction f from P to Q *)
Definition reduces {X Y} (P : X -> Prop) (Q : Y -> Prop) :=
  exists f : X -> Y, reduction f P Q.
Notation "P ⪯ Q" := (reduces P Q) (at level 70).
