Require Import Undecidability.FRACTRAN.FRACTRAN.

From Coq Require Import List Vector Nat.
Import ListNotations Vector.VectorNotations.

Fixpoint enc {k} p i (v : Vector.t nat k) : nat := 
  match v with
  | @nil _ => 1
  | x :: v => (p i) ^ x * enc p (S i) v
  end.

Definition FRACTRAN_computable {k} (p : nat -> nat) (R : Vector.t nat k -> nat -> Prop) := 
  exists P : list (nat * nat), 
    forall v : Vector.t nat k,
      (forall m, R v m <-> FRACTRAN.eval P (enc p 1 v) (p 0))
    /\ (forall n, FRACTRAN.eval P (enc p 1 v) n -> exists m, n = (p 0) ^ m).
