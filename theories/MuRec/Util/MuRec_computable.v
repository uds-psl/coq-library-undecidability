From Undecidability.MuRec Require Import MuRec.

From Coq Require Import List Vector Nat.
Import ListNotations Vector.VectorNotations.

Definition FRACTRAN_computable {k} (R : Vector.t nat k -> nat -> Prop) := 
  exists f : recalg k, forall v : Vector.t nat k, forall m : nat,
        forall m, R v m <-> ra_bs f v m.