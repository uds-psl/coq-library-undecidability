From Coq Require List Vector.

From Undecidability.L Require Import L Datatypes.Lists Datatypes.LNat.

Definition encNatL (n : nat) := nat_enc n.

Definition L_computable {k} (R : Vector.t nat k -> nat -> Prop) := 
  exists s, forall v : Vector.t nat k, 
      (forall m, R v m <-> L.eval (Vector.fold_left (fun s n => L.app s (encNatL n)) s v) (encNatL m)) /\
      (forall o, L.eval (Vector.fold_left (fun s n => L.app s (encNatL n)) s v) o -> exists m, o = encNatL m).
