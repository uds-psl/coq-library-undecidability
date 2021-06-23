Require Import Undecidability.MinskyMachines.MM.

From Coq Require Import List Vector.
Import ListNotations Vector.VectorNotations.

Definition MM_computable {k} (R : Vector.t nat k -> nat -> Prop) := 
  exists n : nat, exists i : nat, exists P : list (mm_instr (Fin.t (1 + k + n))),
    forall v : Vector.t nat k,
      (forall m, R v m <->
         exists c v', @MM.eval (1 + k + n) (i, P) (i, (0 :: v) ++ Vector.const 0 n) (c, m :: v')).