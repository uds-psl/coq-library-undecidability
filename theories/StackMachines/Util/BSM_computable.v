Require Import Undecidability.StackMachines.BSM.

From Coq Require Import List Vector.
Import ListNotations Vector.VectorNotations.

Definition BSM_computable {k} (R : Vector.t nat k -> nat -> Prop) := 
  exists n : nat, exists i : nat, exists P : list (bsm_instr (1 + k + n)),
    forall v : Vector.t nat k,
      (forall m, R v m <->
         exists c v', BSM.eval (1 + k + n) (i, P) (i, (@List.nil bool :: Vector.map (fun n => List.repeat true n) v) ++ Vector.const (@List.nil bool) n) (c, List.repeat true m :: v'))
    /\ (forall c v', BSM.eval (1 + k + n) (i, P) (i, (@List.nil bool :: Vector.map (fun n => List.repeat true n) v) ++ Vector.const (@List.nil bool) n) (c, v') -> exists m v'', v' = List.repeat true m :: v'').    
