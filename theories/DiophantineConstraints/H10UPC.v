(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

Require Import List.

(* Uniform Diophantine pairs constraints (h10upc) are of shape:  
    (x, y) # (1 + x + y, y * y)
*)
Definition h10upc := ((nat * nat) * (nat * nat))%type.

(** Direct semantics of h10upc_sem *)
Definition h10upc_sem_direct (c : h10upc) :=
  match c with 
    | ((x, y), (z1, z2)) => 
        1 + x + y = z1 /\ y * (1 + y) = z2 + z2
  end.

Definition h10upc_sem φ (c : h10upc) :=
  match c with 
    | ((x, y), (z1, z2)) => 
        h10upc_sem_direct ((φ x, φ y), (φ z1, φ z2))
  end.

(*
  Uniform Diophantine Pair Constraint Solvability:
    given a list of uniform Diophantine pair constraints, 
    is there a valuation that satisfies each constraint?
*)
Definition H10UPC_SAT (cs: list h10upc) := 
  exists (φ: nat -> nat), forall c, In c cs -> h10upc_sem φ c.
