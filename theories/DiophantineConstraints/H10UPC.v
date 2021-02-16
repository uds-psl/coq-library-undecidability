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

Definition h10upc_sem φ (c : h10upc) :=
  match c with 
    | ((x, y), (z1, z2)) => 
        1 + φ x + φ y = φ z1 /\ φ y * (1 + φ y) = φ z2 + φ z2
  end.

(*
  Uniform Diophantine Pair Constraint Solvability:
    given a list of uniform Diophantine pair constraints, 
    is there a valuation that satisfies each constraint?
*)
Definition H10UPC_SAT (cs: list h10upc) := 
  exists (φ: nat -> nat), forall c, In c cs -> h10upc_sem φ c.
