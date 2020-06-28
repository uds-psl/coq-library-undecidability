(* 
  Autor(s):
    Dominique Larchey-Wendling (1)
    Andrej Dudenhefner (2) 
  Affiliation(s):
    (1) LORIA -- CNRS
    (2) Saarland University, Saarbrücken, Germany
*)

(* 
  Problems(s):
    Diophantine Constraint Solvability (H10C_SAT)
    Uniform Diophantine Constraint Solvability (H10UC_SAT)
*)

Require Import List.

(** Diophantine constraints (h10c) are of three shapes:
      x = 1 | x + y = z | x * y = z  with x, y, z in nat 
*)

Inductive h10c : Set :=
  | h10c_one : nat -> h10c
  | h10c_plus : nat -> nat -> nat -> h10c
  | h10c_mult : nat -> nat -> nat -> h10c.
  
Definition h10c_sem c φ :=
  match c with
    | h10c_one x      => φ x = 1
    | h10c_plus x y z => φ x + φ y = φ z
    | h10c_mult x y z => φ x * φ y = φ z
  end.

(**
  Diophantine Constraint Solvability:
    given a list of Diophantine constraints, is there a valuation that satisfies each constraint?
*)
Definition H10C_SAT (cs: list h10c) := exists (φ: nat -> nat), forall c, In c cs -> h10c_sem c φ.

(** Uniform Diophantine constraints (h10uc) are of shape:  
      1 + x + y * y = z
*)
Definition h10uc := (nat * nat * nat)%type.

Definition h10uc_sem φ (c : h10uc) :=
  match c with 
    | (x, y, z) => 1 + φ x + φ y * φ y = φ z
  end.

(**
  Uniform Diophantine Constraint Solvability:
    given a list of uniform Diophantine constraints, is there a valuation that satisfies each constraint?
*)
Definition H10UC_SAT (cs: list h10uc) := exists (φ: nat -> nat), forall c, In c cs -> h10uc_sem φ c.
