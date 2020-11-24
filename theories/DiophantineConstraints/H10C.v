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
    Square Diophantine Constraint Solvability (H10SQC_SAT)
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

(** Square Diophantine constraints are of three shapes:
      x = 1 | x + y = z | x * x = y  with x, y, z in nat 
*)

Inductive h10sqc : Set :=
  | h10sqc_one : nat -> h10sqc
  | h10sqc_plus : nat -> nat -> nat -> h10sqc
  | h10sqc_sq : nat -> nat -> h10sqc.

Definition h10sqc_sem φ c :=
  match c with
    | h10sqc_one x      => φ x = 1
    | h10sqc_plus x y z => φ x + φ y = φ z
    | h10sqc_sq x y => φ x * φ x = φ y
  end.

(**
  Square Diophantine Constraint Solvability:
    given a list of Diophantine constraints, is there a valuation that satisfies each constraint?
*)
Definition H10SQC_SAT (cs: list h10sqc) := exists (φ: nat -> nat), forall c, In c cs -> h10sqc_sem φ c.

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
