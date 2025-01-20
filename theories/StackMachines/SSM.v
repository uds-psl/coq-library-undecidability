(* 
  Author(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Definition(s): 
    Confluent Simple Stack Machines (cssm)
  Problems(s):
    Uniform Boundedness of Confluent Simple Stack Machines (CSSM_UB)
*)

From Stdlib Require Import List Relation_Operators.

Definition stack : Set := list bool.
Definition state : Set := nat.
(* configuration: left stack, right stack, state *)
Definition config : Set := stack * stack  * state. 
(* direction: true = move left, false = move right *)
Definition dir : Set := bool. 
(* stack symbol: true = 1, false = 0 *)
Definition symbol : Set := bool. 
(* instruction: 
  (x, y, a, b, true ) = ax -> by 
  (x, y, b, a, false ) = xb -> ay *)
Definition instruction : Set := state * state * symbol * symbol * dir.
(* simple stack machine: list of instructions *)
Definition ssm : Set := list instruction. 

Inductive step (M : ssm) : config -> config -> Prop :=
  (* transition AaxB -> AybB *)
  | step_l (x y: state) (a b: symbol) (A B: stack) : 
    In (x, y, a, b, true) M -> step M (a::A, B, x) (A, b::B, y)
  (* transition AxbB -> AayB *)
  | step_r (x y: state) (a b: symbol) (A B: stack) : 
    In (x, y, b, a, false) M -> step M (A, b::B, x) (a::A, B, y).

(* reflexive transitive closure of step *)
Definition reachable (M: ssm) : config -> config -> Prop := clos_refl_trans config (step M).

(* step is confluent *)
Definition confluent (M: ssm) := forall (X Y1 Y2: config), reachable M X Y1 -> reachable M X Y2 -> 
  exists (Z: config), reachable M Y1 Z /\ reachable M Y2 Z.

(* confluent simple stack machine *)
Definition cssm := { M : ssm | confluent M }.

(* uniform bound for the number of reachable configurations *)
Definition bounded (M: ssm) (n: nat) : Prop := 
  forall (X: config), exists (L: list config), (forall (Y: config), reachable M X Y -> In Y L) /\ length L <= n.

(* given a confluent simple stack machine M, 
  is M uniformly bounded by some n? *)
Definition CSSM_UB (M : cssm) := exists (n: nat), bounded (proj1_sig M) n.
