(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Definition(s): 
    Deterministic, Length-preserving Stack Machines
  Problems(s):
    Uniform Boundedness of Deterministic, Length-preserving Stack Machines (SMNdl_UB)
*)

Require Import Relation_Operators List.
Import ListNotations.

Definition State := nat.
Definition Symbol := bool.

Definition Stack : Set := list Symbol.

(* configuration: state, (left stack, right stack) *)
Definition Config : Set := Stack * Stack * State. 

(* instruction: vXw -> rYs *)
Definition Instruction : Set := Config * Config.

(* stack machine: list of instructions *)
Definition SMN : Set := list Instruction. 

Inductive step (M : SMN) : Config -> Config -> Prop :=
  | transition (v w r s r' s': Stack) (x y: State) : 
    In ((r, s, x), (r', s', y)) M -> 
    step M (r ++ v, s ++ w, x) (r' ++ v, s' ++ w, y).
      
(* step is functional *)
Definition deterministic (M: SMN) := forall (X Y Z: Config), step M X Y -> step M X Z -> Y = Z.

(* reflexive transitive closure of step *)
Definition reachable (M: SMN) : Config -> Config -> Prop := clos_refl_trans Config (step M).

(* step is confluent *)
Definition confluent (M: SMN) := forall (X Y1 Y2: Config), reachable M X Y1 -> reachable M X Y2 -> 
  exists (Z: Config), reachable M Y1 Z /\ reachable M Y2 Z.

(* uniform bound for the number of reachable configurations *)
Definition bounded (M: SMN) (n: nat) : Prop := 
  forall (X: Config), exists (L: list Config), (forall (Y: Config), reachable M X Y -> In Y L) /\ length L <= n.

(* sum of stack sizes is invariant under step *)
Definition length_preserving (M: SMN) : Prop :=
  forall s t X s' t' Y, In ((s, t, X), (s', t', Y)) M -> length (s ++ t) = length (s' ++ t') /\ 1 <= length (s ++ t).

(* given a deterministic, length-preserving stack machine M, 
  is M uniformly bounded by some n? *)
Definition SMNdl_UB : { M : SMN | deterministic M /\ length_preserving M } -> Prop :=
  fun '(exist _ M _) => exists (n: nat), bounded M n.
