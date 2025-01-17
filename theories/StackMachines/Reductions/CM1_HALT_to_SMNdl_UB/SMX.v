(* 
  Author(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Definition(s): 
    Stack Machines with Exchange
*)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Relation_Operators.

Section SMX.
  Context {State Symbol : Set}.

  Definition Stack : Set := list Symbol.

  (* configuration: (left stack, right stack), state *)
  Definition Config : Set := Stack * Stack * State. 

  (* instruction: vXw -> rYs
    if last parameter is true, then exchange stacks after operation *)
  Definition Instruction : Set := Config * Config * bool.

  (* simple stack machine: list of instructions *)
  Definition SMX : Set := list Instruction. 

  Inductive step (M : SMX) : Config -> Config -> Prop :=
    | transition (v w r s r' s': Stack) (x y: State) (b: bool) : 
      In ((r, s, x), (r', s', y), b) M -> 
      step M (r ++ v, s ++ w, x) 
        match b with
        | false => (r' ++ v, s' ++ w, y)
        | true => (s' ++ w, r' ++ v, y)
        end.
        
  (* step is functional *)
  Definition deterministic (M: SMX) := forall (X Y Z: Config), step M X Y -> step M X Z -> Y = Z.

  (* reflexive transitive closure of step *)
  Definition reachable (M: SMX) : Config -> Config -> Prop := clos_refl_trans Config (step M).

  (* uniform bound for the number of reachable configurations *)
  Definition bounded (M: SMX) (n: nat) : Prop := 
    forall (X: Config), exists (L: list Config), (forall (Y: Config), reachable M X Y -> In Y L) /\ length L <= n.

End SMX.
