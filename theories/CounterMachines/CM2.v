(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Problem(s):
    Two Counter Machine Halting (CM2_HALT)
*)

Require Import List.

Definition State : Set := nat.
(* a configuration consists of a state and two counter values *)
Record Config : Set := mkConfig { state : State; value1 : nat; value2 : nat }.

(* the instruction inc true maps 
      a configuration (p, (v1, v2)) to (1+p, (v1, 1+v2))
    the instruction inc false maps 
      a configuration (p, (v1, v2)) (1+p, (1+v1, v2))
    an instruction dec true q maps
      a configuration (p, (v1, 0)) to (1+p, (v1, 0)) 
      a configuration (p, (v1, 1+v2)) to (q, (v1, v2)) 
    an instruction dec false q maps
      a configuration (p, (0, v2)) to (1+p, (0, v2)) 
      a configuration (p, (1+v1, v2)) to (q, (v1, v2)) *)
Inductive Instruction : Set := 
  | inc : bool -> Instruction
  | dec : bool -> State -> Instruction.

(* a two counter machine is a list of instructions *)
Definition Cm2 : Set := list Instruction.

(* two counter machine step function *)
Definition step (M: Cm2) (x: Config) : Config :=
  match nth_error M (state x) with
  | None => x (* halting configuration *)
  | Some (inc b) => (* increase counter, goto next state*)
    {| state := 1 + (state x); 
       value1 := (if b then 0 else 1) + (value1 x);
       value2 := (if b then 1 else 0) + (value2 x) |}
  | Some (dec b y) => (* decrease counter, if successful goto state y *)
    if b then 
      match value2 x with
      | 0 => {| state := 1 + (state x); value1 := value1 x; value2 := 0 |}
      | S n => {| state := y; value1 := value1 x; value2 := n |}
      end
    else
      match value1 x with
      | 0 => {| state := 1 + (state x); value1 := 0; value2 := value2 x |}
      | S n => {| state := y; value1 := n; value2 := value2 x |}
      end
  end.
(* unfold step if the configuration is decomposed *)
Arguments step _ !x /.

(* halting configuration property *)
Definition halting (M : Cm2) (x: Config) : Prop := step M x = x.

(* Two Counter Machine Halting Problem *)
Definition CM2_HALT : Cm2 -> Prop :=
  fun M => exists (n: nat), 
    halting M (Nat.iter n (step M) {| state := 0; value1 := 0; value2 := 0 |}).
