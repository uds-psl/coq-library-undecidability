(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(*** * Halting problem for one counter machines CM1_HALT  *)

(* 
  Problem(s):
    One Counter Machine Halting (CM1_HALT)
*)

Require Import List Nat.

Definition State : Set := nat.
(* a configuration consists of a state and a counter value *)
Record Config : Set := mkConfig { state : State; value : nat }.

(* an instruction (n, q) maps 
  a configuration (p, c) to (q, c * (n+2) / (n+1)) if c is divisible by (n+1)
  and otherwise to (p+1, c) *)
Definition Instruction : Set := State * nat.

(* an one counter machine is a list of instructions *)
Definition Cm1 : Set := list Instruction.

(* one counter machine step function *)
Definition step (M: Cm1) (x: Config) : Config :=
  match (value x), (nth_error M (state x)) with
  | 0, _ => x (* halting configuration *)
  | _, None => x (* halting configuration *)
  | _, Some (p, n) => 
      match modulo (value x) (n+1) with
      | 0 => {| state := p; value := ((value x) * (n+2)) / (n+1) |}
      | _ => {| state := 1 + state x; value := value x |}
      end
  end.

(* unfold step if the configuration is decomposed *)
Arguments step _ !x /.

(* halting configuration property *)
Definition halting (M : Cm1) (x: Config) : Prop := step M x = x.

(* One Counter Machine Halting Problem (with Denominators at most 4) *)
Definition CM1_HALT : { M : Cm1 | Forall (fun '(_, n) => n < 4) M } -> Prop :=
  fun '(exist _ M _) => 
    exists n, halting M (Nat.iter n (step M) {| state := 0; value := 1 |}).
