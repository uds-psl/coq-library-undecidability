(* 
  Author(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(* 
  Problem(s):
    Two-counter Machine Halting (CM2_HALT)
    Two-counter Machine Reversibility (CM2_REV)
    Reversible Two-counter Machine Halting (CM2_REV_HALT)
    Two-counter Machine Uniform Boundedness (CM2_UBOUNDED)
    Two-counter Machine Uniform Mortality (CM2_UMORTAL)
*)

Require Import List ssrfun.

(* a configuration consists of a state and two counter values *)
Definition Config : Set := nat * (nat * nat).

(* accessors for state, value1, value2 of configurations *)
Definition state (x: Config) : nat := fst x.
Arguments state !x /.
Definition value1 (x: Config) : nat := fst (snd x).
Arguments value1 !x /.
Definition value2 (x: Config) : nat := snd (snd x).
Arguments value2 !x /.

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
  | dec : bool -> nat -> Instruction.

(* a two-counter machine is a list of instructions *)
Definition Cm2 : Set := list Instruction.

(* partial two-counter machine step function *)
Definition step (M: Cm2) (x: Config) : option Config :=
  match nth_error M (state x) with
  | None => None (* halting configuration *)
  | Some (inc b) => (* increase counter, goto next state*)
    Some (1 + (state x), ((if b then 0 else 1) + (value1 x), (if b then 1 else 0) + (value2 x)))
  | Some (dec b y) => (* decrease counter, if successful goto state y *)
    Some (
      if b then 
        match value2 x with
        | 0 => (1 + (state x), (value1 x, 0))
        | S n => (y, (value1 x, n))
        end
      else
        match value1 x with
        | 0 => (1 + (state x), (0, value2 x))
        | S n => (y, (n, value2 x))
        end)
  end.

(* iterated partial two-counter machine step function *)
Definition steps (M: Cm2) (k: nat) (x: Config) : option Config :=
  Nat.iter k (obind (step M)) (Some x).

(* two-counter machine configuration reachability *)
Definition reaches (M: Cm2) (x y: Config) :=
  exists k, steps M k x = Some y.

(* does M eventually terminate starting from the configuration x? *)
Definition terminating (M: Cm2) (x: Config) :=
  exists k, steps M k x = None.

(* injectivity of the step function *)
Definition reversible (M : Cm2) : Prop := 
  forall x y z, step M x = Some z -> step M y = Some z -> x = y.

(* k bounds the number of reachable configurations from x *)
Definition bounded (M: Cm2) (k: nat) (x: Config) : Prop := 
  exists (L: list Config), (length L <= k) /\
    (forall (y: Config), reaches M x y -> In y L).

(* uniform bound for number of reachable configurations *)
Definition uniformly_bounded (M: Cm2) : Prop :=
  exists k, forall x, bounded M k x.

(* k bounds the number of steps in a terminating run from x *)
Definition mortal (M: Cm2) (k: nat) (x: Config) : Prop := 
  steps M k x = None.

(* uniform bound for number of steps until termination *)
Definition uniformly_mortal (M: Cm2) : Prop :=
  exists k, forall x, mortal M k x.

(* Two-counter Machine Halting:
   Given a two-counter machine M,
   does a run in M starting from configuration (0, (0, 0)) eventually halt? *)
Definition CM2_HALT : Cm2 -> Prop :=
  fun M => terminating M (0, (0, 0)).

(* Two-counter Machine Reversibility:
   Given a two-counter machine M,
   is the step function of M injective? *)
Definition CM2_REV : Cm2 -> Prop :=
  fun M => reversible M.

(* Reversible Two-counter Machine Halting:
   Given a reversible two-counter machine M and a configucation x, 
   does a run in M starting from x eventually halt? *)
Definition CM2_REV_HALT : { M: Cm2 | reversible M } * Config -> Prop :=
  fun '((exist _ M _), x) => terminating M x.

(* Two-counter Machine Uniform Boundedness:
   Given a two-counter machine M,
   is there a uniform bound n,
   such that for any configuration x,
   the number of reacheable configurations from x is bounded by n? *)
Definition CM2_UBOUNDED : Cm2 -> Prop :=
  fun M => uniformly_bounded M.

(* Two-counter Machine Uniform Mortality:
   Given a two-counter machine M,
   is there a uniform bound n,
   such that for any configuration x,
   a run in M starting from x halts after at most n steps? *)
Definition CM2_UMORTAL : Cm2 -> Prop :=
  fun M => uniformly_mortal M.
