(* 
  Problem(s):
    Binary Single-tape Turing Machine Halting (SBTM2_HALT)
    Binary Single-tape Turing Machine Halting on Empty Tape (SBTM2_HALT0)
*)

Require Coq.Vectors.Fin ssrfun.
Import ssrfun (obind).

#[local] Open Scope list_scope.
#[local] Open Scope type_scope.

(* the blank symbol is "false" *)
Notation tape := (list bool * bool * list bool).

Inductive direction : Type := go_left | go_right.

(* the tape implicitly contains infinitely many blanks to the left and right *)
Definition mv (d: direction) (t: tape) :=
  match d with
  | go_left =>
      match t with
      | (l :: ls, a, rs) => (ls, l, a :: rs)
      | (nil, a, rs) => (nil, false, a :: rs)
      end
  | go_right =>
      match t with
      | (ls, a, r :: rs) => (a :: ls, r, rs)
      | (ls, a, nil) => (a :: ls, false, nil)
      end
  end.

Record SBTM2 := {
  num_states : nat;
  trans : (Fin.t num_states) * bool -> option ((Fin.t num_states) * bool * direction) }.

Notation state M := (Fin.t (num_states M)).
Notation config M := ((state M) * tape).

(* step function *)
Definition step (M: SBTM2) : config M -> option (config M) :=
  fun '(q, (ls, a, rs)) => 
    match trans M (q, a) with
    | None => None
    | Some (q', a', d) => Some (q', mv d (ls, a', rs))
    end.

(* iterated step function *)
Definition steps (M: SBTM2) (k: nat) (x: config M) : option (config M) :=
  Nat.iter k (obind (step M)) (Some x).

(* SBTM2 halting problem *)
Definition SBTM2_HALT : { M : SBTM2 & config M } -> Prop :=
  fun '(existT _ M x) => exists k, steps M k x = None.
