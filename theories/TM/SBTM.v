(* 
  Problem(s):
    Binary Single-tape Turing Machine Halting (SBTM_HALT)
*)

From Stdlib Require Vectors.Fin Vectors.Vector.

#[local] Open Scope list_scope.
#[local] Open Scope type_scope.

Inductive direction : Type := go_left | go_right.

Record SBTM := Build_SBTM {
  num_states : nat;
  (* transition table *)
  trans : Vector.t (
    (option ((Fin.t num_states) * bool * direction)) *
    (option ((Fin.t num_states) * bool * direction)))
    num_states }.

Module SBTMNotations.
  Notation tape := (list bool * bool * list bool).
  Notation state M := (Fin.t (num_states M)).
  Notation config M := ((state M) * tape).
End SBTMNotations.

Import SBTMNotations.

(* the tape implicitly contains blanks ("false") to the left and right *)
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

(* transition table presented as a finite function *)
Definition trans' M : (state M) * bool -> option ((state M) * bool * direction) :=
  fun '(q, a) => 
    match a with
    | true => fst
    | false => snd
    end (Vector.nth (trans M) q).

Arguments trans' : simpl never.

(* step function *)
Definition step (M: SBTM) : config M -> option (config M) :=
  fun '(q, (ls, a, rs)) => 
    match trans' M (q, a) with
    | None => None
    | Some (q', a', d) => Some (q', mv d (ls, a', rs))
    end.

Arguments step : simpl never.

#[local] Definition obind {X Y} (f : X -> option Y) (o : option X) := 
  match o with None => None | Some x => f x end.

(* iterated step function *)
Definition steps (M: SBTM) (k: nat) (x: config M) : option (config M) :=
  Nat.iter k (obind (step M)) (Some x).

(* SBTM halting problem *)
Definition SBTM_HALT : { M : SBTM & config M } -> Prop :=
  fun '(existT _ M x) => exists k, steps M k x = None.
