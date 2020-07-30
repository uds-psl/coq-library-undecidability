(** * Definition of Multi-Tape Turing Machines *)

Require Import PslBase.FiniteTypes.FinTypes.
Require Import Vector List.

Unset Implicit Arguments.

Section Fix_Sigma.

  Variable Σ : Type.

  Inductive tape : Type :=
  | niltape : tape
  | leftof : Σ -> list Σ -> tape
  | rightof : Σ -> list Σ -> tape    (* DLW: why not rightof :  list Σ -> Σ -> tape ? *)
  | midtape : list Σ -> Σ -> list Σ -> tape.

  Definition tapes n := Vector.t tape n.

  (** DLW: Are you sure you want one letter constructors ?
      Each time you import TM, L, R and N become unusable

      I suggest longer constructors names, with possibly
      *local* notations *)

  Inductive move : Type := L : move | R : move | N : move.

  (** DLW: A small visual to explain the intuition
      left/right/mid tape would be good 

      The mv scheme here implies that written cells
      must be contiguous, 
      ie you cannot move right of a rightof tape
      nor left of a leftof tape

      a tape like ..... _ _ a b _ c d _ _ f e _ _ ...
      would not be allowed

      Not sure this corresponds to usual literature?
      It is my understanding that TM can skip over empty cells

      Using the l name for cells contents is unfortunate
      because it suggests a list ...

    *)

  Definition mv (m : move) (t : tape) :=
    match m, t with
    | L, rightof l ls => midtape ls l nil
    | L, midtape nil m rs => leftof m rs
    | L, midtape (l :: ls) m rs => midtape ls l (m :: rs)
    | R, leftof r rs => midtape nil r rs
    | R, midtape ls m nil => rightof m ls
    | R, midtape ls m (r :: rs) => midtape (m :: ls) r rs
    | _, _ => t
    end.

  Definition wr (s : option Σ) (t : tape) : tape :=
    match s, t with
    | None, t => t
    | Some a, niltape => midtape nil a nil
    | Some a, leftof r rs => midtape nil a (r :: rs)
    | Some a, midtape ls b rs => midtape ls a rs
    | Some a, rightof l ls => midtape (l :: ls) a nil
    end.

  Definition current (t : tape) :=
    match t with
    | midtape _ a _ => Some a
    | _ => None
    end.

  (* DLW: I suppose that finType below is much more workable that ns and states = Fin.t ns
     but on the other hand, it requires understanding finType which belongs to
     PslBase 

     I guess it is possible to show that any finType is isomorphic to Fin.t ns 
     for some ns. May be a reference to such a result would help *)

  Variable n : nat.

  (* DLW: I suggest state instead of states, trans and start feels strange with states. *)

  Record mTM : Type :=
    {
    states : finType; (* states of the TM *)
    trans : states * (Vector.t (option Σ) n) -> states * (Vector.t ((option Σ) * move) n); (* the transition function *)
    start: states; (* the start state *)
    halt : states -> bool (* decidable subset of halting states *)
    }.

  Inductive eval (M : mTM) (q : states M) (t : Vector.t tape n) : states M -> Vector.t tape n -> Prop :=
  | eval_halt :
      halt M q = true ->
      eval M q t q t
  | eval_step q' a q'' t' :
      halt M q = false ->
      trans M (q, Vector.map current t) = (q', a) ->
      eval M q' (Vector.map2 (fun tp '(c,m) => mv m (wr c tp)) t a) q'' t' ->
      eval M q t q'' t'.

End Fix_Sigma.

Arguments niltape _, {_}.
Arguments leftof _ _ _, {_} _ _.
Arguments rightof _ _ _, {_} _ _.
Arguments midtape _ _ _ _, {_} _ _ _.

Arguments current {_} _.

Arguments states {_ _} _.
Arguments trans {_ _} _ _, {_ _ _} _.
Arguments start {_ _} _.
Arguments halt {_ _} _ _, {_ _ _} _.

Arguments eval {_ _} _ _ _ _ _.

Arguments Build_mTM {_ _ _} _ _ _.

(* DLW: is there a reason for not always using tapes Σ n below ? *)

Definition HaltsTM {Σ: finType} {n: nat} (M : mTM Σ n) (t : Vector.t (tape Σ) n) :=
  exists q' t', eval M (start M) t q' t'.
Arguments HaltsTM _ _ _ _, {_ _} _ _.

Definition HaltTM (n : nat) : {Σ : finType & mTM Σ n & Vector.t (tape Σ) n} -> Prop :=
  fun '(existT2 _ _ Σ M t) => HaltsTM M t.

Definition HaltMTM : {'(n,Σ) : nat * finType & mTM Σ n & tapes Σ n} -> Prop :=
  fun '(existT2 _ _ (n, Σ) M t) => HaltsTM M t.
