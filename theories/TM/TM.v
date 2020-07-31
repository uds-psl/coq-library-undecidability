(** * Definition of Multi-Tape Turing Machines *)

Require Import PslBase.FiniteTypes.FinTypes.
Require Import Vector List.

Unset Implicit Arguments.

(** * Turing machines  *)

(** The definition of Turing machines is due to Asperti & Ricciotti's "A formalization of multi-tape Turing machines" (2015) and the accompanying Matita code. *)  

Section Fix_Sigma.

  (** The alphabet type *)
  Variable Σ : Type.

  (** ** Tapes

     Tapes are either
     - empty (niltape),
     - non-empty with the head to the left of the content (leftof),
     - non-empty with the head to the right of the content (rightof),
     - or non-empty with the head on the content (midtape).

      The representation does not allow for blank symbols, instead a blank symbol has to be part of the alphabet Σ. The seeming redundancy allows for a unique representation of every tape and no well-formedness predicate is needed.

   *)

  Inductive tape : Type :=
  | niltape : tape
  | leftof : Σ -> list Σ -> tape
  | rightof : Σ -> list Σ -> tape
  | midtape : list Σ -> Σ -> list Σ -> tape.

  Inductive move : Type := Lmove : move | Rmove : move | Nmove : move.

  Definition mv (m : move) (t : tape) :=
    match m, t with
    | Lmove, rightof l ls => midtape ls l nil
    | Lmove, midtape nil m rs => leftof m rs
    | Lmove, midtape (l :: ls) m rs => midtape ls l (m :: rs)
    | Rmove, leftof r rs => midtape nil r rs
    | Rmove, midtape ls m nil => rightof m ls
    | Rmove, midtape ls m (r :: rs) => midtape (m :: ls) r rs
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

End Fix_Sigma.

Arguments niltape _, {_}.
Arguments leftof _ _ _, {_} _ _.
Arguments rightof _ _ _, {_} _ _.
Arguments midtape _ _ _ _, {_} _ _ _.

Arguments current {_} _.

Arguments wr {_} _ _.
Arguments mv {_} _.

Section Fix_Alphabet.

  (** The alphabet type, assumed as finite type *)
  Variable Σ : finType.

   (** finType is defined as a pair of a type with decidable equality, and a duplicate-free list of all elements of the type.

      We have

      Lemma finType_equiv (X : finType) :
         {n & {f : X -> Fin.t n & { g : Fin.t n -> X | (forall x, g (f x) = x) /\ forall i, f (g i) = i }}}.

      in PslBase.FiniteTypes.FinTypesEquiv.

   *)
  
  (** The number of tapes  *)
  Variable n : nat.

  (* DLW: I suggest state instead of states, trans and start feels strange with states. *)

  Record mTM : Type :=
    {
    states : finType; (* states of the TM *)
    trans : states * (Vector.t (option Σ) n) -> states * (Vector.t ((option Σ) * move) n); (* the transition function *)
    start: states; (* the start state *)
    halt : states -> bool (* decidable subset of halting states *)
    }.

  Inductive eval (M : mTM) (q : states M) (t : Vector.t (tape Σ) n) : states M -> Vector.t (tape Σ) n -> Prop :=
  | eval_halt :
      halt M q = true ->
      eval M q t q t
  | eval_step q' a q'' t' :
      halt M q = false ->
      trans M (q, Vector.map current t) = (q', a) ->
      eval M q' (Vector.map2 (fun tp '(c,m) => mv m (wr c tp)) t a) q'' t' ->
      eval M q t q'' t'.

End Fix_Alphabet.

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

Definition HaltMTM : {'(n,Σ) : nat * finType & mTM Σ n & Vector.t (tape Σ) n} -> Prop :=
  fun '(existT2 _ _ (n, Σ) M t) => HaltsTM M t.
