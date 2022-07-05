(** * Halting problem for multi-tape and single-tape Turing machines HaltMTM and HaltTM 1  *)

Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypesDef.
Require Import Vector List.

Unset Implicit Arguments.

(* * Turing machines  *)

(* The definition of Turing machines is due to Asperti & Ricciotti's "A formalization of multi-tape Turing machines" (2015) and the accompanying Matita code. *)  

Section Fix_Sigma.

  (* The alphabet type *)
  Variable Σ : Type.

  (* ** Tapes

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

  (* The current function returns the current symbol, if there is one. If None is returned, this means that the head is on a part of the tape which has never been written before.  *)

  Definition current (t : tape) : option Σ :=
    match t with
    | midtape _ a _ => Some a
    | _ => None
    end.

  Inductive move : Type := Lmove : move | Rmove : move | Nmove : move.

  (* Moving to the left on leftof and to the right on rightof has no effect.
   *)

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

  (* The write function wr takes option Σ as argument. None indicates that nothing should be written. This is necessary because the current symbol might be None, i.e. one can not simply write the current symbol since it might not exist.  *)

  Definition wr (s : option Σ) (t : tape) : tape :=
    match s, t with
    | None, t => t
    | Some a, niltape => midtape nil a nil
    | Some a, leftof r rs => midtape nil a (r :: rs)
    | Some a, midtape ls b rs => midtape ls a rs
    | Some a, rightof l ls => midtape (l :: ls) a nil
    end.

End Fix_Sigma.

(* Differences to traditional presentations:

The tape representation and the implementation of mv is different to presentations of Turing machines in the literature. Moving to the right while on a rightof tape is the identity. One can obtain the more traditional behaviour by assuming a blank symbol as part of the alphabet and always writing a blank when the current symbol is None.

This also means that moving n steps to the right, and then n steps to the left does not yield the same tape, since the moves to the right might have been uneffective. With an explicit blank symbol, moving n steps to the right while always writing the current symbol and the blank if current is None, and the moving n steps to the left is semantically the identity, but still not syntactically.

*)

Arguments niltape _, {_}.
Arguments leftof _ _ _, {_} _ _.
Arguments rightof _ _ _, {_} _ _.
Arguments midtape _ _ _ _, {_} _ _ _.

Arguments current {_} _.

Arguments wr {_} _ _.
Arguments mv {_} _.

Section Fix_Alphabet.

  (* The alphabet type, assumed as finite type *)
  Variable Σ : finType.

   (* finType is defined as a pair of a type with decidable equality, and a duplicate-free list of all elements of the type.

      We have

      Lemma finType_equiv (X : finType) :
         {n & {f : X -> Fin.t n & { g : Fin.t n -> X | (forall x, g (f x) = x) /\ forall i, f (g i) = i }}}.

      in Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypesEquiv.

   *)
  
  (* The number of tapes  *)
  Variable n : nat.

  (* Definition of multi-tape Turing machines  *)
  Record TM : Type :=
    {
    (* type of states of the TM: *)
    state : finType;
    (* transition function: *)
    trans : state * (Vector.t (option Σ) n) -> state * (Vector.t ((option Σ) * move) n);
    (* start state: *)
    start: state;
    (* decidable subset of halting states: *)
    halt : state -> bool 
    }.

  (* evaluation relation, uses trans until a halting state is reached:  *)
  Inductive eval (M : TM) (q : state M) (t : Vector.t (tape Σ) n) : state M -> Vector.t (tape Σ) n -> Prop :=
  | eval_halt :
      halt M q = true ->
      eval M q t q t
  | eval_step q' a q'' t' :
      halt M q = false ->
      trans M (q, Vector.map current t) = (q', a) ->
      eval M q' (Vector.map2 (fun tp '(c,m) => mv m (wr c tp)) t a) q'' t' ->
      eval M q t q'' t'.

End Fix_Alphabet.

Arguments state {_ _} m : rename.
Arguments trans {_ _} m _, {_ _ m} _ : rename.
Arguments start {_ _} m : rename.
Arguments halt {_ _} m _, {_ _ m} _ : rename.

Arguments eval {_ _} _ _ _ _ _.

Arguments Build_TM {_ _ _} _ _ _.

Definition HaltsTM {Σ: finType} {n: nat} (M : TM Σ n) (t : Vector.t (tape Σ) n) :=
  exists q' t', eval M (start M) t q' t'.
Arguments HaltsTM _ _ _ _, {_ _} _ _.

Definition HaltTM (n : nat) : {Σ : finType & TM Σ n & Vector.t (tape Σ) n} -> Prop :=
  fun '(existT2 _ _ Σ M t) => HaltsTM M t.

Definition HaltMTM : {'(n,Σ) : nat * finType & TM Σ n & Vector.t (tape Σ) n} -> Prop :=
  fun '(existT2 _ _ (n, Σ) M t) => HaltsTM M t.

Import ListNotations Vector.VectorNotations.

Definition encNatTM {Σ : Type} (s b : Σ) (n : nat) :=
  @midtape Σ [] b (repeat s n).

Definition TM_computable {k} (R : Vector.t nat k -> nat -> Prop) := 
  exists n : nat, exists Σ : finType, exists s b : Σ, s <> b /\ 
  exists M : TM Σ (1 + k + n),
  forall v : Vector.t nat k, 
  (forall m, R v m <-> exists q t, TM.eval M (start M) ((niltape :: Vector.map (encNatTM s b) v) ++ Vector.const niltape n) q t
                                /\ Vector.hd t = encNatTM s b m) /\
  (forall q t, TM.eval M (start M) ((niltape :: Vector.map (encNatTM s b) v) ++ Vector.const niltape n) q t ->
          exists m, Vector.hd t = encNatTM s b m).
