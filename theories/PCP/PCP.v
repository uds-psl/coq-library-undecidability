(** * Post Correspondence problem PCP *)

(* Definitions of variants of the Post correspondence problem. *)

From Stdlib Require Import List.
Import ListNotations.


(* A string is a list of symbols. *)
Notation string := list.

(* A card a is a pair of the upper string x and the lower string y. *)
Notation card := (fun X => string X * string X)%type.

(* A stack is a list of cards. *)
Definition stack X := list (card X).

(* The upper trace tau1 of a stack A 
  is the concatenation of the upper strings of A. *)
Fixpoint tau1 {X : Type} (A : stack X) : string X :=
  match A with
  | [] => []
  | (x, y) :: A => x ++ tau1 A
  end.

(* The lower trace tau2 of a stack A 
  is the concatenation of the lower strings of A. *)
Fixpoint tau2 {X : Type} (A : stack X) : string X :=
  match A with
  | [] => []
  | (x, y) :: A => y ++ tau2 A
  end.

(* The Post correspondence problem PCP is 
  given a stack P of cards to determine 
  whether there is a non-empty stack A of cards from P (with possible repetition)
  such that the upper trace of A is equal to the lower trace of A. *)
Definition PCPX {X : Type}: stack X -> Prop :=
  fun P => exists A, incl A P /\ A <> [] /\ tau1 A = tau2 A.

Definition PCP : stack nat -> Prop := @PCPX nat.

(* PCPb is PCP restricted to cards with binary strings. *)
Definition PCPb : stack bool -> Prop := @PCPX bool.

(* The indexed upper trace itau1 of indices A from a stack P
  is the concatenation of the upper strings of P each with index from A. *)
Fixpoint itau1 {X : Type} (P : stack X) (A : list nat) : string X :=
  match A with
    | [] => []
    | i :: A => fst (nth i P ([], [])) ++ itau1 P A
  end.

(* The indexed lower trace itau1 of indices A from a stack P
  is the concatenation of the upper strings of P each with index from A. *)
Fixpoint itau2 {X : Type} (P : stack X) (A : list nat) : string X :=
  match A with
    | [] => []
    | i :: A => snd (nth i P ([], [])) ++ itau2 P A
  end.

(* iPCPb is a different presentation of PCPb based on index lists. *)
Definition iPCPb : stack bool -> Prop :=
  fun P => exists (A : list nat), 
    (forall a, In a A -> a < length P) /\ A <> [] /\ itau1 P A = itau2 P A.

(* A pair of words is derivable from a stack P 
  if it can be build by concatenation of upper and lower strings of cards from P. *)
Inductive derivable {X : Type} (P : stack X) : string X -> string X -> Prop :=
  | der_sing x y : In (x, y) P -> derivable P x y
  | der_cons x y u v : In (x, y) P -> derivable P u v -> derivable P (x ++ u) (y ++ v).

(* dPCPb is a different presentation of inductive presentation of PCP. *)
Definition dPCP {X : Type} : stack X -> Prop :=
  fun P => exists u, @derivable X P u u.

(* dPCPb is a different presentation of PCPb based in index derivability. *)
Definition dPCPb : stack bool -> Prop := @dPCP bool.

(* Binary PCP inductively defined (cf Trakhtenbrot IJCAR 2020) *)

Inductive BPCP (P : stack bool) : Prop := 
  | cBPCP : forall u, derivable P u u -> BPCP P.

(* The modified Post correspondence problem MPCP is 
  given a card x/y and stack P of cards to determine 
  whether there is a stack A of cards from x/y, P (with possible repetition)
  such that the upper trace of x/y, A is equal to the lower trace of x/y,A. *)
Definition MPCP : card nat * stack nat -> Prop :=
  fun '((x, y), P) => exists (A : stack nat), 
    incl A ((x, y) :: P) /\ x ++ tau1 A = y ++ tau2 A.

(* MPCPb is MPCP restricted to cards with binary strings. *)
Definition MPCPb : card bool * stack bool -> Prop :=
  fun '((x, y), P) => exists (A : stack bool), 
    incl A ((x, y) :: P) /\ x ++ tau1 A = y ++ tau2 A.