(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland Informatics Campus, Saarland University, Saarbrücken, Germany
*)

(* 
  Problem(s):
    Provability in Hilbert-style calculi (HSC_PRV)

    Recognizing axiomatizations of Hilbert-style calculi (HSC_AX)
    (Linial-Post theorem, strengthened by Bokov [1,2])

  HSC_PRV:
    Fix a list s₁,...,sₙ of formulae.
    Given a formula s, is [s₁,...,sₙ] ⊢ s derivable?

  HSC_AX:
    Given a list s₁,...,sₙ of formulae such that 
    [a → b → a] ⊢ sᵢ is derivable for i = 1...n,
    is [s₁,...,sₙ] ⊢ a → b → a derivable?
  
  References:
    [1] Grigoriy V. Bokov: Undecidable problems for propositional calculi with implication. 
      Logic Journal of the IGPL, 24(5):792–806, 2016. doi:10.1093/jigpal/jzw013
    [2] Andrej Dudenhefner, Jakob Rehof: Lower End of the Linial-Post Spectrum. 
      TYPES 2017: 2:1-2:15. doi: 10.4230/LIPIcs.TYPES.2017.2
*)

Require Import PeanoNat.
Require Import List.
Import ListNotations.

(* propositional formulae s, t ::= a | s → t *)
Inductive formula : Set :=
  | var : nat -> formula
  | arr : formula -> formula -> formula.

(* the formula a → b → a *)
Definition a_b_a : formula := arr (var 0) (arr (var 1) (var 0)).

(* substitute ζ t replaces each variable n in t by ζ n *)
Fixpoint substitute (ζ: nat -> formula) (t: formula) : formula :=
  match t with
  | var n => ζ n
  | arr s t => arr (substitute ζ s) (substitute ζ t)
  end.

(* Hilbert-style calculus *)
Inductive hsc (Gamma: list formula) : formula -> Prop :=
  | hsc_var : forall (ζ: nat -> formula) (t: formula), In t Gamma -> hsc Gamma (substitute ζ t)
  | hsc_arr : forall (s t : formula), hsc Gamma (arr s t) -> hsc Gamma s -> hsc Gamma t.

(* single formula *)
Definition HSC_PRV_PROBLEM := formula.

(* is the formula s derivable from the formulae Gamma? *)
Definition HSC_PRV (Gamma: list formula) (s: HSC_PRV_PROBLEM) := hsc Gamma s.

(* list of formulae derivable from a → b → a *)
Definition HSC_AX_PROBLEM := { Gamma: list formula | forall s, In s Gamma -> hsc [a_b_a] s}.

(* is the formula a → b → a derivable? *)
Definition HSC_AX (l: HSC_AX_PROBLEM) := hsc (proj1_sig l) a_b_a.
