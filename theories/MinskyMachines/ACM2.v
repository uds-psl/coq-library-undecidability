(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Utf8.

#[local] Set Implicit Arguments.

Section And_Branching_Two_Counter_Machines.

  (* locations: index type for instructions, normally is nat *)
  Variables loc : Set.

  (* Four instructions: INCₐ, DECₐ, FORKₐ and STOPₐ
     See eg

     "Decision problems for propositional linear logic" 
       by Lincoln, Mitchell, Scedrov & Shankar
       Annals of Pure and Applied Logic 56 (1992) 239-311
       https://doi.org/10.1016/0168-0072(92)90075-B
 
     only two nat valued registers, indexed with bool
     ie true/α of which the values are denoted "x" below
     and false/β of which the values are denoted "y" below 

     In any of the cases above, several instructions can 
     co-exist at a given location. This model is
     inherently non-deterministic and may contain
     parallel (but non-interacting) computations.

     STOPₐ p:     accepts location p when α = β = 0
     INCₐ x p q:  at location p, x += 1 and jumps to location q
     DECₐ x p q:  at location p, x -= 1 (if possible) and jumps to location q
                  if x is already 0 then this instruction cannot compute
     FORKₐ p q r: at location p, fork to locations q and r 

     *)

  Inductive acm2_instr : Set :=
    | acm2_stop    : loc  → acm2_instr
    | acm2_inc     : bool → loc → loc → acm2_instr
    | acm2_dec     : bool → loc → loc → acm2_instr
    | acm2_fork    : loc  → loc → loc → acm2_instr.

  Abbreviation α := true.
  Abbreviation β := false.

  Abbreviation FORKₐ := acm2_fork.
  Abbreviation INCₐ  := acm2_inc.
  Abbreviation DECₐ  := acm2_dec.
  Abbreviation STOPₐ := acm2_stop.

  Infix "∊" := In (at level 70).

  (* Programs are non-deterministic and described by 
     a (finite) list of instructions 

     Notice that eg 

          [ STOPₐ 0 ; INCₐ α 0 4 ; DECₐ β 0 2 ; FORKₐ 0 4 5 ]

     can both accept location 0 (if α, β are not 0)
     or increment α and jump to location 4
     or decrement β (if possible) and jump to location 2
     or fork to locations 4 and 5 

     Also repetitions and order do not matter hence these
     lists are viewed as finite sets, see remark 
     acm2_accept_mono in ACM2/acm2_utils.v
  *)

  Reserved Notation "Σ ⫽ₐ x ⊕ y ⊦ p" (at level 70, no associativity).

  (* Σ ⫽ₐ x ⊕ y ⊦ p denotes 

         "Σ accepts the initial location p with values α:=x and β:=y"

    This big step semantics only describes the overall "accept" 
    predicate and does not capture the tree of computations. *)

  Inductive acm2_accept (Σ : list acm2_instr) : nat → nat → loc → Prop :=

    | in_acm2a_stop p :          STOPₐ p ∊ Σ      →  Σ ⫽ₐ   0 ⊕   0 ⊦ p

    | in_acm2a_fork x y p q r :  FORKₐ p q r ∊ Σ  →  Σ ⫽ₐ   x ⊕   y ⊦ q
                                                  →  Σ ⫽ₐ   x ⊕   y ⊦ r
                                                  →  Σ ⫽ₐ   x ⊕   y ⊦ p

    | in_acm2a_inc_a x y p q :   INCₐ α p q ∊ Σ   →  Σ ⫽ₐ 1+x ⊕   y ⊦ q
                                                  →  Σ ⫽ₐ   x ⊕   y ⊦ p

    | in_acm2a_inc_b x y p q :   INCₐ β p q ∊ Σ   →  Σ ⫽ₐ   x ⊕ 1+y ⊦ q
                                                  →  Σ ⫽ₐ   x ⊕   y ⊦ p

    | in_acm2a_dec_a x y p q :   DECₐ α p q ∊ Σ   →  Σ ⫽ₐ   x ⊕   y ⊦ q
                                                  →  Σ ⫽ₐ 1+x ⊕   y ⊦ p

    | in_acm2a_dec_b x y p q :   DECₐ β p q ∊ Σ   →  Σ ⫽ₐ   x ⊕   y ⊦ q
                                                  →  Σ ⫽ₐ   x ⊕ 1+y ⊦ p

  where "Σ ⫽ₐ x ⊕ y ⊦ u" := (acm2_accept Σ x y u).

  (* A problem is a list of instructions Σ, a start location p 
     and initial values (x,y) for α/β *)

  Definition ACM2_problem := ( list acm2_instr * loc * (nat * nat) )%type.

  (* The question is Σ ⫽ₐ x ⊕ y ⊦ p ? *)

  Definition ACM2_ACCEPT (i : ACM2_problem) : Prop :=
    match i with (Σ,p,(x,y)) => Σ ⫽ₐ x ⊕ y ⊦ p end.

End And_Branching_Two_Counter_Machines.

#[global] Arguments acm2_fork {_}.
#[global] Arguments acm2_stop {_}.
#[global] Arguments acm2_inc {_}.
#[global] Arguments acm2_dec {_}.

Module ACM2_Notations.

  Abbreviation FORKₐ := acm2_fork.
  Abbreviation INCₐ  := acm2_inc.
  Abbreviation DECₐ  := acm2_dec.
  Abbreviation STOPₐ := acm2_stop.

  Notation "s ⫽ₐ x ⊕ y ⊦ p" := (@acm2_accept _ s x y p) (at level 70).

End ACM2_Notations.





