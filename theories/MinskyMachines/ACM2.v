(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Utf8.

Set Implicit Arguments.

Section And_Branching_Two_Counter_Machines.

  (* locations: index type for instructions, normally is nat *)

  Variables loc : Set.

  (* three instructions: INCₐ, DECₐ, FORKₐ and STOPₐ
     See eg

     https://pdf.sciencedirectassets.com/271596/1-s2.0-S0168007200X01996/1-s2.0-016800729290075B/main.pdf?X-Amz-Security-Token=IQoJb3JpZ2luX2VjENL%2F%2F%2F%2F%2F%2F%2F%2F%2F%2FwEaCXVzLWVhc3QtMSJHMEUCIA4wDNbpp2SpTdmcr5a4K%2Fpn1%2FZb8kIi%2BvEq5lCLgDsOAiEAmUlGejtLFVFFsKmJApjjYo3dBP6KsCktU4Uv9W0nNegqvAUImv%2F%2F%2F%2F%2F%2F%2F%2F%2F%2FARAFGgwwNTkwMDM1NDY4NjUiDJFMonc5KUhExNrFWiqQBZ0Kkpu8x68Vma53He043d4tTk%2BTr9qmj7kFRq%2BtL%2BWjhLQ5pVBQ04m0VxtquB2MsRyTt%2FOIjCiEpAEgf%2BqO8PohiXoNAEhsLzEXPTNkgDKnfOT%2FZXSx%2B4nKo%2BejLDxzxYuM%2BIptuGMrixWPctrCLkO1Ru0TwyyDqlEmwLY%2FGp0sYkOuCmWMsZ6%2B7UXbRZ3TuaZsyC1xzbWI2QwuDvX4QPqzXaKouXskO1Ccobp5uLpX5cQtvi9nxDmOjHuHw%2Bzq0rVd8YXgSvKuNrnHmYlsDJLPy%2BPSZtbvrT%2Fvv87esWL3tcUttXqE6aoUiccMT1vlHJGzJ37czpz7QNNJ4ftubjB%2F9wHJBfLsD25qCk9fQuKQevSJx2Jy7%2FchIR7%2BG2xaBLJesmFyeg89IBEeSMUgCaTmZCIVAiqDbXyMHFUXLyV4W5Mrs%2FQFKDLk%2BMRqo1vXQ4N7Kzq6Jm6XuDpubLrdcbcSGPSTiMcLRYlBB6xNn5MXrhAit3DI4RXCijfHDgrV3gbDRLxn83gjw%2FdbPq8bUl4YBUaZ2TgXdEuKAW8WxsWUcrPBGCNbiww0lUrGBIwGTRFNWOnJ5qtWoebjx1yrhUL337iOFYSRXWVfck%2F58YWXgZj07A49L4e0a%2Fqr6rPhTMM3ZH4KLZnF8vgmkolmTF5%2Btt%2F%2FG00rp7U8Jhz87YKsir%2B60KFNWOMH9A5FeElX2vvZYcwBlqM9rzkzpRLRO2SC7xqjd5A6xwSskwh3GNIASFsvVy19rHV%2FgyQNiVy0YLrunwjNGtkBF%2FhcgczfyVerkYx9jnvpEg5DkB5g5QZmRnf99%2FwYdgWr%2Bqg5wmq12X5g%2Fg0EXAr0%2B9ZwY10ZoszWIdd6OQfk2e8850HYuU2GMPeMi84GOrEBvpQD%2Ff%2FX5fMee05rbi6BCgWwfyUF0ITUJKIZ%2BYWIMbY6A3eb5LD7ezvfj6W%2B4P34ZJcrDL3oPaz6q7OpURH0L0XFoC%2FFzaYXi3o3Gyy0dQYXZR4dO8v93OyZiRjM1pyfmgmbKxdMJUmritzt1%2BBnE425EFOCvSw8KFignUMrIH7q2ukz%2BP5%2FpaoGg2c9Gc7ignqjM41E4qHztyr8Piy57ZGhM4hW1dKspEhTfAv7CyDK&X-Amz-Algorithm=AWS4-HMAC-SHA256&X-Amz-Date=20260324T184630Z&X-Amz-SignedHeaders=host&X-Amz-Expires=300&X-Amz-Credential=ASIAQ3PHCVTY2YEE2OBH%2F20260324%2Fus-east-1%2Fs3%2Faws4_request&X-Amz-Signature=bb63799f88b24894205cd36742828506f79d0f8162676c523b01be027e2dd672&hash=8d68edc88c08179dc338bb44a1b5783556d8daa40f7e877c7908659d37aa952d&host=68042c943591013ac2b2430a89b270f6af2c76d8dfd086a07176afe7c76c2c61&pii=016800729290075B&tid=spdf-b6904c96-6aaf-4f2c-9d98-991d051fc116&sid=c9457054500b5943187b5e57f7e2221ff37agxrqb&type=client&tsoh=d3d3LnNjaWVuY2VkaXJlY3QuY29t&rh=d3d3LnNjaWVuY2VkaXJlY3QuY29t&ua=08175b025156035001&rr=9e17d6c919d00636&cc=fr

     only two nat valued registers, indexed with bool
     ie true/α of which the values are denoted "a" below
     and false/β of which the values are denoted "b" below 

     In any of the cases above, several instructions can 
     co-exist at a given location, hence, no instruction
     can stop the computation by itself. This model is
     inherently no-deterministic.

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

  Notation α := true.
  Notation β := false.

  Notation FORKₐ := acm2_fork.
  Notation INCₐ  := acm2_inc.
  Notation DECₐ  := acm2_dec.
  Notation STOPₐ := acm2_stop.

  Infix "∊" := In (at level 70).

  (* Programs are non-deterministic and described by 
     a (finite) list of instructions 

     Notice that eg 

          [ STOPₐ 0 ; INCₐ α 0 4 ; DECₐ β 0 2 ; FORKₐ 0 4 5 ]

     can both accept location 0 (if α = β = 0)
     or increment α and jump to location 4
     or decrement β (if not zero already) and jump to location 2
     or fork to locations 4 and 5 

     Also repetitions and order do not matter hence these
     lists are viewed as finite sets, see acm2_accept_mono 
     in ACM2/acm2_utils.v
  *)

  Reserved Notation "Σ ⫽ₐ a ⊕ b ⊦ u" (at level 70, no associativity).

  (* Σ ⫽ₐ a ⊕ b ⊦ u denotes 

         "Σ accepts the initial location u with values α:=a and β:=b"

    This big step semantics only describes the overall accepts predicate
    and does not capture output values.

   *)

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

  (* A problem is a program, a start location and initial values for α/β *)

  Definition ACM2_problem := { Σ : list acm2_instr & loc * (nat * nat) }%type.

  Definition ACM2_ACCEPT (i : ACM2_problem) : Prop := 
    match i with existT _ Σ (u,(a,b)) => Σ ⫽ₐ a ⊕ b ⊦ u end.

End And_Branching_Two_Counter_Machines.

Arguments acm2_fork {_}.
Arguments acm2_stop {_}.
Arguments acm2_inc {_}.
Arguments acm2_dec {_}.

Module ACM2_Notations.

  Notation FORKₐ := acm2_fork.
  Notation INCₐ  := acm2_inc.
  Notation DECₐ  := acm2_dec.
  Notation STOPₐ := acm2_stop.

  Notation "s ⫽ₐ x ⊕ y ⊦ u" := (@acm2_accept _ s x y u) (at level 70).

End ACM2_Notations.





