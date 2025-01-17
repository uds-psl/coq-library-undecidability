(* * Base Library for ICL

   - Version: 3 October 2016
   - Author: Gert Smolka, Saarland University
   - Acknowlegments: Sigurd Schneider, Dominik Kirst, Yannick Forster, Fabian Kunze, Maximilian Wuttke
 *)

From Stdlib Require Export Bool Lia List Setoid Morphisms Arith.
From Undecidability.Shared.Libs.PSL Require Export Tactics.
From Stdlib Require Import FinFun.

Global Set Implicit Arguments. 
Global Unset Strict Implicit.
Global Unset Printing Records.
Global Unset Printing Implicit Defensive.

Notation injective := FinFun.Injective.
Notation surjective := FinFun.Surjective.
