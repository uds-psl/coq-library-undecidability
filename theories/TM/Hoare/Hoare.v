(* * A New Logic  for the specification of Turing Machines, Based on Hoare Logic *)

From Undecidability.TM.Hoare Require Export HoareLogic. (* Abstract definition of Hoare triples *)
From Undecidability.TM.Hoare Require Export HoareCombinators. (* Rules for the combinators *)
From Undecidability.TM.Hoare Require Export HoareRegister. (* Definition of a specification language for Register machines; rules for lifts *)
From Undecidability.TM.Hoare Require Export HoareTactics HoareTacticsView. (* Verification step tactics *)
From Undecidability.TM.Hoare Require Export HoareStdLib. (* Hoare rules for standard machine *)
From Undecidability.TM.Hoare Require Export HoareLegacy. (* generating Legacy Lemmas for Realise/Terminates *)


(* TODO:
- Prefix "_size" or "_space"?
- Univ
*)
