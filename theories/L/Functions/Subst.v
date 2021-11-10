From Undecidability.L Require Import Tactics.LTactics Functions.EqBool.
From Undecidability.L.Datatypes Require Import LNat LTerm LBool.
Require Import Nat .
Import EqBool.

(* ** Extracted substitution on terms *)
Global
Instance term_substT :
  computableTime' subst (fun s _ => (5, (fun n _ => (1, (fun t _ => ( (size s) * (size s + c__eqbComp nat * 4 + 20), tt)))))).
Proof.
  extract. unfold eqbTime.
  recRel_prettify2. all:unfold eqbTime; cbn [fst snd size].
  all:try rewrite !size_nat_enc.
  all: unfold c__natsizeS, c__natsizeO in *. 
  all:try nia.
Qed.
