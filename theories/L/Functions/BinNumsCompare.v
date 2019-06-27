From Undecidability.L Require Import Tactics.LTactics.
Require Import Numbers.BinNums.
From Undecidability.L.Datatypes Require Import LBinNums LComparison LNat LBool.
Instance termT_Pos_compare_cont : computableTime' Pos.compare_cont (fun _ _ => (5,fun x _ => (1,fun y _ => (min (Pos.size_nat x) (Pos.size_nat y)*17,tt)))).
Proof.
  extract. solverec.
Qed.

Instance term_Pos_compare : computableTime' Pos.compare (fun x _ => (7,fun y _ => (min (Pos.size_nat x) (Pos.size_nat y)*17,tt))).
Proof.
  change Pos.compare with (fun x => Pos.compare x). unfold Pos.compare.
  extract. solverec.
Qed.

Instance termT_N_compare : computableTime' N.compare (fun x _ => (1,fun y _ => (min (N.size_nat x) (N.size_nat y)*17+ 16,tt))).
Proof.
  extract. solverec.
Qed.

Instance termT_N_leb : computableTime' N.leb (fun x _ => (1,fun y _ => (min (N.size_nat x) (N.size_nat y)*17+ 22,tt))).
Proof.
  extract. solverec.
Qed.

Instance termT_N_ltb : computableTime' N.ltb  (fun x _ => (1,fun y _ => (min (N.size_nat x) (N.size_nat y)*17+ 22,tt))).
Proof.
  extract. solverec.
Qed.

Instance termT_N_eqb : computableTime' N.eqb  (fun x _ => (1,fun y _ => (min (N.size_nat x) (N.size_nat y)*17+ 22,tt))).
Proof.
  eapply computableTimeExt with (x:=fun x y : N => match (x ?= y)%N with
                       | Eq => true
                       | _ => false
                                                end).
  -repeat intro. hnf. now rewrite N.eqb_compare.
  -extract. solverec.
Qed.
