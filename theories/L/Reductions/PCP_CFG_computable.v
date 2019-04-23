From Undecidability.PCP Require Import PCP_CFI Definitions.
From Undecidability.L.Tactics Require Export LTactics.
From Undecidability.L.Datatypes Require Export LNat LProd Lists.
From Undecidability.L Require Import Reductions.MPCP_PCP_computable.

Instance internalize_Sigma : computable PCP_CFI.Sigma.
Proof.
  extract.
Defined.

Definition fn1 P := (fun '(x / y) =>
   x / (x ++ [fresh (PCP_CFI.Sigma P)] ++ y ++ [fresh (PCP_CFI.Sigma P)])%list).

Instance computable_fn1 : computable fn1.
Proof.
  extract.
Defined.

Instance computable_gamma1 : computable gamma1.
Proof.
  change gamma1 with (fun P A => map (fn1 P) A).
  extract.
Defined.

Definition fn2 P := (fun '(x / y) =>
   y / (x ++ [fresh (PCP_CFI.Sigma P)] ++ y ++ [fresh (PCP_CFI.Sigma P)])%list).

Instance computable_fn2 : computable fn2.
Proof.
  extract.
Defined.

Instance computable_gamma2 : computable gamma2.
Proof.
  change gamma2 with (fun P A => map (fn2 P) A).
  extract.
Defined.

Instance computable_red : computable (fun P => (gamma1 P P, gamma2 P P, fresh (sym P))).
Proof.
  extract.
Defined.

From Undecidability.PCP Require Import PCP_CFP.

Definition fn : Definitions.card -> _ := (fun '(x / y) => x / rev y).

Instance computable_fn : computable fn.
Proof.
  unfold Definitions.card.
  extract.
Defined.

Instance computable_gamma : computable gamma.
Proof.
  change gamma with (fun A => map fn A).
  extract.
Defined.

Instance internalize_red' : computable (fun P => (gamma P, fresh (sym P))).
Proof.
  extract.
Defined.
