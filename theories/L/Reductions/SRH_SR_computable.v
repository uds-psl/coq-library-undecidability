From Undecidability.L Require Import Reductions.MPCP_PCP_computable.
From Undecidability.PCP Require Import SRH_SR.

Definition red := (fun '(R, x, a) => (P R x a, x, [a])).

Instance computable_Sigma : computable Sigma.
Proof.
  extract.
Defined.

Definition card1 (a0 : symbol) := (fun a => [a; a0] / [a0]).
Definition card2 (a0 : symbol) := (fun a => [a0; a] / [a0]).

Instance internalize_card1 : computable card1.
Proof.
  extract.
Defined.

Instance internalize_card2 : computable card2.
Proof.
  extract.
Defined.

Instance internalize_P : computable P.
Proof.
  change P with
      (fun (R : SRS) (x0 : Definitions.string) (a0 : symbol) =>
         R ++
           map (card1 a0) (a0 :: x0 ++ sym R) ++ map (card2 a0) (a0 :: x0 ++ sym R)).
  extract.
Defined.

Instance internalize_red : computable red.
Proof.
  extract.
Defined.
