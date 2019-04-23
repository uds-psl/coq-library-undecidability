From Undecidability.L Require Import Reductions.MPCP_PCP_computable.
From Undecidability.PCP Require Import SR_MPCP.

Definition red := (fun '(R, x, y) => (d R x y, P R x y)).

Instance computable_Sigma : computable Sigma.
Proof.
  extract.
Defined.

Instance computable_dollar : computable dollar.
Proof.
  extract.
Defined.

Instance computable_hash : computable hash.
Proof.
  extract.
Defined.

Instance internalize_d : computable d.
Proof.
  extract.
Defined.

Instance internalize_e : computable e.
Proof.
  extract.
Defined.

Definition singcard := (fun a : symbol => [a] / [a]).

Instance internalize_singcard : computable singcard.
Proof.
  extract.
Defined.

Instance internalize_P : computable P.
Proof.
  change P with
      (fun (R : SRS) (x0 y0 : Definitions.string) =>
         [d R x0 y0; e R x0 y0] ++ R ++ [[hash R x0 y0] / [hash R x0 y0]] ++ map singcard (x0 ++ y0 ++ sym R)).
  extract.
Defined.

Instance internalize_red : computable red.
Proof.
  extract.
Defined.
