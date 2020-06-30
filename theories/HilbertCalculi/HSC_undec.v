(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Undecidability Result(s):
    Provability in Hilbert-style calculi (HSC_PRV)
    Recognizing axiomatizations of Hilbert-style calculi (HSC_AX)
*)

Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.HilbertCalculi.HSC.

Require Undecidability.HilbertCalculi.Reductions.MPCPb_to_HSC_PRV.
Require Undecidability.HilbertCalculi.Reductions.MPCPb_to_HSC_AX.

Require Import Undecidability.PCP.PCP_undec.

(* Hilbert-style Axiomatization of the Post Correspondenc Problem *)
Definition ΓPCP := MPCPb_to_HSC_PRV.Argument.ΓPCP.

(* Undecidability of Provability in Hilbert-style Calculi with the Fixed Environment ΓPCP *)
Theorem HSC_PRV_undec : undecidable (HSC_PRV ΓPCP).
Proof.
  apply (undecidability_from_reducibility MPCPb_undec).
  exact MPCPb_to_HSC_PRV.reduction.
Qed.

Check HSC_PRV_undec.

(* Undecidability of Recognizing Axiomatizations of Hilbert-style Calculi *)
Theorem HSC_AX_undec : undecidable HSC_AX.
Proof.
  apply (undecidability_from_reducibility MPCPb_undec).
  exact MPCPb_to_HSC_AX.reduction.
Qed.

Check HSC_AX_undec.
