From Undecidability.FOL Require Import FSAT.
From Undecidability.FOL.Util Require Import Syntax_facts FullTarski_facts sig_bin.
Export Undecidability.FOL.Util.Syntax.FullSyntax.
From Undecidability.SeparationLogic Require Import min_seplogic.

From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.

(** encoding function **)

Fixpoint encode {b : falsity_flag} (phi : form) : msp_form :=
  match phi with
  | falsity => mbot
  | atom _ v => let x := match Vector.hd v with var x => x | func f _ => match f with end end in
               let y := match Vector.hd (Vector.tl v) with var y => y | func f _ => match f with end end in
               mand (mex (mpointer (Some 0) (Some (S x)) (Some (S y))))
                    (mand (mpointer (Some x) None None) ((mpointer (Some y) None None)))
  | bin Impl phi psi => mimp (encode phi) (encode psi)
  | bin Conj phi psi => mand (encode phi) (encode psi)
  | bin Disj phi psi => mor (encode phi) (encode psi)
  | quant All phi => mall (mimp (mpointer (Some 0) None None) (encode phi))
  | quant Ex phi => mex (mand (mpointer (Some 0) None None) (encode phi))
  end.

Definition encode' (phi : form) : msp_form :=
  mimp (mex (mpointer (Some 0) None None)) (encode phi).

Require Import Undecidability.Synthetic.Definitions.

Theorem reduction :
  FSAT ⪯ MSPSAT.
Proof.
  exists encode'.
Admitted.
