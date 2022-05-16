From Undecidability.FOL.Semantics Require Import Tarski.FullFacts.
From Undecidability.FOL.Syntax Require Import Facts.
Require Import Undecidability.Synthetic.DecidabilityFacts.
Require Import List.

#[global]
Existing Instance falsity_on.

(* Definition of finiteness *)

Definition listable X :=
  exists L, forall x : X, In x L.

Section DefaultSyntax. (* An alternative development of FSAT in Trakhtenbrot is "Trakhtenbrot Syntax" *)
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  (* Satisfiability in a finite and decidable model *)

  Definition FSAT (phi : form) :=
    exists D (I : interp D) rho, listable D /\ (forall p, decidable (fun v => i_atom (P:=p) v)) /\ rho ⊨ phi.

  (* Validity in a finite and decidable model *)

  Definition FVAL (phi : form) :=
    forall D (I : interp D) rho, listable D /\ (forall p, decidable (fun v => i_atom (P:=p) v)) -> rho ⊨ phi.


  (* Satisfiability in a discrete, finite, and decidable model *)

  Definition FSATd (phi : form) :=
    exists D (I : interp D) rho, listable D /\ discrete D /\ (forall p, decidable (fun v => i_atom (P:=p) v)) /\ rho ⊨ phi.

  (* Satisfiability in a discrete, finite, and decidable model restricted to closed formulas *)

  Definition cform := { phi | bounded 0 phi }.

  Definition FSATdc (phi : cform) :=
    FSATd (proj1_sig phi).
End DefaultSyntax.
