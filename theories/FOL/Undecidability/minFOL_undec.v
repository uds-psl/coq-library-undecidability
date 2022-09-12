(** ** Signature Minimisation *)

From Undecidability.DiophantineConstraints Require Import H10C H10C_undec.
From Undecidability.FOL.Syntax Require Import Core BinSig.
From Undecidability.FOL Require Semantics.Tarski.FragmentFacts Deduction.FragmentNDFacts Semantics.Kripke.FragmentCore Semantics.FiniteTarski.Fragment.
From Undecidability.FOL Require Semantics.Tarski.FragmentFacts Deduction.FullNDFacts.
From Undecidability.FOL.Undecidability.Reductions Require H10UPC_to_FOL_minimal.
From Undecidability.FOL.Undecidability.Reductions Require H10UPC_to_FOL_full_fragment H10UPC_to_FSAT.
From Undecidability.Synthetic Require Import Definitions Undecidability ReducibilityFacts.

Set Default Proof Using "Type".

Definition minimalForm (ff:falsity_flag) := @form sig_empty sig_binary FragmentSyntax.frag_operators ff.


Section full_fragment.
  Import H10UPC_to_FOL_full_fragment.
  Import Undecidability.FOL.Semantics.Tarski.FullFacts.

  Lemma minSignatureValiditiyUndec : @undecidable (@form sig_empty sig_binary FullSyntax.full_operators falsity_on) valid.
  Proof.
    apply (undecidability_from_reducibility H10UPC_SAT_undec).
    exact fullFragValidReduction.
  Qed.
End full_fragment.

Section general.
  Import H10UPC_to_FOL_minimal.
  Import Semantics.Tarski.FragmentFacts Deduction.FragmentNDFacts Semantics.Kripke.FragmentCore.

  Lemma minValidityUndec : undecidable (fun k : minimalForm falsity_off => valid k).
  Proof.
    apply (undecidability_from_reducibility H10UPC_SAT_undec).
    exact validReduction.
  Qed.

  Lemma minKripkeValidityUndec : undecidable (fun k : minimalForm falsity_off => kvalid k).
  Proof.
    apply (undecidability_from_reducibility H10UPC_SAT_undec).
    exact kripkeValidReduction.
  Qed.

  Definition int_provable (phi : minimalForm falsity_off) : Prop := nil ⊢M phi.
  Definition class_provable (phi : minimalForm falsity_off) : Prop := nil ⊢C phi.

  Lemma minProvabilityUndec : undecidable int_provable.
  Proof.
    apply (undecidability_from_reducibility H10UPC_SAT_undec).
    exact proveReduction.
  Qed.

  Lemma minClassicalProvabilityUndec : undecidable class_provable.
  Proof.
    apply (undecidability_from_reducibility H10UPC_SAT_undec).
    exact classicalProveReduction.
  Qed.

  Lemma minSatisfiabilityUndec : undecidable (fun k : minimalForm falsity_on => satis k).
  Proof.
    apply (undecidability_from_reducibility H10UPC_SAT_compl_undec).
    apply satisReduction.
  Qed.

  Lemma minKripkeSatisfiabilityUndec : undecidable (fun k : minimalForm falsity_on => ksatis k).
  Proof.
    apply (undecidability_from_reducibility H10UPC_SAT_compl_undec).
    apply kripkeSatisReduction.
  Qed.

End general.


Section finite.
  Import H10UPC_to_FSAT.
  Import Semantics.FiniteTarski.Fragment.
  Import Semantics.Tarski.FragmentFacts.
  (* Reduction into fragment syntax. Step 1: define FSAT for fragment syntax *)
  Definition FSAT_frag (phi : minimalForm falsity_on) :=
  exists D (I : interp D) rho, listable D /\ decidable (fun v => i_atom (P:=tt) v) /\ @sat _ _ D I _ rho phi.

  (* Also define FVAL for fragment syntax *)
  Definition FVAL_frag (phi : minimalForm falsity_on) :=
  forall D (I : interp D) rho, listable D /\ decidable (fun v => i_atom (P:=tt) v) -> @sat _ _ D I _ rho phi.

  (* Also define FVAL for negation-free fragment *)
  Definition FVAL_frag_no_negation (phi : minimalForm falsity_off) :=
  forall D (I : interp D) rho, listable D /\ decidable (fun v => i_atom (P:=tt) v) -> @sat _ _ D I _ rho phi.

  Lemma minFiniteSatisfiabilityUndec : undecidable FSAT_frag.
  Proof.
    apply (undecidability_from_reducibility H10UPC_SAT_undec).
    eapply reduces_transitive.
    * eexists. apply fsat_reduction.
    * eexists. apply frag_reduction_fsat.
  Qed.

  Lemma minFiniteValidityUndec : undecidable FVAL_frag.
  Proof.
    apply (undecidability_from_reducibility H10UPC_SAT_compl_undec).
    eapply reduces_transitive.
    * eexists. apply fval_reduction.
    * eexists. apply frag_reduction_fval.
  Qed.

  (* This is a conjecture *)
  Lemma minFiniteValidityConjecture : undecidable FVAL_frag_no_negation.
  Abort.

End finite.
(*
Print Assumptions minFiniteValidityUndec.
Print Assumptions minFiniteSatisfiabilityUndec.
Print Assumptions minProvabilityUndec.
Print Assumptions minSatisfiabilityUndec.
Print Assumptions minValidityUndec.
Print Assumptions minKripkeSatisfiabilityUndec.
Print Assumptions minKripkeValidityUndec. *)

(* Closed under the global context *)
