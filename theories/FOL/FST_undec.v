From Undecidability.Synthetic
     Require Import Definitions Undecidability.

From Undecidability.FOL
     Require Import Sets.FST
                    Semantics.Tarski.FullFacts
                    Semantics.Tarski.FullSoundness
                    Deduction.FullNDFacts
                    Sets.Models.FST_model.


From Undecidability.FOL.Reductions
     Require Import PCPb_to_FST PCPb_to_FSTD ZF_to_FST.

From Undecidability.PCP
     Require Import PCP PCP_undec Reductions.PCPb_iff_dPCPb.

Theorem undecidable_entailment_FSTeq :
  undecidable entailment_FSTeq.
Proof.
  apply (undecidability_from_reducibility PCPb_undec).
  exists solvable'. intros B. split.
  - intros HP % (PCP_FSTD (p:=intu)).
    apply soundness in HP. intros I M rho H. apply HP, H.
  - apply PCP_FST.
Qed.

Theorem undecidable_deduction_FST :
  undecidable deduction_FST.
Proof.
  apply (undecidability_from_reducibility PCPb_undec).
  exists solvable'. intros B. split.
  - intros HP % (PCP_FSTD (p:=intu)). apply HP.
  - intros HP % soundness. apply PCP_FST.
    intros I M rho H. apply HP. apply H.
Qed.

Theorem undecidable_entailment_FST :
  undecidable entailment_FST.
Proof.
  apply (undecidability_from_reducibility PCPb_undec).
  exists solvable. intros B. apply PCPb_to_FST.PCP_FST.
  apply FST_model.
Qed.

Theorem undecidable_entailment_FSTI :
  undecidable entailment_FSTI.
Proof.
  apply (undecidability_from_reducibility PCPb_undec).
  exists solvable. intros B. rewrite PCPb_iff_dPCPb. split; intros H.
  - destruct H as [s H]. intros M HM rho H1 H2. eapply PCP_FST1; eauto.
    intros sigma psi Hp. apply H2. now constructor.
  - destruct FSTI_model as (D & I & H1 & H2 & H3).
    specialize (H D I (fun _ => @i_func _ _ _ _ eset Vector.nil) H1 H3).
    apply PCP_FST2 in H as [s Hs]; trivial. now exists s.
    intros sigma psi Hp. apply H3. now constructor.
Qed.

Theorem undecidable_deduction_FSTI :
  undecidable deduction_FSTI.
Proof.
  apply (undecidability_from_reducibility PCPb_undec).
  exists solvable. intros B. split; intros H.
  - exists FSTeq. split; try apply FSTeq_base. now apply PCPb_to_FSTD.PCP_FSTD.
  - destruct FSTI_model as (D & I & H1 & H2 & H3).
    rewrite PCPb_iff_dPCPb. unshelve eapply PCP_FST2; eauto.
    + exact (fun _ => @i_func _ _ _ _ eset Vector.nil).
    + intros sigma psi Hp. apply H3. now constructor.
    + apply (tsoundness H). intros psi [theta [<-|[<-|[<-|[<-|Hp]]]]|theta].
      1-4: cbn; setoid_rewrite H1; congruence.
      * apply H3. now constructor.
      * apply H3. constructor 2.
Qed.
  
  
