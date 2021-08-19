(** ** Reduction from binary ZF to binary FST *)

Require Import Undecidability.FOL.Util.Syntax.
Require Import Undecidability.FOL.Util.Syntax_facts.
Require Import Undecidability.FOL.Util.FullTarski_facts.
Require Import Undecidability.FOL.binFST Undecidability.FOL.binZF.
Require Import Lia.

From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Definition ZF_to_FST phi :=
  ax_pair' ~> ax_union' ~> ax_power' ~> ax_om' ~> phi.

Theorem reduction_entailment phi :
  entailment_binZF phi <-> entailment_binFST (ZF_to_FST phi).
Proof.
  split; intros Hp D I rho HI.
  - unfold ZF_to_FST. intros H1 H2 H3 H4. apply Hp.
    intros psi. intros [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; trivial.
    all: apply HI; unfold binFST; intuition.
  - apply Hp; fold sat. 2-5: apply HI; unfold binZF; intuition auto 7.
    intros psi [<-|[<-|[<-|[<-|[]]]]]. 1-3: apply HI; unfold binZF; intuition.
    intros x y. cbn.
