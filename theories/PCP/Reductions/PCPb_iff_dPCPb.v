Require Import List.
Import ListNotations.

Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.Facts.

Require Import Undecidability.Problems.Reduction.

Require Import Undecidability.Shared.Prelim.

Lemma derivable_BPCP X (P : stack X) u v :
  derivable P u v -> exists A, incl A P /\ A <> nil /\ tau1 A = u /\ tau2 A = v.
Proof.
  induction 1 as [ | ? ? ? ? ? ? (A & ? & ? & ? & ?)].
  - exists [(x, y)]. repeat split; cbn; simpl_list; eauto. congruence.
  - subst. exists ((x, y) :: A). repeat split. apply incl_cons; assumption. congruence.
Qed.
    
Lemma BPCP_derivable X (P : stack X) u v : (exists A, A <<= P /\ A <> nil /\ tau1 A = u /\ tau2 A = v) -> derivable P u v.
Proof.
  intros (A & ? & ? & ? & ?). subst. 
  revert H. pattern A. revert A H0. eapply list_ind_ne; cbn; intros; destruct x as (x,y).
  - simpl_list. eauto using der_sing, der_cons.
  - eauto using der_sing, der_cons.
Qed.

Lemma PCPb_iff_dPCPb P : PCPb P <-> dPCPb P.
Proof.
  split.
  - intros (? & ? & ? & ?). econstructor. eapply BPCP_derivable. eauto.
  - intros []. edestruct (derivable_BPCP H) as (? & ? & ? & ? & ?). subst. exists x0. eauto.
Qed.

Lemma reductionLR : PCPb ⪯ dPCPb.
Proof.
  exists id. exact PCPb_iff_dPCPb.
Qed.

Lemma reductionRL : dPCPb ⪯ PCPb.
Proof.
  exists id. intro x. now rewrite PCPb_iff_dPCPb.
Qed.