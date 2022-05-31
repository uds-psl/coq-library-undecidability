Require Import List.
Import ListNotations.

Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.Facts.
Import PCPListNotation.

Require Import Undecidability.Shared.ListAutomation.
Require Import Undecidability.Synthetic.Definitions.

Set Default Goal Selector "!".

Section derivable_iff_PCPX.

  Variable X : Type.

  Implicit Type P : stack X.

  Lemma derivable_PCPX P u v : derivable P u v -> exists A, A <<= P /\ A <> nil /\ tau1 A = u /\ tau2 A = v.
  Proof.
    induction 1 as [ x y | x y ? ? ? ? (A & ? & ? & ? & ?)].
    - exists [(x,y)]; repeat split; cbn; simpl_list; auto; discriminate.
    - exists ((x,y) :: A); repeat split; simpl; auto; try discriminate; congruence.
  Qed.

  Lemma PCPX_derivable P u v : (exists A, A <<= P /\ A <> nil /\ tau1 A = u /\ tau2 A = v) -> derivable P u v.
  Proof.
    intros (A & H1 & H2 & <- & <-). 
    revert H1; pattern A; revert A H2. 
    eapply list_ind_ne; cbn; intros (x,y) H.
    - simpl_list; constructor 1; auto.
    - constructor 2; eauto.
  Qed.

  Theorem PCPX_iff_dPCP P : PCPX P <-> dPCP P.
  Proof.
    split.
    - intros (A & H1 & H2 & H3); exists (tau1 A).
      rewrite H3 at 2; apply PCPX_derivable.
      exists A; auto.
    - intros (u & Hu).
      apply derivable_PCPX in Hu.
      destruct Hu as (A & H1 & H2 & H3 & H4).
      exists A; subst; auto.
  Qed.

End derivable_iff_PCPX.

Lemma reductionLR (X : Type) : @PCPX X ⪯ @dPCP X.
Proof. exists id; intro; now rewrite PCPX_iff_dPCP. Qed.

Lemma reductionRL (X : Type) : @dPCP X ⪯ @PCPX X.
Proof. exists id; intro; now rewrite PCPX_iff_dPCP. Qed.
