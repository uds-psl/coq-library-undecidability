From Undecidability.SeparationLogic Require Import min_seplogic seplogic.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.

Fixpoint embed (P : msp_form) : sp_form :=
  match P with
  | mpointer E E1 E2 => sand (pointer E E1 E2) (imp bot bot)
  | mbot => bot
  | mimp P1 P2 => imp (embed P1) (embed P2)
  | mall x P => all x (embed P)
  end.

Lemma embed_sat s h P :
  msp_sat s h P <-> sp_sat s h (embed P).
Proof.
  induction P in s, h |- *; cbn.
  - split.
    + intros (l & H1 & H2). apply in_split in H2 as (h1 & h2 & ->).
      exists [(l, (sp_eval s s1, sp_eval s s2))], (h1 ++ h2). split.
      * unfold equiv, incl. repeat setoid_rewrite in_app_iff. cbn. firstorder.
      * split; trivial. exists l. split; trivial.
    + intros (h1 & h2 & H1 & [l[H2 ->]] & _). exists l. split; trivial. apply H1, in_app_iff. now left.
  - tauto.
  - rewrite IHP1, IHP2. tauto.
  - setoid_rewrite IHP. tauto.
Qed.

Require Import Undecidability.Synthetic.Definitions.

Theorem reduction :
  MSPSAT ⪯ SPSAT.
Proof.
  exists embed. intros P. split; intros (s & h & H); exists s, h; now apply embed_sat.
Qed.
