(*
  Reduction from:
    Weak call-by-name leftmost outermost normalization of closed terms (wCBNclosed)
  to:
    Weak call-by-name leftmost outermost normalization (wCBN)
*)

From Undecidability.LambdaCalculus Require Import wCBN Util.term_facts Util.wCBN_facts.
Require Undecidability.L.Util.L_facts.
Require Import Undecidability.Synthetic.Definitions.

Set Default Goal Selector "!".

Theorem reduction : wCBNclosed ⪯ wCBN.
Proof.
  exists (@proj1_sig L.term _).
  intros [s Hs]. cbn. split.
  - intros [t Ht]. exists (L.lam t). split; [assumption|].
    intros u H%stepE. destruct H.
  - intros [t [Hst Ht]].
    assert (L.closed t) as H't.
    { apply (@steps_bound 0) in Hst; [now apply L_facts.closed_dcl|].
      apply L_facts.closed_dcl. apply closed_I. intros k.
      now rewrite L_subst_wCBN_subst. }
    apply (closed_halt_iff H't) in Ht.
    destruct Ht as [t' ?]. subst t.
    exists t'. assumption.
Qed.
