
Require Import Undecidability.Synthetic.Definitions.
From Undecidability.L Require Import L Functions.Eval Util.L_facts.
Import L_Notations.

(* Halting problem for call-by-value lambda-calculus *)
Definition HaltLclosed (s : {s : term | closed s}) := exists t, eval (proj1_sig s) t.

Lemma reduction : HaltL ⪯ HaltLclosed.
Proof.
  unshelve eexists.
  - intros s. exists (Eval (enc s)). unfold Eval. Lproc. 
  - cbn. intros s. unfold HaltL. split; intros (t & Ht).
    + eapply eval_converges. edestruct Eval_converges. eapply H.
      eapply eval_iff in Ht. eauto.
    + setoid_rewrite eval_iff. eapply eval_converges.
      eapply Eval_converges. eapply Seval.eval_converges. eauto.
Qed.
