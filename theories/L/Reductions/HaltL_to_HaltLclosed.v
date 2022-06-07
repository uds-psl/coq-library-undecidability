
Require Import Undecidability.Synthetic.Definitions.
From Undecidability.L Require Import L Functions.Eval.
Import L_Notations.

(* Halting problem for call-by-value lambda-calculus *)
Definition HaltLclosed (s : {s : term | closed s}) := exists t, eval (proj1_sig s) t.

Lemma reduction : HaltL ⪯ HaltLclosed.
Proof.
  unshelve eexists.
  - intros s. exists (Eval (enc s)). unfold Eval. Lproc. 
  - cbn. intros s. unfold HaltL. split; intros (t & Ht).
    + eapply Seval.converges_eval. edestruct Eval_converges. eapply H.
      eapply eval_iff in Ht. eauto.
    + setoid_rewrite eval_iff. cbn in Ht. eapply Seval.converges_eval.
      eapply Eval_converges. eapply Seval.eval_converges. eauto.
Qed.
