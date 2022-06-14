
Require Import Undecidability.Synthetic.Definitions.
From Undecidability.L Require Import L Computability.Seval Functions.Eval.
From Undecidability.L Require Import Datatypes.LTerm Tactics.LTactics Computability.MuRec.
Import L_Notations.

(* Halting problem for closed terms in the call-by-value lambda-calculus *)
Definition HaltLclosed (s : {s : term | closed s}) := exists t, eval (proj1_sig s) t.

Lemma reduction : HaltL ⪯ HaltLclosed.
Proof.
  unshelve eexists.
  - intros s. exists (Eval (enc s)). unfold Eval. Lproc. 
  - cbn. intros s. unfold HaltL. split; intros (t & Ht).
    + eapply converges_eval. edestruct Eval_converges. eapply H.
      eapply eval_iff in Ht. eauto.
    + setoid_rewrite eval_iff. cbn in Ht. eapply converges_eval.
      eapply Eval_converges. eapply eval_converges. eauto.
Qed.
