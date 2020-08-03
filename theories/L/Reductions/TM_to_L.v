From Undecidability Require Import TM.TMEncoding TM.TMinL TM.Util.TM_facts.
From Undecidability.L Require Import Computability.MuRec.
Require Import Undecidability.FOL.Reductions.

Lemma TM_eval_halts Σ n (M : TM Σ n) q t q' t' :
  TM.eval M q t q' t' -> halt M q' = true.
Proof.
  induction 1; eauto.
Qed.

(** ** Reducing halting problem for TMs to halting problem for L *)
Theorem HaltMTM_to_HaltL :
  HaltMTM ⪯ HaltL.
Proof.
  eexists (fun '(existT2 (Sigma, n) M tp) =>
             (L.app mu (@ext _ _ _ (term_test (mk_mconfig (start M) tp))))).
  intros [ [Sigma n] M tp ]. cbn.
  unfold HaltL. setoid_rewrite eval_iff.
  split.
  - intros H.
    epose proof (Halt_red (mk_mconfig (start M) tp)) as [[v [H1 H2]] _].
    + destruct H as (? & ? & ?). eexists (mk_mconfig _ _).
      rewrite <- TM_eval_iff. split. 2:eassumption.
      eapply TM_eval_halts. eassumption.
    + exists v. split; eauto.
      eapply equiv_lambda. eassumption. eassumption.
  - intros [t [H1 H2]].
    epose proof (Halt_red (mk_mconfig (start M) tp)) as [_ [[q' t']]].
    + eexists. eauto.
    + exists q', t'. eapply TM_eval_iff. eapply H.
Qed.
