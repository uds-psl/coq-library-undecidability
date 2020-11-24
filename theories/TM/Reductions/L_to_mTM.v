Require Import Undecidability.TM.TM.
Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.
From Undecidability.L Require Import L Seval LM_heap_def LM_heap_correct.
Require Import Undecidability.TM.L.HeapInterpreter.M_LHeapInterpreter.

(* * L to TM *)

-Definition HaltLclosed (s : {s : term | closed s}) := exists t, eval (proj1_sig s) t. (* Halting problem for call-by-value lambda-calculus *)

Definition eva_LM_lin sigma := exists tau, evaluates step sigma tau.

Lemma red_haltL_to_LM_Lin s:
  closed s -> HaltL s <-> eva_LM_lin (init s).
Proof.
  intros ?.
  unfold HaltL, eva_LM_lin.
  split.
  -intros (t&R).
   eapply eval_iff in R.
   eapply completeness in R as (g&Hp&_&R). 2:easy.
   eexists. split. eassumption.
   intros ? H'. inv H'.
  -intros (?&E). 
   eapply soundness in E as (?&?&?&?&?&?). all:eauto.
   eexists. eapply eval_iff. eauto.
Qed.

Lemma LM_halting_LM_halting : HaltLclosed ⪯ eva_LM_lin.
Proof.
  eexists (fun '(exist s _ ) => _). intros [s].
  unfold HaltLclosed. cbn.
  setoid_rewrite <- eval_iff.
  now eapply red_haltL_to_LM_Lin.
Qed.

Require Import Undecidability.L.Functions.Encoding Undecidability.L.Functions.Eval Undecidability.L.Tactics.LTactics.
Import L_Notations.

Lemma HaltL_HaltLclosed :
  HaltL ⪯ HaltLclosed.
Proof.
  unshelve eexists.
  - intros s. exists (Eval (enc s)). unfold Eval. Lproc. 
  - cbn. intros s. unfold HaltL. split; intros (t & Ht).
    + eapply eval_converges. edestruct Eval_converges. eapply H.
      eapply eval_iff in Ht. eauto.
    + setoid_rewrite eval_iff. eapply eval_converges. eapply Eval_converges. eapply Seval.eval_converges. eauto.
Qed.


Lemma star_def_equiv X R (x y : X):
  star R x y <-> Relations.star R x y.
Proof.
  split;induction 1.  all:eauto using star,Relations.star.
Qed.
  

Lemma halts_eva_LM_lin sigma:
  halts sigma <-> eva_LM_lin sigma.
Proof.
  unfold halts,eva_LM_lin,evaluates,steps,halt_state,terminal.
  setoid_rewrite star_def_equiv. intuition.
Qed.

Lemma HaltL_HaltTM :
  HaltL ⪯ HaltTM 11.
Proof.
  eapply reduces_transitive. 1:exact HaltL_HaltLclosed.
  eapply reduces_transitive. 1:exact LM_halting_LM_halting.
  eexists (fun x => (existT2 _ _ _ _ _)). intro.
  setoid_rewrite <- halts_eva_LM_lin.
  rewrite HaltingProblem. unfold HaltTM. cbn. reflexivity.
Qed.
