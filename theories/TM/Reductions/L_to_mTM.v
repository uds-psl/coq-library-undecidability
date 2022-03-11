Require Import Undecidability.TM.TM.
Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.
From Undecidability.L Require Import L Seval LM_heap_def LM_heap_correct.
Require Import Undecidability.TM.L.HeapInterpreter.M_LHeapInterpreter.
Require Undecidability.L.Reductions.HaltL_to_HaltLclosed.
Import HaltL_to_HaltLclosed (HaltLclosed).

(* * L to TM *)

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
  eapply reduces_transitive. 1:exact HaltL_to_HaltLclosed.reduction.
  eapply reduces_transitive. 1:exact LM_halting_LM_halting.
  eexists (fun x => (existT2 _ _ _ _ _)). intro.
  setoid_rewrite <- halts_eva_LM_lin.
  rewrite HaltingProblem. unfold HaltTM. cbn. reflexivity.
Qed.
