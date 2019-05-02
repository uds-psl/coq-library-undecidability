From Undecidability.LAM Require Import Prelims.
(** * Abstract Simulation Proof*)
Section absSim.
  Variable term state : Type.
  Variable step : term -> term -> Prop.
  Variable M_tau M_beta: state -> state -> Prop.
  Variable represents: state -> term -> Prop. 

  Definition M s t := M_tau s t \/ M_beta s t.
  
  Hypothesis finish: forall conf s, represents conf s -> terminal M conf -> terminal step s.
  Hypothesis tau_correct: forall conf conf' u, M_tau conf conf' -> represents conf u -> represents conf' u.
  Hypothesis beta_correct: simulatedWith M_beta step represents.
  Hypothesis sn_tau: forall conf u, represents conf u -> SN M_tau conf.
  Hypothesis M_classical : forall conf s, represents conf s -> classical M conf.
  Hypothesis uc : uniform_confluent step.

  Local Hint Unfold evaluates M.
  
(** ** upwards *)
Lemma upSim s conf conf': evaluates M conf conf' -> represents conf s -> exists t, evaluates step s t /\ represents conf' t.
Proof.
  intros [R ter]. induction R in s,ter|-*;intros rep.
  -exists s;split. 2:tauto. split. reflexivity. eapply finish. all:eauto. 
  -destruct H.
   +eapply tau_correct in H as ?. 2:eassumption.
    apply IHR. all:eauto.
   +eapply beta_correct in H as (?&?&R'). 2:eassumption.
    edestruct IHR as (?&(?&?)&?). all:eauto 10 using star.
Qed.
(** ** downwards *)
  Lemma downSim s t conf: evaluates step s t -> represents conf s -> exists conf', evaluates M conf conf' /\ represents conf' t.
Proof.
  intros [R ter] rep. eapply star_pow in R as (n&R). induction n as [n IH] in conf,rep,s,R|-* using complete_induction.
  specialize (sn_tau rep). induction sn_tau as [conf ? IHSN]. 
  edestruct (M_classical rep) as [ter'|[conf' [R'|R'] ]]. 
  -eapply finish in ter' as ter''. 2:eauto.
   enough (s=t) as -> by eauto using star. 
   destruct n;inv R.
   +eexists;repeat split;eauto.
   +edestruct ter'';intuition eauto.
  -edestruct IHSN as (?&[? ?]&?). all:eauto 10 using star.
  -edestruct beta_correct as (?&?&?). 1,2:now eauto. 
   edestruct uc_terminal as (?&?&?). 1-4:now eauto.
   subst. edestruct IH as (conf''&[]&?). 1,2,3:now eauto;omega.
   eauto 10 using star. 
Qed.

End absSim.

