(*
  Consider two binary relations
    step1 : X -> X -> Prop
    step2 : Y -> Y -> Prop
  such that
  - step2 is deterministic (step2_det)
  - one step in step1 is simulated by a positive number of steps in step2 (fstep)
  - halting in step2 is simulated by termination in step2 (fstop)
  - step1 admits existential successor decision (step1_intro)

  Then, strong normalization in step1 is transported to (terminates_transport)
  and reflected by (terminates_reflection) strong normalization in step 2.
*)

Require Import Relations Transitive_Closure.

Section Preliminaries.

  (* configuration space and step repation *)
  Context {X : Type} (step : X -> X -> Prop).

  (* halting *)
  Definition stuck s := forall t, ~ step s t.

  (* eventual termination *)
  Definition terminates s := exists t, clos_refl_trans X step s t /\ stuck t.

  Fact terminates_extend {s t} : clos_refl_trans X step s t -> terminates t -> terminates s.
  Proof.
    intros ? [u [??]]. exists u. eauto using clos_refl_trans.
  Qed.

  Lemma clos_trans_clos_refl_trans s t : clos_trans _ step s t -> clos_refl_trans _ step s t.
  Proof.
    intros H. now induction H; eauto using clos_refl_trans.
  Qed.

End Preliminaries.

Section Deterministic_simulation.

  (* configuration spaces *)
  Context {X Y : Type}.

  (* step functions *)
  Context {step1 : X -> X -> Prop} {step2 : Y -> Y -> Prop}.

  (* configuration encoding *)
  Context {sync : X -> Y -> Prop}.

  (* determinism of step2 *)
  Context (step2_det : forall s' t1' t2', step2 s' t1' -> step2 s' t2' -> t1' = t2').
  Arguments step2_det {s' t1' t2'}.

  (* step simulation wrt. encoding *)
  Context (fstep : forall s t s', step1 s t -> sync s s' ->
                     exists t', clos_trans Y step2 s' t' /\ sync t t').
  Arguments fstep {s t s'}.

  (* halting simulation wrt. encoding *)
  Context (fstop : forall s s', stuck step1 s -> sync s s' -> terminates step2 s').
  Arguments fstop {s s'}.

  (* propositional progress/halting decision *)
  Context (step1_intro : forall s, (exists t, step1 s t) \/ stuck step1 s).

  (* transport of reachability by structural induction on transitive closure *)
  Lemma clos_refl_trans_transport {s s' t} :
    sync s s' -> clos_refl_trans _ step1 s t ->
    exists t', sync t t' /\ clos_refl_trans _ step2 s' t'.
  Proof using fstep.
    intros Hss' Hst. apply clos_rt_rt1n in Hst.
    revert s' Hss'. induction Hst as [|??? Hxy Hyz IH].
    - intros s' ?. exists s'. now split; [|apply rt_refl].
    - intros s' Hxs'. destruct (fstep Hxy Hxs') as [y' [Hs'y' Hyy']].
      destruct (IH _ Hyy') as [t' [? Hy't']].
      exists t'. split; [|eapply rt_trans; [apply clos_trans_clos_refl_trans|]]; eassumption.
  Qed.

  (* transport of termination by transport of reachability *)
  Lemma terminates_transport {s s'} :
    sync s s' -> terminates step1 s -> terminates step2 s'.
  Proof using fstop fstep.
    intros Hss' [t [Hst Ht]].
    destruct (clos_refl_trans_transport Hss' Hst) as [t' [Htt' Hs't']].
    apply (terminates_extend _ Hs't').
    eapply fstop; eassumption.
  Qed.

  (* terminating configurations are accessible
     note that (Acc R^-1 s) means s is strongly normalizing for R in a constructive setting *)
  Lemma terminating_Acc {s} : terminates step2 s -> Acc (fun y x => step2 x y) s.
  Proof using step2_det.
    intros [t [Hst%clos_rt_rt1n Ht]].
    induction Hst as [|??? Hxy Hyz IH]; constructor.
    - now intros y ?%Ht.
    - intros y' Hxy'. rewrite <- (step2_det Hxy Hxy'). now apply IH.
  Qed.

  (* reflection of termination by well-founded induction on transitive closure using
     Lemma Acc_clos_trans A R x : Acc R x -> Acc (clos_trans A R) x
     from the Coq standard library *)
  Lemma terminates_reflection {s s'} : sync s s' -> terminates step2 s' -> terminates step1 s.
  Proof using step2_det step1_intro fstep.
    intros Hss' Hs'%terminating_Acc%(Acc_clos_trans Y).
    revert s Hss'. induction Hs' as [s' _ IH].
    intros s. destruct (step1_intro s) as [[t Hst] | Hs].
    - intros [t' [Hs't' Htt']]%(fstep Hst).
      apply (terminates_extend _ (t := t)); [now apply rt_step|].
      eapply (IH t'); [|now apply Htt'].
      clear Htt' IH. induction Hs't'; eauto using clos_trans.
    - intros _. exists s. eauto using clos_refl_trans.
  Qed.

End Deterministic_simulation.
