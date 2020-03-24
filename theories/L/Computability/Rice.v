From Undecidability.L.Computability Require Export Scott Acceptability.
Import Undecidability.L.Prelim.ARS.ARSNotations.

(** * The self halting problem is not L-acceptable *)

Definition self_diverging (s : term) := ~ pi s s.

Definition self_diverging_comb := conj self_diverging proc.

Lemma self_div : ~ lacc self_diverging.
Proof.
  intros H.
  destruct H as [u [[cls_u lam_u] H]].
  unfold self_diverging in H. specialize (H u). intuition. 
Qed.

Lemma self_div_comb : ~ lacc self_diverging_comb.
Proof.
  intros [u [[cls_u lam_u] H]].
  unfold self_diverging_comb in H. unfold conj in H.
  specialize (H u). unfold self_diverging in H.
  destruct H. unfold proc in *. tauto.
Qed.

(** * Rice's Theorem *)

Lemma Rice1 (M : term -> Prop) : (M <=1 proc) ->
                                 (forall (s t : term), proc t -> M s -> (forall u, pi s u <-> pi t u) -> M t) ->
                                 (exists p, proc p /\ ~ M p) -> (exists p, proc p /\ M p) ->
                                 M (lam Omega) -> ~ lacc M.
Proof with eauto; try now intuition.
  intros M_proc M_cl_equiv [t2 [cls_t2 nMt2]] [t1 [cls_t1 nMt1]] MLO [u [[cls_u lam_u] Hu]].

  eapply (self_div_comb).
  
  destruct (dec_lacc ldec_proc) as [c [[cls_c lam_c] Hc]].
  pose (v  := lam ( u ((ext lam) ((ext app) (enc (lam (t2 #1))) ((ext app) #0 ((ext (enc(X:= term))) #0)))))).
  pose (v' := acc_conj c v).
  assert (proc v). subst v;unfold acc_conj;Lproc.
  assert (proc v'). subst v';unfold acc_conj;Lproc. 
  exists v'; split. Lproc.
  intros s.
  pose (vs := lam ((lam (t2 #1)) (s (enc s)))).

  symmetry.
  transitivity (pi v s /\ proc s). 
  {
    unfold v'. rewrite acc_conj_correct;try Lproc. rewrite <- Hc. tauto.
  }

  unfold self_diverging_comb, conj.

  transitivity (pi u vs /\ proc s).
  { 
    split; intros [R cls_s];(split;[|Lproc]).
    -revert R. eapply converges_proper. symmetry. subst v. Lsimpl.
    -revert R. eapply converges_proper. subst v. Lsimpl.
  }

  transitivity (M vs /\ proc s). 
  split; intros [? ?]; intuition; try (now rewrite Hu). (* apply Hu;tauto.  *)
  
  {
    split.
    - intros [Mvs cls_s]; intuition.
      intros [w [Hw lw]]. 
      assert (forall t, pi vs t <-> pi t2 t). {
        intros t. eapply converges_proper.
        assert (closed w). eapply (equiv_lambda lw) in Hw. eapply closed_star. exact Hw. Lproc. subst vs. Lsimpl. rewrite Hw. Lsimpl. 
      }
      eapply nMt2. eapply M_cl_equiv; eassumption.
    - intros [npi_s_s cls_s]; intuition.
      assert (forall t, pi (lam Omega) t <-> pi vs t). {
        intros t; split; intros H'.
        - exfalso. destruct H' as [w [Hw lw]]. inv lw. eapply Omega_diverges. rewrite <- Hw. symmetry. clear Hw. now redStep.
        - exfalso. eapply npi_s_s.
          assert (A: converges (lam ( t2 (enc t)) (s (enc s)))). revert H'. eapply converges_proper. symmetry. unfold vs. Lsimpl.
          eapply app_converges in A. firstorder.
      }
                                                       subst vs.
      eapply M_cl_equiv; try Lproc;try eassumption.
  }
Qed.

Lemma Rice2 (M : term -> Prop) : (M <=1 proc) ->
                                 (forall (s t : term), proc t -> M s -> (forall u, pi s u <-> pi t u) -> M t) ->
                                 (exists p, proc p /\ ~ M p) -> (exists p, proc p /\ M p) ->
                                 ~ M (lam Omega) -> ~ lacc (complement M).
Proof.
  intros M_cls M_cl_equiv [t2 [cls_t2 nMt2]] [t1 [cls_t1 nMt1]] nMLO decM.
  destruct decM as [u [[cls_u lam_u] Hu]]. unfold complement in Hu.

  eapply (self_div_comb).
  
  destruct (dec_lacc ldec_proc) as [c [[cls_c lam_c] Hc]].
  pose (v  := lam ( u ((ext lam) ((ext app) (enc (lam (t1 #1))) ((ext app) #0 ((ext (enc (X:=term))) #0)))))).
  pose (v' := acc_conj c v).
  exists v'; split. subst v' v. unfold acc_conj. Lproc. 
  intros s.
  pose (vs := lam ((lam (t1 #1)) (s (enc s)))).
  assert (cv:closed v) by (subst v; Lproc).

  symmetry.
  transitivity (pi v s /\ proc s). 
  {
    unfold v'. rewrite acc_conj_correct;try Lproc. intuition ; now apply Hc. }

  unfold self_diverging_comb, conj.

  transitivity (pi u vs /\ proc s).
  {
    split; intros [R cls_s];(split;[|Lproc]).
    -revert R. eapply converges_proper. symmetry. subst v. Lsimpl.
    -revert R. eapply converges_proper. subst v. Lsimpl.
  }

  transitivity (~ M vs /\ proc s).
  {
    split; intros [? ?]; try (rewrite Hu); intuition; firstorder. 
  }
  
  {
    split.
    - intros [Mvs cls_s]; intuition.
      intros [w [Hw lw]]. 
      assert (forall t, pi t1 t <-> pi vs t). {
        intros t. symmetry. assert (closed w). eapply closed_star. eapply equiv_lambda;eauto. Lproc.  eapply converges_proper.
        transitivity (lam ( t1 (enc t)) (s (enc s))). unfold vs. Lsimpl. rewrite Hw. Lsimpl.
      }
      eapply Mvs. eapply M_cl_equiv;try subst vs; try Lproc; try eassumption.
    - intros [npi_s_s cls_s]; intuition.
      assert (forall t, pi (lam Omega) t <-> pi vs t). {
        intros t; split; intros A.
        - exfalso. destruct A as [w [Hw lw]]. inv lw. eapply Omega_diverges. rewrite <- Hw. symmetry. clear Hw. now LsimplRed.
        - exfalso. eapply npi_s_s.
          assert (B: converges (lam ( t1 (enc t)) (s (enc s)))). revert A. eapply converges_proper. symmetry. unfold vs. Lsimpl.
          eapply app_converges in B. firstorder.
      }
      eapply nMLO.
      eapply M_cl_equiv; try (symmetry); eauto. Lproc.
  }
Qed.

(** ** Rice's Theorem, classical *)

Theorem Rice (M : term -> Prop) : (M <=1 proc) ->
                                 (forall (s t : term), proc t -> M s -> (forall u, pi s u <-> pi t u) -> M t) ->
                                  (exists p, proc p /\ ~ M p) -> (exists p, proc p /\ M p) ->
                                  ~ ldec M.
Proof.
  intros. intros A. assert (B : ldec M) by eassumption. destruct A as [u [proc_u Hu]].
  destruct (Hu (lam Omega)) as [[] [eq m]].
  - eapply Rice1; try eassumption. apply dec_lacc. exists u; tauto.
  - eapply Rice2; try eassumption. apply dec_lacc. apply ldec_complement. exists u; tauto.
Qed.

Lemma lamOmega s : ~ pi (lam Omega) s.
Proof.
   intros A. destruct A as [? [H l]]. inv l. eapply Omega_diverges. rewrite <- H. clear H. symmetry. now redSteps.
Qed.

(** * Applications of Rice's Theorem *)

Goal ~ ldec (fun s => proc s /\ forall t, pi s t).
Proof.
  eapply Rice.
  - firstorder.
  - intuition;now apply H1.
  - exists (lam Omega). split. Lproc. intros [_ A]. eapply lamOmega; eauto. 
  - exists (lam I). repeat split;try Lproc. intros t; eexists; split; [|eexists;reflexivity]. now Lsimpl.
Grab Existential Variables. repeat econstructor. 
Qed.

Goal ~ lacc (fun s => proc s /\ exists t, ~ pi s t).
Proof.
  eapply Rice1.
  - firstorder.
  - intros s t cls_t [cls_s [t0 H]] He. split; eauto.
    exists t0. rewrite <- He. eassumption.
  - exists (lam I). split.  Lproc. intros [_ [? H]]. eapply H. eexists;split;[|eexists;reflexivity]. now Lsimpl.
  - exists (lam Omega). repeat split;try Lproc. exists I. eapply lamOmega.
  - split. Lproc. exists I. eapply lamOmega. 
Qed.

(** * Rice's Theorem, classical, on combinators *)

Theorem Rice_classical (M : term -> Prop) : (M <=1 closed) ->
                                 (forall (s t : term), closed t -> M s -> (forall u, pi s u <-> pi t u) -> M t) ->
                                  (exists p, closed p /\ ~ M p) -> (exists p, closed p /\ M p) ->
                                  ~ ldec M.
Proof.
  intros. eapply Scott.
  - firstorder. 
  - intros. eapply H0; try eassumption. intros. unfold pi. now rewrite H5.
  - destruct H2; eauto.
  - destruct H2; eauto.
Qed.
