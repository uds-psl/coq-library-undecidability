From Undecidability.L.Computability Require Export Fixpoints Decidability Seval.
From Undecidability.L.Functions Require Export Proc Encoding.
Import ARS.ARSNotations L_Notations.
(** * Scott's Theorem *)

Theorem Scott (M : term -> Prop) : M <=1 closed ->
  (forall s t, M s -> closed t -> t == s -> M t) ->
  (exists t1, closed t1 /\ M t1) -> (exists t2, closed t2 /\ ~ M t2) ->
  ~ ldec M.                                                                 
Proof.
  intros M_cl M_equiv [s1 [cls_s1 Ms1]] [s2 [cls_s2 nMs2]] [u [[cls_u lam_u] Hu]].
  pose (x := lam(u #0 (lam s2) (lam s1) I)).
  destruct (SecondFixedPoint (s := x)) as [t [cls_t H]]. subst x. Lproc.
  eapply eqTrans with (s := u (enc t) (lam s2) (lam s1) I) in H.
  destruct (Hu t) as [[]  [R C]].
  - eapply nMs2, M_equiv; eauto.
    rewrite <- H,R. symmetry. Lrewrite. LsimplRed.
  - eapply C, M_equiv; eauto.
    rewrite <- H,R. Lrewrite. LsimplRed.
  -symmetry. etransitivity. apply eqStep. apply step_Lproc;Lproc. simpl. now rewrite cls_u,cls_s1,cls_s2.
Qed.

(** * Applications of Scott's Theorem *)

Goal ~ ldec (fun x => closed x /\ converges x).
Proof.
  eapply Scott.
  - tauto.
  - intros s t [cls_s [x [Hx lx]]] cls_t t_e_s; split.
    + eassumption.
    + exists x;split;[|Lproc]. now rewrite t_e_s.
  - exists I. repeat split. exists I;split.  reflexivity. Lproc. 
  - exists Omega. repeat split. intros [_ [x [Hx lx]]]. inv lx. eapply Omega_diverges. exact Hx.
Qed.

Lemma I_neq_Omega : ~ I == Omega.
Proof.
  intros H. eapply Omega_diverges. rewrite <- H. unfold I. cbv; reflexivity.
Qed.

Lemma C27 : forall t, closed t -> ~ ldec (fun x => closed x /\ x == t).
Proof. 
  intros t cls_t H. cut (ldec (fun x : term => closed x /\ x == t)).
  eapply Scott.
  - tauto.
  - intros s t0 [cls_s H0] cls_t0 H1. split. assumption. rewrite H1. assumption.
  - exists t. repeat split. assumption. assumption. reflexivity.
  - destruct H. destruct H. destruct (H0 I) as [[] [? ?]].
    +destruct H2 as [? ?]. exists Omega. split. intros k r. simpl. reflexivity. intros [_ C]. eapply I_neq_Omega. rewrite C. auto.
    +exists I. split. Lproc. auto.
  - eassumption.
Qed.

Lemma C27_proc : forall t, proc t -> ~ ldec (fun x => x == t).
Proof. 
  intros t proc_t H. eapply C27; eauto using ldec_conj, ldec_closed; Lproc.
Qed.
    
Lemma Eq_ldec : ~ ldec (fun x => exists (s t : term), x = enc (s t) /\ s == t).
Proof.
  intros [u [[cls_u lam_u] Hu]].
  pose (t := I).
  eapply (C27_proc (t := t)). Lproc.
  pose (v := (lam(u ((ext (term_enc)) ((ext app) #0 (ext t)))))). 
  exists v. split. subst v;Lproc.
  intros s. destruct (Hu (ext (s t))) as [b [eq C]].
  exists b. split.
  +subst v. Lsimpl. eassumption. 
  +destruct b.
   *destruct C as [? [? [eq' ?]]]. apply inj_enc in eq'. congruence.
   *intros eq'. apply C. now repeat eexists.
Qed.
