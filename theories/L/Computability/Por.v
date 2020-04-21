From Undecidability.L.Functions Require Export Eval.
From Undecidability.L.Tactics Require Import Lbeta_nonrefl.
(** * Definition of parallel or *)

Section hoas. Import HOAS_Notations.
Definition Por :term := Eval simpl in (λ s t , (λ n0,  !!(ext doesHaltIn) s n0 ) (!!mu (λ n ,!!(ext orb) (!!(ext doesHaltIn) s n) (!!(ext doesHaltIn) t n)))) .
End hoas.

Lemma Por_proc : proc Por.
Proof.
  unfold Por; Lproc.
Qed.

Hint Resolve Por_proc : LProc.

Import L_Notations.

Lemma Por_correct_1a (s t:term) : converges s -> converges (Por (ext s) (ext t)).
Proof.
  intros H. apply eval_converges in H as [t' H]. apply eval_seval in H as [n H].
  apply seval_eva in H. edestruct mu_complete with (n:=n) (P:=(lam ((ext orb) ((ext doesHaltIn) (ext s) 0) ((ext doesHaltIn) (ext t) 0)))) as [v R].
  -Lproc.
  -eexists;now Lsimpl.
  -Lsimpl. edestruct (doesHaltIn s n) eqn:eq;unfold doesHaltIn in eq;rewrite H in eq. 2:congruence. Lsimpl.
  -eapply Seval.eval_converges. unfold Por. Lsimpl. rewrite R. Lsimpl.
Qed.

Lemma Por_correct_1b (s t:term) : converges t -> converges (Por (ext s) (ext t)).
Proof.
  intros H. apply eval_converges in H as [t' H]. apply eval_seval in H as [n H].
  apply seval_eva in H. edestruct mu_complete with (n:=n) (P:=lam ( (ext orb) ((ext doesHaltIn) (ext s) 0) ((ext doesHaltIn) (ext t) 0))) as [v R].
  -Lproc.
  -eexists;now Lsimpl.
  -Lsimpl.  edestruct (doesHaltIn t n) eqn:eq;unfold doesHaltIn in eq;rewrite H in eq. 2:congruence. edestruct doesHaltIn;Lsimpl.
  -eapply Seval.eval_converges. unfold Por. Lsimpl. rewrite R. Lsimpl.
Qed.

Lemma Por_correct_1 s t : converges s \/ converges t -> converges (Por (ext s) (ext t)).
Proof.
  intros [convs | convt]; eauto using Por_correct_1a, Por_correct_1b.
Qed.

Lemma Por_correct_2 (s t:term) : converges (Por (ext s) (ext t)) -> 
  exists (b:bool), Por (ext s) (ext t) == ext b.
Proof.
  intros [v [R lv]]. unfold Por in R. LsimplHypo.
  evar (s':term). assert (C:converges s'). eexists. split. exact R. Lproc. subst s'.
  apply app_converges in C as [_ [v' [C lv']]].
  assert (C':=C).
  apply mu_sound in C as [n [eq [R' H]]];try Lproc.
  -exists (doesHaltIn s n). subst. unfold Por. Lsimpl. rewrite C'. Lsimpl. 
  -eexists. now Lsimpl.
Qed.


Lemma Por_correct' (s t:term) (b:bool) : Por (ext s) (ext t) == ext b -> if b then converges s else converges t.
Proof.
  intros H. unfold Por in H. LsimplHypo. evar (s':term). assert (C:converges s'). eexists. split. exact H. Lproc. subst s'.
  apply app_converges in C as [_ [v [C lv]]]. 
  assert (C':= C). apply mu_sound in C'; try Lproc.
  -destruct C' as [n [eq [R C']]]. subst v. rewrite C in H. LsimplHypo. Lrewrite in R. Lrewrite in H. apply enc_extinj in H. rewrite H in R. destruct b.
   +unfold doesHaltIn in H. destruct (eva n s) eqn: eq. apply eva_seval in eq. apply seval_eval in eq. eauto. congruence. 
   +simpl in R. apply enc_extinj in R. unfold doesHaltIn in R. destruct (eva n t) eqn: eq. apply eva_seval in eq. apply seval_eval in eq. eauto. congruence.
  -intros. eexists. now Lsimpl.
Qed.
