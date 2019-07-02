From Undecidability.L Require Export LTerm Por Decidability Lbeta_nonrefl.

(** * Definition of L-acceptability *)

Definition pi (s t:term) := converges (s (ext t)).

Definition lacc (P : term -> Prop) := 
  exists u, proc u /\ forall t, P t <-> pi u t.

(** * Properties of acceptance *)

Goal forall s1 s2 t, s1 == s2 -> (pi s1 t <-> pi s2 t).
Proof. 
  intros s1 s2 t H; intuition; unfold pi; [now rewrite <- H | now rewrite H].
Qed.

(** * L-acceptable predicates are closed under conjunction and disjunction *)

Definition acc_conj (p q : term) := lam ((lam (q #1)) (p #0) ).
Hint Unfold acc_conj : cbv.

Lemma acc_conj_correct p q s : closed p -> closed q -> (pi (acc_conj p q) s <-> pi p s /\ pi q s).
Proof.
  intros cls_p cls_q.
  split.
  - intros [x [Hx lx]].
    assert (H : converges (lam( q (enc s)) (p (enc s)))). { exists x;split;auto. symmetry. symmetry in Hx. unfold acc_conj in Hx. rewrite Hx. redStep. LsimplRed. }
    destruct (app_converges H) as [_ [y [Hy ly]]]. split.
    + eexists; split;eassumption.
    + exists x;split;auto. rewrite <- Hx. symmetry. clear Hx. unfold acc_conj. LsimplRed. rewrite Hy.  LsimplRed. 
  - intros [[x [Hx ?]] [y [Hy ?]]]. exists y. split. unfold acc_conj. LsimplRed. rewrite Hx. LsimplRed. tauto. Lproc.
Qed.

Lemma lacc_conj P Q : lacc P -> lacc Q -> lacc (conj P Q).
Proof.
  intros [u1 [[? ?] Hu1]] [u2 [[? ?] Hu2]].
  exists (acc_conj u1 u2). split. unfold acc_conj. Lproc.
  intros; rewrite acc_conj_correct; firstorder.
Qed.

Lemma lacc_disj M N : lacc M -> lacc N -> lacc (disj M N).
Proof.
  intros [u [[lam_u cls_u] Hu]] [v [[lam_v cls_v] Hv]].
  unfold lacc, disj.
  exists (lam (Por ((ext app) (enc u) ((ext (term_enc) #0))) (((ext app) (enc v) ((ext (term_enc)) #0))))).
  split. Lproc. intros t.

  rewrite Hu, Hv; unfold pi.
  evar (t':term).
  (* todo: nicer way?*)
  assert (R':(lam(
      (Por ((ext app) (ext u) ((ext (term_enc)) 0)))
      ((ext app) (ext v) ((ext (term_enc)) 0))) (ext t)) >* t'). subst t'. Lsimpl.
  rewrite R'. subst t'.
  split. intros [A|B].
  -destruct (Por_correct_1a (v (enc t)) A) as [s [R ls]]. exists s. split;try Lproc. eassumption.
  -destruct (Por_correct_1b (u (enc t)) B) as [s [R ls]]. exists s. split;try Lproc. eassumption.
  -intros [s [H ls]]. edestruct Por_correct_2 as [].
   { exists s. split;auto.
     rewrite !ext_is_enc.
     unfold Por. 
     rewrite <- R'. Lsimpl. eassumption. }
   apply Por_correct' in H0. destruct x;auto.                       
Qed.

(** * L-ecidable predicates are L-acceptable (and their complement too) *)

Lemma dec_lacc M : ldec M -> lacc M.
Proof.
  intros [u [[cls_u lam_u] dec_u_M]].
  exists (lam (u #0 I (lam Omega) I)); split. Lproc. 
    + intros t. specialize (dec_u_M t).
      split; intros H; destruct dec_u_M; try tauto. 
      * destruct H0 as [u_true ?]. eexists;split;[|eexists;reflexivity]. redSteps. rewrite u_true. destruct x. now Lsimpl. tauto.
      * destruct H0. destruct x. tauto. 
        assert ((lam ((((u #0) I) (lam Omega)) I)) (enc t) == Omega). clear H. LsimplRed. rewrite H0. Lrewrite. now Lsimpl. destruct H as [H [? []]]. subst H. rewrite H2 in H3. 
        destruct (Omega_diverges H3).
Qed.

Lemma dec_acc : forall M, ldec M -> lacc M /\ lacc (complement M).
Proof.
  intros M decM; split.
  - eapply (dec_lacc decM).
  - eapply ldec_complement in decM. eapply (dec_lacc decM).
Qed.
