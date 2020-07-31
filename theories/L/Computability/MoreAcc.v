From From Undecidability.L Require Import Computability.Rice Functions.Size.

Lemma totality : ~ lacc(fun s => forall t, pi s t).
Proof.
  intros [u [proc_u Hu]].

  pose (w := (.\"x"; !!u (!!(int lam) (!!(int app) (!!(int app) (!!(int app) (!!(int app)
                              !!(enc (int eva))
                              !!(int app (enc (int size')) (enc (var 0))))
                              (!!(int (enc (X:=term))) (!!(int app) "x" (!!(int (enc (X:=term))) "x"))))
                              !!(enc (lam Omega Lia)))
                              !!(enc I)))) : term).
  
  eapply self_div. cbn in w. assert (pw:proc w). subst w. Lproc.
  exists w. split. auto. 

  intros s.

  pose (v_s := (.\"y"; !!(int eva) (!!(int size') "y") !!(enc (s (enc s))) !!(lam Omega Lia) !!I) : term ). 

  assert (~ pi s s <-> pi u v_s). {
    cbn in v_s.
    rewrite <- Hu.
    unfold pi.
    assert (forall t, v_s (enc t) == ((enc (eva (size' t) (s (enc s)))) (λ Omega Lia)) I) by (subst v_s; LsimplRed).
    split; intros A.
    - intros t. rewrite int_is_enc,H.
      eapply eval_converges. 
      Lsimpl'. destruct eva eqn:E.
      +exfalso. apply A. apply eva_seval in E. eapply eval_converges. eapply seval_eval;eauto.
      +Lsimpl.
    - intros [v [Hv lv]]. eapply equiv_lambda in Hv;[|auto].
      assert (B : eval (s (enc s)) v) by eauto. 
      destruct (eval_seval B) as [n C]. eapply seval_eva in C.
      destruct (size'_surj n) as [t Ht]. subst n. 
      specialize (A t); specialize (H t). eapply lamOmega Lia.
      destruct A as [v' [A lv']]. exists v';split;[|auto].
      rewrite <- A, H. clear A H.
      transitivity Omega Lia. LsimplRed. symmetry. Lrewrite. rewrite C. LsimplRed.
  }

  assert (A : w (enc s) == u (enc v_s)). {
    subst w v_s. LsimplRed.
  }
  unfold pi; now rewrite A.
Grab Existential Variables. auto. 
Qed.

Lemma totality_proc : ~ lacc (fun s => proc s /\ ~ forall t, pi s t).
Proof.
  eapply Rice1.
  - firstorder.
  - intuition. apply H3.  intros. now rewrite H1.
  - exists (lam I). repeat split;try Lproc. intros [_ H]. eapply H. intros. eexists;split;[|eexists;reflexivity]. now Lsimpl.
  - exists (lam Omega Lia). repeat split;try  Lproc. intros H. eapply lamOmega Lia. eauto.
  - split.  Lproc. intros H; eapply lamOmega Lia. eauto.
Grab Existential Variables. repeat econstructor. repeat econstructor.
Qed.

Lemma totality_compl : ~ (lacc (fun s => ~ forall t, pi s t)).
Proof.
  intros H.
  eapply totality_proc.
  eapply lacc_conj.
  - eapply dec_lacc. eapply ldec_proc.
  - eassumption.
Qed.
