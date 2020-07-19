(** * Post Correspondence Problem *)

From Undecidability Require Export Reductions PCP.PCP.
From Undecidability.Shared Require Export ListAutomation.

Lemma stack_discrete :
  discrete (stack bool).
Proof. Locate discrete.
  eapply discrete_iff; econstructor. intros ? ?. hnf. repeat decide equality.
Qed.

Lemma stack_enum :
  enumerable__T (stack bool).
Proof.
  unfold stack, card. eauto.
Qed.

Local Definition BSRS := list (card bool).
Local Notation "x / y" := (x, y).
(** ** Enumerability *)

Fixpoint L_PCP n : list (BSRS * (string bool * string bool)) :=
  match n with
  | 0 => []
  | S n => L_PCP n
              ++ [ (C, (x, y)) | (C, x, y) ∈ (L_T BSRS n × L_T (string bool) n × L_T (string bool) n), (x/y) el C ]
              ++ [ (C, (x ++ u, y ++ v)) | ( (C, (u,v)), x, y) ∈ (L_PCP n × L_T (string bool) n × L_T (string bool) n), (x,y) el C ]
  end.

Lemma enum_PCP' :
  list_enumerator L_PCP (fun '(C, (u, v)) => @derivable bool C u v).
Proof.
  intros ( C & u & v ). split.
  + induction 1.
    * destruct (el_T C) as [m1], (el_T x) as [m2], (el_T y) as [m3].
      exists (1 + m1 + m2 + m3). cbn. in_app 2.
      in_collect (C, x, y); eapply cum_ge'; eauto; lia.
    * destruct IHderivable as [m1], (el_T x) as [m2], (el_T y) as [m3]. 
      exists (1 + m1 + m2 + m3). cbn. in_app 3.
      in_collect ( (C, (u, v), x, y)); eapply cum_ge'; eauto; try lia.
  + intros [m]. revert C u v H. induction m; intros.
    * inv H.
    * cbn in H. inv_collect; inv H; eauto using der_sing, der_cons.
Qed.

Lemma enumerable_derivable : enumerable (fun '(C, (u, v)) => @derivable bool C u v).
Proof.
  eapply list_enumerable_enumerable. eexists. eapply enum_PCP'.
Qed.

Lemma enumerable_PCP : enumerable dPCPb.
Proof.
  pose proof enumerable_derivable. 
  assert (enumerable (X := (stack bool * (string bool * string bool))) (fun '(C, (s, t)) => s = t)). {
    eapply dec_count_enum.
    - eapply decidable_iff. econstructor. intros (? & ? & ?). exact _.
    - eapply enum_enumT. econstructor. exact _.
  }
  unshelve epose proof (enumerable_conj _ _ _ _ H H0).
  - eapply discrete_iff. econstructor. exact _.
  - eapply projection in H1 as [f]. exists f.
    unfold enumerator in *.
    intros x. rewrite <- H1. intuition.
    + destruct H2 as [u]. exists (u,u). eauto.
    + destruct H2 as [[u v] [? ->]]. exists v. eauto.
Qed.
