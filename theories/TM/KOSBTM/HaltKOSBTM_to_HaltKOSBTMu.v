Require Import Undecidability.TM.KOSBTM.KOSBTM.
Require Import Undecidability.Synthetic.Definitions.
From Equations Require Import Equations.

Section fixM.

  Variable M : KOSBTM.

  Definition M' : KOSBTM.
  Proof using M.
    exists (1 + num_states M).
    intros [q o].
    dependent elimination q.
    - destruct (trans M (Fin.F1, o)) as [[[q' w] m] | ].
      dependent elimination q'.
      + exact (Some (Fin.F1, w, m)).
      + exact (Some (Fin.FS (Fin.FS t), w, m)).
      + exact (Some (Fin.FS Fin.F1, None, Nmove)).
    - dependent elimination t.
      + exact None.
      + destruct (trans M (Fin.FS t, o)) as [[[q' w] m] | ].
        dependent elimination q'.
        * exact (Some (Fin.F1, w, m)).
        * exact (Some (Fin.FS (Fin.FS t0), w, m)).
        * exact (Some (Fin.FS Fin.F1, None, Nmove)).
  Defined. (* because definition *)

  Lemma spec1 c : trans M' (Fin.FS Fin.F1, c) = None.
  Proof. reflexivity. Qed.
  
  Lemma spec2 c q' : trans M' (q', c) = None -> q' = Fin.FS Fin.F1.
  Proof. 
    cbn. dependent elimination q'.
    - cbn. destruct (trans M (Fin.F1, c)) as [[[q' w] m] | ].
      dependent elimination q'; cbn; congruence. inversion 1.
    - cbn. dependent elimination t; cbn.
      + reflexivity.
      + destruct (trans M) as [[[q' w] m] | ].
        dependent elimination q'; cbn; congruence. inversion 1.
  Qed.

  Definition conv_state (q : Fin.t (S (num_states M))) : Fin.t (S (1 + num_states M)).
  Proof.
  dependent elimination q. exact Fin.F1. exact (Fin.FS (Fin.FS t)).
  Defined. (* because definition *)

  Lemma spec3 q c : trans M (q, c) = None -> trans M' (conv_state q, c) = Some (Fin.FS Fin.F1, None, Nmove).
  Proof.
    intros H. cbn. dependent elimination q; cbn.
    - destruct trans as [[[q' w] m] | ].
      dependent elimination q'; cbn. all:congruence.
    - destruct trans as [[[q' w] m] | ].
      dependent elimination q'; cbn. all:congruence.
  Qed.

  Lemma spec4 q c q' w m : trans M (q, c) = Some (q', w, m) -> trans M' (conv_state q, c) = Some (conv_state q', w, m).
  Proof.
    cbn. dependent elimination q; cbn; intros H.
    - rewrite H.
      dependent elimination q'; cbn. all:congruence.
    - rewrite H. revert H.
      dependent elimination q'; cbn. all:congruence.
  Qed.

End fixM.    

Lemma reduction :
  HaltKOSBTM ⪯ HaltKOSBTMu.
Proof.
  unshelve eexists.
  - intros [M t]. refine (_, t). exists (@M' M). exists (Fin.FS Fin.F1). split. eapply spec1. eapply spec2.
  - intros [M t]. cbn. split.
    + intros (q' & t' & H). assert (conv_state M Fin.F1 = Fin.F1) as E by reflexivity. cbn [Nat.add] in E.
      rewrite <- E. clear E. revert H. 
      generalize (@Fin.F1 (num_states M)) at 1 2. intros q H. exists t'.
      induction H.
      * econstructor. now eapply spec3. cbn. econstructor. reflexivity.
      * econstructor. 2:eassumption. now eapply spec4.
    + intros (t' & H). 
      assert (conv_state M Fin.F1 = Fin.F1) as E by reflexivity. cbn [Nat.add] in E.
      rewrite <- E in H. clear E. revert H.
      generalize (@Fin.F1 (num_states M)) at 1 3. intros q H.
      remember (conv_state M q) as q_.
      induction H in q, Heqq_ |- *; subst.
      * eexists. econstructor. eapply spec2 in H. dependent elimination q. inversion H. inversion H.
      * destruct t as [[ls c] rs]. destruct (trans M (q, c)) as [[[q'_ w_] m_] | ] eqn:Et; 
        pose proof (ET := Et).   
        -- eapply spec4 in Et. cbn [curr num_states M' Nat.add] in H. cbn [Nat.add] in Et. rewrite H in Et.
           inversion Et; subst; clear Et.
           edestruct IHeval as (? & ? & ?). reflexivity. exists x, x0. econstructor. exact ET. eassumption.
        -- eapply spec3 in Et. cbn [curr num_states M' Nat.add] in H. cbn [Nat.add] in Et. rewrite H in Et.
           inversion Et; subst; clear Et. exists q, (ls, c, rs).
            econstructor 1. eassumption.
Unshelve. exact q. exact t.
Qed.
