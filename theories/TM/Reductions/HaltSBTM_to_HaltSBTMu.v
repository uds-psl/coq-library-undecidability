Require Import Undecidability.TM.SBTM.
Require Import Undecidability.Synthetic.Definitions.

Set Default Proof Using "Type".

Section fixM.

  Variable M : SBTM.

  Definition M' : SBTM.
  Proof using M.
    exists (1 + num_states M).
    intros [q o].
    remember (1 + num_states M) as n eqn:En. revert En.
    change ((fun n' (q' : Fin.t (S n')) =>
      n' = 1 + num_states M ->  option (Fin.t (S n') * option bool * move)) n q).
    apply Fin.caseS.
    - destruct (trans M (Fin.F1, o)) as [[[q' w] m] | ].
      pattern q'. apply (Fin.caseS' q').
      + intros ? ?. exact (Some (Fin.F1, w, m)).
      + intros t ? ->. exact (Some (Fin.FS (Fin.FS t), w, m)).
      + intros ? ->. exact (Some (Fin.FS Fin.F1, None, Nmove)).
    - clear n q. intros n [|? t].
      + intros ?. exact None.
      + intros [= E]. rewrite E in t. rewrite E.
        destruct (trans M (Fin.FS t, o)) as [[[q' w] m] | ].
        pattern q'. apply (Fin.caseS' q').
        * exact (Some (Fin.F1, w, m)).
        * intros t'. exact (Some (Fin.FS (Fin.FS t'), w, m)).
        * exact (Some (Fin.FS Fin.F1, None, Nmove)).
  Defined. (* because definition *)

  Lemma spec1 c : trans M' (Fin.FS Fin.F1, c) = None.
  Proof. reflexivity. Qed.

  Lemma spec2 c q' : trans M' (q', c) = None -> q' = Fin.FS Fin.F1.
  Proof.
    cbn. apply (Fin.caseS' q').
    - cbn. clear q'. destruct (trans M (Fin.F1, c)) as [[[q' w] m] | ].
      + now apply (Fin.caseS' q'); cbn.
      + easy.
    - cbn. intros t. apply (Fin.caseS' t).
      + easy.
      + cbn. clear t q'. intros t.
        destruct (trans M _) as [[[q' w] m] | ].
        * cbn. now apply (Fin.caseS' q').
        * easy.
  Qed.

  Definition conv_state (q : Fin.t (S (num_states M))) : Fin.t (S (1 + num_states M)).
  Proof.
    pattern q. apply (Fin.caseS' q).
    - exact Fin.F1.
    - intros t. exact (Fin.FS (Fin.FS t)).
  Defined. (* because definition *)

  Lemma spec3 q c : trans M (q, c) = None -> trans M' (conv_state q, c) = Some (Fin.FS Fin.F1, None, Nmove).
  Proof.
    cbn. apply (Fin.caseS' q); cbn.
    - now destruct trans as [[[q' w] m] | ].
    - intros t. now destruct trans as [[[q' w] m] | ].
  Qed.

  Lemma spec4 q c q' w m : trans M (q, c) = Some (q', w, m) -> trans M' (conv_state q, c) = Some (conv_state q', w, m).
  Proof.
    apply (Fin.caseS' q); cbn.
    - intros ->. now apply (Fin.caseS' q').
    - intros t ->. now apply (Fin.caseS' q').
  Qed.

End fixM.    

Lemma reduction :
  HaltSBTM ⪯ HaltSBTMu.
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
      * eexists. econstructor. eapply spec2 in H.
        revert H. now apply (Fin.caseS' q).
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
