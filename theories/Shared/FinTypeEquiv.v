From Undecidability.Shared.Libs.PSL Require Import FiniteTypes.

Fixpoint position {X : eqType} (x : X) (l : list X) : option (Fin.t (length l)).
Proof.
  induction l.
  - exact None.
  - cbn. decide (a = x).
    + exact (Some Fin.F1).
    + destruct (position _ x l) as [res | ].
      * exact (Some (Fin.FS res)). 
      * exact None.
Defined.

Lemma position_in {X : eqType} (x : X) (l : list X) (H : x el l) : 
  { i | position x l = Some i}.
Proof.  
    induction l; cbn in *.
    - inv H.
    - decide (a = x).
        + eauto.
        + destruct IHl as [i IH]. firstorder. rewrite IH. eauto.
Defined. 

Definition posIn {X : eqType} (x : X) (l : list X) (H : x el l) : Fin.t (length l).
Proof.
    eapply position_in in H. destruct (position x l) as [i | ]. exact i.
    abstract (exfalso; firstorder congruence).
Defined.

Fixpoint getat {X : Type} (l : list X) (i : Fin.t (length l)) : X.
Proof.
    destruct l.
    - inv i.
    - cbn in i. eapply (Fin.caseS' i (fun _ => X)).
      + exact x.
      + eapply getat.
Defined.

Arguments getat {_} _ _.

Lemma getatIn {X : Type} (l : list X) (i : Fin.t (length l)) : 
    getat l i el l.
Proof.
    induction l.
    - inv i.
    - cbn in *. eapply (Fin.caseS' i); cbn. eauto. eauto.
Qed.

Lemma finite_n (F : finType) :
    { n & {f : F -> Fin.t n & { g : Fin.t n -> F | (forall i, f (g i) = i) /\ forall x, g (f x) = x }}}.
Proof.
    destruct F as (X & [l H]). cbn in *. 
    exists (length l).
    assert (Hin : forall x, x el l). { intros x. eapply count_in_equiv. rewrite H. lia. }
    exists (fun x => proj1_sig (position_in (Hin x))). exists (@getat _ l). split.
    - intros i. destruct position_in. cbn.
      specialize (H (getat l i)). clear - H e. 
      induction l.
      + inv x.
      + cbn in *. revert H e.
        eapply (Fin.caseS' i). cbn.
        * decide (a = a); congruence.
        * cbn. intros. decide (getat l p = a).
         -- decide (a = getat l p); try congruence. subst. inv e. inv H.
            eapply countZero in H1 as []. eapply getatIn.
         -- decide (a = getat l p); try congruence.
            destruct position eqn:E; inv e. eapply IHl in E; congruence.
    - intros x. generalize (Hin x). clear. intros H.
      destruct (position_in H) as [i H1]. cbn.
      induction l; cbn in *. 
      + inv H1.
      + decide (a = x).
        * inv H1. cbn. reflexivity.
        * destruct (position x l) eqn:E; inv H1.
          cbn. eapply IHl. firstorder. reflexivity.
Qed.




