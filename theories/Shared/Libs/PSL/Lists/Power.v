From Undecidability.Shared.Libs.PSL Require Import BaseLists Dupfree.

(** *** Power lists *)

Section Power.
  Variable X : Type.

  Fixpoint power (U: list X ) : list (list X) :=
    match U with
    | nil => [nil]
    | x :: U' => power U' ++ map (cons x) (power U')
    end.
  
  Lemma power_incl A U :
    A el power U -> A <<= U.
  Proof.
    revert A; induction U as [|x U]; cbn; intros A D.
    - destruct D as [[]|[]]; auto.
    - apply in_app_iff in D as [E|E]. now auto.
      apply in_map_iff in E as [A' [E F]]. subst A.
      auto.
  Qed.

  Lemma power_nil U :
    nil el power U.
  Proof.
    induction U; cbn; auto.
  Qed.

End Power.

Section PowerRep.
  Variable X : eqType.
  Implicit Types A U : list X.

  Definition rep (A U : list X) : list X :=
    filter (fun x => Dec (x el A)) U.

  Lemma rep_cons A x U :
    x el A -> rep A (x::U) = x :: rep A U.
  Proof.
    intros H. apply filter_fst. auto.
  Qed.

  Lemma rep_cons' A x U :
    ~ x el A -> rep A (x::U) = rep A U.
  Proof.
    intros H. apply filter_fst'. auto.
  Qed.

  Lemma rep_cons_eq x A U :
    ~ x el U -> rep (x::A) U = rep A U.
  Proof.
    intros D. apply filter_pq_eq. intros y E.
    apply Dec_reflect_eq. split.
    - intros [<-|F]; tauto.
    - auto.
  Qed.

  Lemma rep_power A U :
    rep A U el power U.
  Proof.
    revert A; induction U as [|x U]; intros A.
    - cbn; auto.
    - decide (x el A) as [H|H].
      + rewrite (rep_cons _ H). cbn. auto using in_map.
      + rewrite (rep_cons' _ H). cbn. auto.
  Qed.

  Lemma rep_incl A U :
    rep A U <<= A.
  Proof.
    intros x. unfold rep. rewrite in_filter_iff, Dec_reflect.
    intuition.
  Qed.

  Lemma rep_in x A U :
    A <<= U -> x el A -> x el rep A U.
  Proof.
    intros D E. apply in_filter_iff; auto.
  Qed.

  Lemma rep_equi A U :
    A <<= U -> rep A U === A.
  Proof.
    intros D. split. now apply rep_incl.
    intros x. apply rep_in, D.
  Qed.

  Lemma rep_mono A B U :
    A <<= B -> rep A U <<= rep B U.
  Proof.
    intros D. apply filter_pq_mono.
    intros E; rewrite !Dec_reflect; auto.
  Qed.

  Lemma rep_eq' A B U :
    (forall x, x el U -> (x el A <-> x el B)) -> rep A U = rep B U.
  Proof.
    intros D. apply filter_pq_eq. intros x E.
    apply Dec_reflect_eq. auto.
  Qed.

  Lemma rep_eq A B U :
    A === B -> rep A U = rep B U.
  Proof.
    intros D. apply filter_pq_eq. intros x E.
    apply Dec_reflect_eq. firstorder.
  Qed.

  Lemma rep_injective A B U :
    A <<= U -> B <<= U -> rep A U = rep B U -> A === B.
  Proof.
    intros D E F. transitivity (rep A U). 
    - symmetry. apply rep_equi, D.
    - rewrite F. apply rep_equi, E.
  Qed.

  Lemma rep_idempotent A U :
    rep (rep A U) U = rep A U.
  Proof. 
    unfold rep at 1 3. apply filter_pq_eq.
    intros x D. apply Dec_reflect_eq. split.
    + apply rep_incl.
    + intros E. apply in_filter_iff. auto.
  Qed.
    
  Lemma dupfree_power U :
    dupfree U -> dupfree (power U).
  Proof.
    intros D. induction D as [|x U E D]; cbn.
    - constructor. now auto. constructor.
    - apply dupfree_app.
      + intros [A [F G]]. apply in_map_iff in G as [A' [G G']].
        subst A. apply E. apply (power_incl F). auto.
      + exact IHD.
      + apply dupfree_map; congruence.
  Qed.

  Lemma dupfree_in_power U A :
    A el power U -> dupfree U -> dupfree A.
  Proof.
    intros E D. revert A E.
    induction D as [|x U D D']; cbn; intros A E.
    - destruct E as [[]|[]]. constructor.
    - apply in_app_iff in E as [E|E].
      + auto.
      + apply in_map_iff in E as [A' [E E']]. subst A.
        constructor.
        * intros F; apply D. apply (power_incl E'), F.
        * auto.
  Qed.

  Lemma rep_dupfree A U :
    dupfree U -> A el power U -> rep A U = A.
  Proof.
    intros D; revert A. 
    induction D as [|x U E F]; intros A G.
    - destruct G as [[]|[]]; reflexivity.
    - cbn in G. apply in_app_iff in G as [G|G]. 
      + rewrite rep_cons'. now auto.
        contradict E. apply (power_incl G), E.
      + apply in_map_iff in G as [A' [<- H]].
        specialize (IHF _ H).
        rewrite rep_cons. 2:now auto.
        rewrite rep_cons_eq. now rewrite IHF. exact E.
   Qed.

  Lemma power_extensional A B U :
    dupfree U -> A el power U -> B el power U -> A === B -> A = B.
  Proof.
    intros D E F G. 
    rewrite <- (rep_dupfree D E). rewrite <- (rep_dupfree D F).
    apply rep_eq, G.
  Qed.

End PowerRep.

