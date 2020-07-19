Require Import List.

(** Filter *)

Section Filter.
  Variable X : Type.
  Implicit Types (x y: X) (A B C: list X) (p q: X -> bool).

  Local Notation "x 'el' L" := (In x L) (at level 50).

  Lemma in_filter_iff x p A :
    x el filter p A <-> x el A /\ p x = true.
  Proof. 
    induction A as [|y A]; cbn.
    - tauto.
    - destruct (p y) eqn:E; cbn;
      rewrite IHA; intuition; subst; auto. congruence.
  Qed.

  Local Notation "A '<<=' B" := (incl A B) (at level 50).

  Lemma filter_incl p A :
    filter p A <<= A.  
  Proof.
    intros x D. apply in_filter_iff in D. apply D.
  Qed.

  Lemma filter_mono p A B :
    A <<= B -> filter p A <<= filter p B.
  Proof.
    intros D x E. apply in_filter_iff in E as [E E'].
    apply in_filter_iff. auto.
  Qed.

  Lemma filter_id p A :
    (forall x, x el A -> p x = true) -> filter p A = A.
  Proof.
    intros D.
    induction A as [|x A]; cbn.
    - reflexivity.
    - destruct (p x) eqn:E.
      + f_equal. eapply IHA. intros y H. apply D. cbn. eauto.
      + exfalso. rewrite D in E. congruence. cbn. eauto.
  Qed.

  Lemma filter_app p A B :
    filter p (A ++ B) = filter p A ++ filter p B.
  Proof.
    induction A as [|y A]; cbn.
    - reflexivity.
    - rewrite IHA. destruct (p y); reflexivity.  
  Qed.

  Lemma filter_fst p x A :
    p x = true -> filter p (x::A) = x::filter p A.
  Proof.
    cbn. destruct (p x); auto. congruence.
  Qed.

  Lemma filter_fst' p x A :
    p x = false -> filter p (x::A) = filter p A.
  Proof.
    cbn. destruct (p x); auto; congruence.
  Qed.

  Lemma filter_pq_mono p q A :
    (forall x, x el A -> p x = true -> q x = true) -> filter p A <<= filter q A.
  Proof. 
    intros D x E. apply in_filter_iff in E as [E E'].
    apply in_filter_iff. auto.
  Qed.

  Lemma filter_pq_eq p q A :
    (forall x, x el A -> p x = q x) -> filter p A = filter q A.
  Proof. 
    intros C; induction A as [|x A]; cbn.
    - reflexivity.
    - destruct (p x) eqn:D, (q x) eqn:E.
      + f_equal. eapply IHA. intros. eapply C. cbn. eauto.
      + exfalso. enough (p x = q x) by congruence. firstorder.
      + exfalso. enough (p x = q x) by congruence. firstorder.
      + firstorder.
  Qed.

  Lemma filter_and p q A :
    filter p (filter q A) = filter (fun x => andb (p x) (q x)) A.
  Proof.
    induction A as [|x A]; cbn. reflexivity.
    destruct (p x) eqn:E, (q x); cbn;
      try rewrite E; now rewrite IHA.
  Qed.

  Lemma filter_comm p q A :
    filter p (filter q A) = filter q (filter p A).
  Proof.
    rewrite !filter_and. apply filter_pq_eq.
    intros x _. now destruct (p x), (q x).
  Qed.
  
End Filter.
