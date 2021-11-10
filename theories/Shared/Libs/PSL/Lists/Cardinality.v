From Undecidability.Shared.Libs.PSL Require Export BaseLists Removal.

(* *** Cardinality *)

Section Cardinality.
  Variable X : eqType.
  Implicit Types A B : list X.

  Fixpoint card A :=
    match A with
      | nil => 0
      | x::A => if Dec (x el A) then card A else 1 + card A
    end.

  Lemma card_cons x A :
    x el A -> card (x::A) = card A.
  Proof.
    intros H. cbn. decide (x el A) as [H1|H1]; tauto.
  Qed.

  Lemma card_cons' x A :
    ~ x el A -> card (x::A) = 1 + card A.
  Proof.
    intros H. cbn. decide (x el A) as [H1|H1]; tauto.
  Qed.
  
  Lemma card_in_rem x A :
    x el A -> card A = 1 + card (rem A x).
  Proof.
    intros D. 
    induction A as [|y A].
    - contradiction D.
    - decide (y = x) as [->|H].
      + clear D. rewrite rem_fst.
        cbn. decide (x el A) as [H1|H1].
        * auto.
        * now rewrite (rem_id H1).
      + assert (x el A) as H1 by (destruct D; tauto). clear D.
        rewrite (rem_fst' _ H). specialize (IHA H1).
        simpl card at 2. 
        decide (y el rem A x) as [H2|H2].
        * rewrite card_cons. exact IHA.
          apply in_rem_iff in H2. intuition.
        * rewrite card_cons'. now rewrite IHA.
          contradict H2.  now apply in_rem_iff.
  Qed.
  
  Lemma card_not_in_rem A x :
    ~ x el A -> card A = card (rem A x).
  Proof.
    intros D; rewrite rem_id; auto.
  Qed.

  Lemma card_le A B :
    A <<= B -> card A <= card B.
  Proof.
  revert B. 
  induction A as [|x A]; intros B D; cbn.
  - lia.
  - apply incl_lcons in D as [D D1].
    decide (x el A) as [E|E].
    + auto.
    + rewrite (card_in_rem D).
      enough (card A <= card (rem B x)) by lia.
      apply IHA. auto.
  Qed.

  Lemma card_eq A B :
    A === B -> card A = card B.
  Proof.
    intros [E F]. apply card_le in E. apply card_le in F. lia.
  Qed.

  Lemma card_cons_rem x A :
    card (x::A) = 1 + card (rem A x).
  Proof.
    rewrite (card_eq (rem_equi x A)). cbn.
    decide (x el rem A x) as [D|D].
    - exfalso. apply in_rem_iff in D; tauto.
    - reflexivity.
  Qed.

  Lemma card_0 A :
    card A = 0 -> A = nil.
  Proof.
    destruct A as [|x A]; intros D.
    - reflexivity.
    - exfalso. rewrite card_cons_rem in D. lia.
  Qed.

  Lemma card_ex A B :
    card A < card B -> exists x, x el B /\ ~ x el A.
  Proof.
    intros D.
    decide (B <<= A) as [E|E].
    - exfalso. apply card_le in E. lia.
    - apply list_exists_not_incl; auto.
  Qed.

  Lemma card_equi A B :
    A <<= B -> card A = card B -> A === B.
  Proof.
    revert B. 
    induction A as [|x A]; cbn; intros B D E.
    - symmetry in E. apply card_0 in E. now rewrite E.
    - apply incl_lcons in D as [D D1].
      decide (x el A) as [F|F].
      + rewrite (IHA B); auto.
      + rewrite (IHA (rem B x)).
        * symmetry. apply rem_reorder, D.
        * auto.
        * apply card_in_rem in D. lia.
  Qed.

  Lemma card_lt A B x :
    A <<= B -> x el B -> ~ x el A -> card A < card B.
  Proof.
    intros D E F.
    decide (card A = card B) as [G|G].
    + exfalso. apply F. apply (card_equi D); auto.
    + apply card_le in D. lia.
  Qed.

  Lemma card_or A B :
    A <<= B -> A === B \/ card A < card B.
  Proof.
    intros D.
    decide (card A = card B) as [F|F].
    - left. apply card_equi; auto.
    - right. apply card_le in D. lia.
  Qed.

End Cardinality.

Global
Instance card_equi_proper (X: eqType) : 
  Proper (@equi X ==> eq) (@card X).
Proof. 
  hnf. apply card_eq.
Qed.
