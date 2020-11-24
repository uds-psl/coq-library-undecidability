From Undecidability.Shared.Libs.PSL Require Export BaseLists Filter.

(* *** Element removal *)

Section Removal.
  Variable X : eqType.
  Implicit Types (x y: X) (A B: list X).

  Definition rem A x : list X :=
    filter (fun z => Dec (z <> x)) A.

  Lemma in_rem_iff x A y :
    x el rem A y <-> x el A /\ x <> y.
  Proof.
    unfold rem. rewrite in_filter_iff, Dec_reflect. tauto.
  Qed.

  Lemma rem_not_in x y A :
    x = y \/ ~ x el A -> ~ x el rem A y.
  Proof.
    unfold rem. rewrite in_filter_iff, Dec_reflect. tauto.
  Qed.

  Lemma rem_incl A x :
    rem A x <<= A.
  Proof.
    apply filter_incl.
  Qed.

  Lemma rem_mono A B x :
    A <<= B -> rem A x <<= rem B x.
  Proof.
    apply filter_mono.
  Qed.

  Lemma rem_cons A B x :
    A <<= B -> rem (x::A) x <<= B.
  Proof.
    intros E y F. apply E. apply in_rem_iff in F.
    destruct F as [[|]]; congruence.
  Qed.

  Lemma rem_cons' A B x y :
    x el B -> rem A y <<= B -> rem (x::A) y <<= B.
  Proof.
    intros E F u G. 
    apply in_rem_iff in G as [[[]|G] H]. exact E.
    apply F. apply in_rem_iff. auto.
  Qed.

  Lemma rem_in x y A :
    x el rem A y -> x el A.
  Proof.
    apply rem_incl.
  Qed.

  Lemma rem_neq x y A :
    x <> y -> x el A -> x el rem A y.
  Proof.
    intros E F. apply in_rem_iff. auto.
  Qed.

  Lemma rem_app x A B :
    x el A -> B <<= A ++ rem B x.
  Proof.
    intros E y F. decide (x=y) as [[]|]; auto using rem_neq.
  Qed.

  Lemma rem_app' x A B C :
    rem A x <<= C -> rem B x <<= C -> rem (A ++ B) x <<= C.
  Proof.
    unfold rem; rewrite filter_app; auto.
  Qed.

  Lemma rem_equi x A :
    x::A === x::rem A x.
  Proof.
    split; intros y; 
    intros [[]|E]; decide (x=y) as [[]|D]; 
    eauto using rem_in, rem_neq. 
  Qed.

  Lemma rem_comm A x y :
    rem (rem A x) y = rem (rem A y) x.
  Proof.
    apply filter_comm.
  Qed.

  Lemma rem_fst x A :
    rem (x::A) x = rem A x.
  Proof.
    unfold rem. rewrite filter_fst'; auto.
  Qed.

  Lemma rem_fst' x y A :
    x <> y -> rem (x::A) y = x::rem A y.
  Proof.
    intros E. unfold rem. rewrite filter_fst; auto.
  Qed.

  Lemma rem_id x A :
    ~ x el A -> rem A x = A.
  Proof.
    intros D. apply filter_id. intros y E.
    apply Dec_reflect. congruence.
  Qed.

  Lemma rem_reorder x A :
    x el A -> A === x :: rem A x.
  Proof.
    intros D. rewrite <- rem_equi. apply equi_push, D.
  Qed.

  Lemma rem_inclr A B x :
    A <<= B -> ~ x el A -> A <<= rem B x.
  Proof.
    intros D E y F. apply in_rem_iff.
    intuition; subst; auto. 
  Qed.

End Removal.

Hint Resolve rem_not_in rem_incl rem_mono rem_cons rem_cons' rem_app rem_app' rem_in rem_neq rem_inclr : core.
