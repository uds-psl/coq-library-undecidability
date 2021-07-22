From Coq Require List Vector.

From Undecidability.TM Require Import TM Util.TM_facts.

Import ListNotations Vector.VectorNotations.

Definition encNatTM {Σ : Type} (s b : Σ) (n : nat) :=
  @midtape Σ [] b (repeat s n).

Definition TM_computable {k} (R : Vector.t nat k -> nat -> Prop) := 
  exists n : nat, exists Σ : finType, exists s b : Σ, s <> b /\ 
  exists M : TM Σ (1 + k + n),
  forall v : Vector.t nat k, 
  (forall m, R v m <-> exists q t, TM.eval M (start M) ((niltape :: Vector.map (encNatTM s b) v) ++ Vector.const niltape n) q t
                                /\ Vector.hd t = encNatTM s b m) /\
  (forall q t, TM.eval M (start M) ((niltape :: Vector.map (encNatTM s b) v) ++ Vector.const niltape n) q t ->
          exists m, Vector.hd t = encNatTM s b m).

Lemma TM_computable_iff {k} (R : Vector.t nat k -> nat -> Prop) :
  TM_computable R <->
  exists n : nat, exists Σ : finType, exists s b : Σ, s <> b /\ 
  exists M : TM Σ (1 + k + n),
  (forall v : Vector.t nat k, 
  (forall m, R v m -> exists q t, TM.eval M (start M) ((niltape :: Vector.map (encNatTM s b) v) ++ Vector.const niltape n) q t
                                /\ Vector.hd t = encNatTM s b m)) /\
   forall v : Vector.t nat k, (forall q t, TM.eval M (start M) ((niltape :: Vector.map (encNatTM s b) v) ++ Vector.const niltape n) q t ->
          exists m, R v m).
Proof.
  split.
  - intros (n & Σ & s & b & Hsb & M & H). exists n, Σ, s, b. split. 1:exact Hsb. exists M. split.
    + now intros v m Hvm % H.
    + intros v q t H'. pose proof H' as [m Ht] % H. exists m. eapply H. eauto.
  - intros (n & Σ & s & b & Hsb & M & H). exists n, Σ, s, b. split. 1:exact Hsb. exists M. intros v.
    split. 
    + intros m. split. 1: eapply H.
      intros (q & t & Heval & Ht). pose proof Heval as [m' Hm] % H.
      enough (m' = m) as -> by assumption.
      eapply H in Hm as (q' & t' & Heval' & Ht').
      eapply TM_eval_iff in Heval as [i Heval].
      eapply TM_eval_iff in Heval' as [i' Heval']. unfold loopM in *.
      eapply loop_injective in Heval. 2: eauto. inv Heval.
      rewrite Ht in Ht'. unfold encNatTM in Ht'. inv Ht'.
      eapply (f_equal (@length Σ)) in H1. rewrite !repeat_length in H1. congruence.
    + intros q t Heval. pose proof Heval as [m' Hm] % H. exists m'.
      eapply H in Hm as (q' & t' & Heval' & Ht').
      eapply TM_eval_iff in Heval as [i Heval].
      eapply TM_eval_iff in Heval' as [i' Heval']. unfold loopM in *.
      eapply loop_injective in Heval. 2: eauto. now inv Heval.
Qed.