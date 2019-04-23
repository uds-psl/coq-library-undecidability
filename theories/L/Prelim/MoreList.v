Require Import PslBase.Base.
(** Nats smaller than n *)

Fixpoint natsLess n : list nat :=
  match n with
    0 => []
  | S n => n :: natsLess n
  end.

Lemma natsLess_in_iff n m:
  n el natsLess m <-> n < m.
Proof.
  induction m in n|-*;cbn. omega.
  split.
  -intuition. destruct n;intuition. apply IHm in H0. omega.
  -intros. decide (m=n). intuition. right. apply IHm. omega.
Qed.


Lemma natsLess_S n :
  natsLess (S n) = map S (natsLess n)++[0].
Proof.
  induction n;cbn in *;congruence.
Qed.


(** Sum *)

Fixpoint sumn (A:list nat) :=
  match A with
    [] => 0
  | a::A => a + sumn A
  end.

Lemma sumn_app A B : sumn (A++B) = sumn A + sumn B.
Proof.
  induction A;cbn;omega.
Qed.

Hint Rewrite sumn_app : list. 

Lemma length_concat X (A : list (list X)) :
  length (concat A) = sumn (map (@length _) A).
  induction A;cbn. reflexivity. autorewrite with list in *. omega.
Qed.

Lemma sumn_rev A :
  sumn A = sumn (rev A).
Proof.
  enough (H:forall B, sumn A + sumn B = sumn (rev A++B)).
  {specialize (H []). cbn in H. autorewrite with list in H. cbn in H. omega. }
  induction A as [|a A];intros B. reflexivity.
  cbn in *. specialize (IHA (a::B)). autorewrite with list in *. cbn in *. omega.
Qed.

Lemma sumn_map_natsLess f n :
  sumn (map f (natsLess n)) = sumn (map (fun i => f (n - (1 + i))) (natsLess n)).
Proof.
  rewrite sumn_rev. f_equal.
  rewrite <- map_rev.
  rewrite <- map_map with (g:=f) (f:= fun i => (n - (1+i))).
  f_equal.
  induction n;intros;autorewrite with list in *. reflexivity.
  rewrite natsLess_S at 2. cbn. rewrite map_app. cbn.
  rewrite map_map. cbn in IHn.
  rewrite IHn. rewrite <- minus_n_O. reflexivity.
Qed.
