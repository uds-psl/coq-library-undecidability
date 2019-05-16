Require Export PslBase.Base.

Lemma nth_error_lt_Some A (H:list A) a : a < |H| -> exists x, nth_error H a = Some x.
Proof.
  intros eq. revert H eq. induction a;intros;destruct H;cbn in *;inv eq;eauto. all:edestruct (IHa H); try omega; eauto.
Qed.

Lemma map_nth_lt (A B : Type) (f : A -> B) x (l : list A) (d : A) (n : nat): 
  n < | l | -> nth n (map f l) x = f (nth n l d).
Proof.
  revert n.
  induction l;cbn;intros;try firstorder omega.
  destruct _;firstorder.
Qed.

Lemma nth_error_nth (A : Type) x (l : list A) (d : A) (n : nat): 
  nth_error l n = Some x -> nth n l d = x.
Proof.
  revert n.
  induction l;destruct n;cbn;intros; firstorder;congruence.
Qed.


Lemma nth_error_Some_lt A (H:list A) a x : nth_error H a = Some x -> a < |H|.
Proof.
  intros eq. revert H eq. induction a;intros;destruct H;cbn in *;inv eq. omega. apply IHa in H1. omega.
Qed.

Lemma nth_length X (d:X) A n: nth n A d <> d -> n < length A.
Proof.
  revert n. induction A;intros [] neq;cbn in *;try congruence;try firstorder omega.
Qed.

Lemma Forall_map X Y (A:list X) p (f:X->Y):
  Forall (fun x => p (f x)) A -> Forall p (map f A).
Proof.
  rewrite !Forall_forall. setoid_rewrite in_map_iff. firstorder subst. eauto.
Qed.


Lemma Forall_nth X P E i (x:X): Forall P E -> nth_error E i = Some x -> P x.
Proof.
  intros. eapply Forall_forall. eassumption. eapply nth_error_In. eauto.
Qed.

Lemma Forall2_nth1 X Y (P:X->Y->Prop) A B i a: Forall2 P A B -> nth_error A i = Some a -> (exists b, P a b /\ nth_error B i = Some b).
Proof.
  intros. induction H in i,H0|-*;destruct i; inv H0. now eauto. edestruct IHForall2;eauto.
Qed.

Lemma Forall2_nth2 X Y (P:X->Y->Prop) A B i b: Forall2 P A B -> nth_error B i = Some b -> (exists a, P a b /\ nth_error A i = Some a).
Proof.
  intros. induction H in i,H0|-*;destruct i; inv H0. now eauto. edestruct IHForall2;eauto.
Qed.

Lemma Forall2_length X Y (P:X->Y->Prop) A B: Forall2 P A B -> length A = length B.
Proof.
  intros. induction H;cbn in *;omega.
Qed.

Lemma Forall2_impl X Y (P1 P2:X->Y->Prop) A B: (forall x y, P1 x y -> P2 x y) -> Forall2 P1 A B -> Forall2 P2 A B.
Proof.
  intros ? H. induction H;cbn in *;eauto.
Qed.
