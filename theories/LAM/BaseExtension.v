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


(*
Lemma app_eq_cons X xs1 xs2 (y:X) ys:
  xs1++xs2 = y::ys -> xs1 <> nil -> exists ys', ys = ys'++xs2 /\ xs1=y::ys'.
Proof.
  induction xs1. tauto.
  intros [= -> eq]. eauto.
Qed.

Lemma app_cons_not_nil A xs (y:A) ys: xs++y::ys <> nil.
Proof.
  intros H. destruct xs; cbn in H;congruence. 
Qed.

(*Local Hint Extern 3 False => eapply app_cons_not_nil;eassumption.*)

Lemma app_neq_nilL X (xs ys :list X): xs <> [] -> xs++ys<>nil.
  destruct xs;subst;cbn; congruence.
Qed.

Lemma app_neq_nilR X (xs ys :list X): ys <> [] -> xs++ys<>nil.
  destruct xs;subst;cbn; congruence.
Qed.


Lemma cons_nil X x (xs :list X): x::xs <> [].
  destruct xs;subst;cbn; congruence.
Qed.

Lemma app_shift A (xs ys zs : list A) z: xs ++ ys = z :: zs -> xs <> [] -> exists zs', xs = z::zs' /\ zs = zs'++ys.
Proof with try eauto using app_neq_nilL,cons_nil.
  revert xs zs. induction ys;intros.
  -eexists;autorewrite with list in *;intuition eauto.
  -replace (xs ++ a :: ys)with ((xs ++ [a])++ ys) in H by (now repeat (cbn;autorewrite with list)).
   apply IHys in H;eauto...
   edestruct H as (zs'& eq1& eq2);eauto.
   edestruct (exists_last (l:=zs')) as (?&a'&->).
   +destruct zs'...
    change ([z]) with ([]++[z]) in eq1. eapply app_inj_tail in eq1;tauto.
   +change (z :: x ++ [a']) with ((z ::x) ++ [a']) in eq1.
    apply app_inj_tail in eq1 as [-> ->].  
    eexists;intuition. now autorewrite with list in *.
Qed.


Lemma cons_eq_app X xs1 (x:X) xs2 ys1 ys2:
  xs1 ++ x :: xs2 = ys1 ++ ys2 ->
  exists xs', (xs2 = xs'++ys2 /\  ys1 = xs1++x::xs')\/(xs1 = ys1++xs' /\ ys2 = xs'++x::xs2).
Proof.
  revert xs1 ys1;induction xs1;destruct ys1 as [ |y ys1'];cbn;autorewrite with list;intros [=];subst.
  -exists [];now right. 
  -eexists;eauto. 
  -eexists(_::_);cbn;eauto.
  -destruct (IHxs1 _ H1) as (xs' & [[-> ->]|[-> ->]] );exists xs';eauto.
Qed.


Lemma nth_nth_error (A : Type) (l : list A) (d : A) (n : nat): 
  n < |l| -> nth_error l n = Some (nth n l d).
Proof.
  revert n.
  induction l;destruct n;cbn;intros; firstorder;try omega.
Qed.

Lemma last_eq X d (x:X) xs : last (xs++[x]) d = x.
Proof.
  induction xs;cbn.
  -auto.
  -destruct _ eqn:eq. now destruct xs;cbn in eq. auto.
Qed.

Lemma removelast_eq X (x:X) xs : removelast (xs++[x]) = xs.
Proof.
  induction xs;cbn.
  -auto.
  -destruct _ eqn:eq. now destruct xs;cbn in eq. congruence.
Qed.

Lemma last_app_eq X (d:X) xs ys : ys <> nil -> last (xs++ys) d = last ys d.
Proof.
  induction xs;cbn.
  -auto.
  -destruct _ eqn:eq. now destruct xs;cbn in eq. auto.
Qed.

Hint Rewrite last_eq removelast_eq: list. 
 *)

