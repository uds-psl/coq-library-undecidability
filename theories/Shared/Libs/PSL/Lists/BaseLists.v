From Undecidability.Shared.Libs.PSL Require Export Prelim EqDec.

Export List.ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).
Notation "| A |" := (length A) (at level 65).
Definition equi X (A B : list X) : Prop := incl A B /\ incl B A.
Notation "A === B" := (equi A B) (at level 70).
#[export] Hint Unfold equi : core.

#[export] Hint Extern 4 => 
match goal with
|[ H: ?x el nil |- _ ] => destruct H
end : core.

(* ** Lists *)

(* Register additional simplification rules with autorewrite / simpl_list *)
(* Print Rewrite HintDb list. *)
Hint Rewrite <- app_assoc : list.
Hint Rewrite rev_app_distr map_app prod_length : list.

Lemma list_cycle  (X : Type) (A : list X) x :
  x::A <> A.
Proof.
  intros B.
  assert (C: |x::A| <> |A|) by (cbn; lia).
  apply C. now rewrite B.
Qed.

(* *** Decisions for lists *)

Instance list_in_dec X (x : X) (A : list X) :  
  eq_dec X -> dec (x el A).
Proof.
  intros D. apply in_dec. exact D.
Qed.

(* Certifying find *)

Lemma cfind X A (p: X -> Prop) (p_dec: forall x, dec (p x)) :
  {x | x el A /\ p x} + {forall x, x el A -> ~ p x}.
Proof.
  destruct (find (fun x => Dec (p x)) A) eqn:E.
  - apply find_some in E. firstorder.
  - right. intros. eapply find_none in E; eauto.
Qed.

Arguments cfind {X} A p {p_dec}.

Instance list_forall_dec X A (p : X -> Prop) :
  (forall x, dec (p x)) -> dec (forall x, x el A -> p x).
Proof.
  intros p_dec.
  destruct (find (fun x => Dec (~ p x)) A) eqn:Eq.
  - apply find_some in Eq as [H1 H0 %Dec_true]; right; auto. 
  - left. intros x E. apply find_none with (x := x) in Eq. apply dec_DN; auto. auto.
Qed.

Instance list_exists_dec X A (p : X -> Prop) :
  (forall x, dec (p x)) -> dec (exists x, x el A /\ p x).
Proof.
  intros p_dec.
  destruct (find (fun x => Dec (p x)) A) eqn:Eq. (* New: eta expansion needed *)
  - apply find_some in Eq as [H0 H1 %Dec_true]. firstorder. (* New: Need firstorder here *)
  - right. intros [x [E F]]. apply find_none with (x := x) in Eq; auto. eauto. (* New: Why can't auto solve this? *)
Qed.

Lemma list_exists_DM X A  (p : X -> Prop) : 
  (forall x, dec (p x)) ->
  ~ (forall x, x el A -> ~ p x) -> exists x, x el A /\ p x.
Proof. 
  intros D E. 
  destruct (find (fun x => Dec (p x)) A) eqn:Eq.
  + apply find_some in Eq as [? ?%Dec_true]. eauto.
  + exfalso. apply E. intros. apply find_none with (x := x) in Eq;  eauto. 
Qed.

Lemma list_exists_not_incl (X: eqType) (A B : list X) :
  ~ A <<= B -> exists x, x el A /\ ~ x el B.
Proof.
  intros E.
  apply list_exists_DM; auto.
  intros F. apply E. intros x G.
  apply dec_DN; auto.
Qed.

Lemma list_cc X (p : X -> Prop) A : 
  (forall x, dec (p x)) -> 
  (exists x, x el A /\ p x) -> {x | x el A /\ p x}.
Proof.
  intros D E. 
  destruct (cfind A p) as [[x [F G]]|F].
  - eauto.
  - exfalso. destruct E as [x [G H]]. apply (F x); auto.
Qed.



(* *** Membership

We use the following lemmas from Coq's standard library List.
- [in_eq :  x el x::A]
- [in_nil :  ~ x el nil]
- [in_cons :  x el A -> x el y::A]
- [in_or_app :  x el A \/ x el B -> x el A++B]
- [in_app_iff :  x el A++B <-> x el A \/ x el B]
- [in_map_iff :  y el map f A <-> exists x, f x = y /\ x el A]
*)

#[export] Hint Resolve in_eq in_nil in_cons in_or_app : core.

Section Membership.
  Variable X : Type.
  Implicit Types (x y: X) (A B: list X).

  Lemma in_sing x y :
    x el [y] -> x = y.
  Proof. 
    cbn. intros [[]|[]]. reflexivity. 
  Qed.

  Lemma in_cons_neq x y A :
    x el y::A -> x <> y -> x el A.
  Proof. 
    cbn. intros [[]|D] E; congruence. 
  Qed.

  Lemma not_in_cons x y A :
    ~ x el y :: A -> x <> y /\ ~ x el A.
  Proof.
    intuition; subst; auto.
  Qed.

(* *** Disjointness *)

  Definition disjoint A B :=
    ~ exists x, x el A /\ x el B.

  Lemma disjoint_forall A B :
    disjoint A B <-> forall x, x el A -> ~ x el B.
  Proof.
    split.
    - intros D x E F. apply D. exists x. auto.
    - intros D [x [E F]]. exact (D x E F).
  Qed.

  Lemma disjoint_symm A B :
    disjoint A B -> disjoint B A.
  Proof.
    firstorder.
  Qed.

  Lemma disjoint_incl A B B' :
    B' <<= B -> disjoint A B -> disjoint A B'.
  Proof.
    firstorder.
  Qed.

  Lemma disjoint_nil B :
    disjoint nil B.
  Proof.
    firstorder.
  Qed.

  Lemma disjoint_nil' A :
    disjoint A nil.
  Proof.
    firstorder.
  Qed.
  
  Lemma disjoint_cons x A B :
    disjoint (x::A) B <-> ~ x el B /\ disjoint A B.
  Proof.
    split.
    - intros D. split.
      + intros E. apply D. eauto.
      + intros [y [E F]]. apply D. eauto.
    - intros [D E] [y [[F|F] G]]. 
      + congruence.
      + apply E. eauto.
  Qed.

  Lemma disjoint_app A B C :
    disjoint (A ++ B) C <-> disjoint A C /\ disjoint B C.
  Proof.
    split.
    - intros D. split.
      + intros [x [E F]]. eauto 6.
      + intros [x [E F]]. eauto 6.
    - intros [D E] [x [F G]]. 
      apply in_app_iff in F as [F|F]; eauto.
  Qed.

End Membership.

#[export] Hint Resolve disjoint_nil disjoint_nil' : core.

(* *** Inclusion

We use the following lemmas from Coq's standard library List.
- [incl_refl :  A <<= A]
- [incl_tl :  A <<= B -> A <<= x::B]
- [incl_cons : x el B -> A <<= B -> x::A <<= B]
- [incl_appl : A <<= B -> A <<= B++C]
- [incl_appr : A <<= C -> A <<= B++C]
- [incl_app : A <<= C -> B <<= C -> A++B <<= C]
*)

#[export] Hint Resolve incl_refl incl_tl incl_cons incl_appl incl_appr incl_app : core.

Lemma incl_nil X (A : list X) :
  nil <<= A.

Proof. intros x []. Qed.

#[export] Hint Resolve incl_nil : core.

Lemma incl_map X Y A B (f : X -> Y) :
  A <<= B -> map f A <<= map f B.

Proof.
  intros D y E. apply in_map_iff in E as [x [E E']].
  subst y. apply in_map_iff. eauto.
Qed.

Section Inclusion.
  Variable X : Type.
  Implicit Types A B : list X.

  Lemma incl_nil_eq A :
    A <<= nil -> A=nil.

  Proof.
    intros D. destruct A as [|x A].
    - reflexivity.
    - exfalso. apply (D x). auto.
  Qed.

  Lemma incl_shift x A B :
    A <<= B -> x::A <<= x::B.

  Proof. auto. Qed.

  Lemma incl_lcons x A B :
    x::A <<= B <-> x el B /\ A <<= B.
  Proof. 
    split. 
    - intros D. split; hnf; auto.
    - intros [D E] z [F|F]; subst; auto.
  Qed.

  Lemma incl_sing x A y :
    x::A <<= [y] -> x = y /\ A <<= [y].
  Proof.
    rewrite incl_lcons. intros [D E].
    apply in_sing in D. auto.
  Qed.

  Lemma incl_rcons x A B :
    A <<= x::B -> ~ x el A -> A <<= B.

  Proof. intros C D y E. destruct (C y E) as [F|F]. 1: congruence. assumption. Qed.

  Lemma incl_lrcons x A B :
    x::A <<= x::B -> ~ x el A -> A <<= B.

  Proof.
    intros C D y E.
    assert (F: y el x::B) by auto.
    destruct F as [F|F]; congruence.
  Qed.

  Lemma incl_app_left A B C :
    A ++ B <<= C -> A <<= C /\ B <<= C.
  Proof.
    firstorder.
  Qed.

End Inclusion.

Definition inclp (X : Type) (A : list X) (p : X -> Prop) : Prop :=
  forall x, x el A -> p x.

(* *** Setoid rewriting with list inclusion and list equivalence *)

Instance incl_preorder X : 
  PreOrder (@incl X).
Proof. 
  constructor; hnf; unfold incl; auto. 
Qed.

Instance equi_Equivalence X : 
  Equivalence (@equi X).
Proof. 
  constructor; hnf; firstorder. 
Qed.

Instance incl_equi_proper X : 
  Proper (@equi X ==> @equi X ==> iff) (@incl X).
Proof. 
  hnf. intros A B D. hnf. firstorder. 
Qed.

Instance cons_incl_proper X x : 
  Proper (@incl X ==> @incl X) (@cons X x).
Proof.
  hnf. apply incl_shift.
Qed.

Instance cons_equi_proper X x : 
  Proper (@equi X ==> @equi X) (@cons X x).
Proof. 
  hnf. firstorder.
Qed.

Instance in_incl_proper X x : 
  Proper (@incl X ==> Basics.impl) (@In X x).
Proof.
  intros A B D. hnf. auto.
Qed.

Instance in_equi_proper X x : 
  Proper (@equi X ==> iff) (@In X x).
Proof. 
  intros A B D. firstorder. 
Qed.

Instance app_incl_proper X : 
  Proper (@incl X ==> @incl X ==> @incl X) (@app X).
Proof. 
  intros A B D A' B' E. auto.
Qed.

Instance app_equi_proper X : 
  Proper (@equi X ==> @equi X ==> @equi X) (@app X).
Proof. 
  hnf. intros A B D. hnf. intros A' B' E.
  destruct D, E; auto.
Qed.

Section Equi.
  Variable X : Type.
  Implicit Types A B : list X.

  Lemma equi_push x A :
    x el A -> A === x::A.
  Proof.
    auto.
  Qed.

  Lemma equi_dup x A :
    x::A === x::x::A.

  Proof.
    auto.
  Qed.

  Lemma equi_swap x y A:
    x::y::A === y::x::A.
  Proof.
    split; intros z; cbn; tauto.
  Qed.

  Lemma equi_shift x A B :
    x::A++B === A++x::B.
  Proof. 
    split; intros y.
    - intros [D|D].
      + subst; auto.
      + apply in_app_iff in D as [D|D]; auto.
    - intros D. apply in_app_iff in D as [D|D].
      + auto.
      + destruct D; subst; auto.
  Qed.

  Lemma equi_rotate x A :
    x::A === A++[x]. 
  Proof. 
    split; intros y; cbn.
    - intros [D|D]; subst; auto.
    - intros D. apply in_app_iff in D as [D|D].
      + auto.
      + apply in_sing in D. auto.
  Qed.
  
End Equi.

Lemma in_concat_iff A l (a:A) : a el concat l <-> exists l', a el l' /\ l' el l.
Proof.
  induction l; cbn.
  - intuition. now destruct H. 
  - rewrite in_app_iff, IHl. firstorder subst. auto.
Qed.


Lemma app_comm_cons' (A : Type) (x y : list A) (a : A) :
  x ++ a :: y = (x ++ [a]) ++ y.
Proof. rewrite <- app_assoc. cbn. trivial. Qed.


(* skipn *)

Lemma skipn_nil (X : Type) (n : nat) : skipn n nil = @nil X.
Proof. destruct n; cbn; auto. Qed.

Lemma skipn_app (X : Type) (xs ys : list X) (n : nat) :
  n = (| xs |) ->
  skipn n (xs ++ ys) = ys.
Proof.
  intros ->. revert ys. induction xs; cbn; auto.
Qed.

Lemma skipn_length (X : Type) (n : nat) (xs : list X) :
  length (skipn n xs) = length xs - n.
Proof.
  revert xs. induction n; intros; cbn.
  - lia.
  - destruct xs; cbn; auto.
Qed.



(* Repeat *)

Lemma map_repeat (X Y : Type) (f : X -> Y) (n : nat) (a : X) :
  map f (repeat a n) = repeat (f a) n.
Proof. induction n; cbn in *; f_equal; auto. Qed.

Lemma repeat_add_app (X : Type) (m n : nat) (a : X) :
  repeat a (m + n) = repeat a m ++ repeat a n.
Proof. induction m; cbn; f_equal; auto. Qed.

Lemma repeat_S_cons (X : Type) (n : nat) (a : X) :
  a :: repeat a n = repeat a n ++ [a].
Proof.
  replace (a :: repeat a n) with (repeat a (S n)) by trivial. replace (S n) with (n+1) by lia.
  rewrite repeat_add_app. cbn. trivial.
Qed.

Lemma repeat_app_eq (X : Type) (m n : nat) (a : X) :
  repeat a n ++ repeat a m = repeat a m ++ repeat a n.
Proof. rewrite <- !repeat_add_app. f_equal. lia. Qed.

Lemma repeat_eq_iff (X : Type) (n : nat) (a : X) x :
  x = repeat a n <-> length x = n /\ forall y, y el x -> y = a.
Proof.
  split.
  {
    intros ->. split. apply repeat_length. apply repeat_spec.
  }
  {
    revert x. induction n; intros x (H1&H2); cbn in *.
    - destruct x; cbn in *; congruence.
    - destruct x; cbn in *; inv H1. f_equal.
      + apply H2. auto.
      + apply IHn. auto.
  }
Qed.

Lemma rev_repeat (X : Type) (n : nat) (a : X) :
  rev (repeat a n) = repeat a n.
Proof.
  apply repeat_eq_iff. split.
  - rewrite rev_length. rewrite repeat_length. auto.
  - intros y Hx % in_rev. eapply repeat_spec; eauto.
Qed.

Lemma concat_repeat_repeat (X : Type) (n m : nat) (a : X) :
  concat (repeat (repeat a n) m) = repeat a (m*n).
Proof.
  induction m as [ | m' IHm]; cbn.
  - auto.
  - rewrite repeat_add_app. f_equal. auto.
Qed.


Corollary skipn_repeat_add (X : Type) (n m : nat) (a : X) :
  skipn n (repeat a (n + m)) = repeat a m.
Proof.
  rewrite repeat_add_app. erewrite skipn_app; eauto. symmetry. apply repeat_length.
Qed.

Corollary skipn_repeat (X : Type) (n : nat) (a : X) :
  skipn n (repeat a n) = nil.
Proof.
  rewrite <- (app_nil_r (repeat a n)). erewrite skipn_app; eauto. symmetry. apply repeat_length.
Qed.


(* Facts about equality for [map] and [rev] *)
Lemma rev_eq_nil (Z: Type) (l: list Z) :
  rev l = nil -> l = nil.
Proof. intros. destruct l; cbn in *. reflexivity. symmetry in H. now apply app_cons_not_nil in H. Qed.

Lemma map_eq_nil (Y Z: Type) (f: Y->Z) (l: list Y) :
  map f l = nil -> l = nil.
Proof. intros. destruct l; cbn in *. reflexivity. congruence. Qed.

Lemma map_eq_nil' (Y Z: Type) (f: Y->Z) (l: list Y) :
  nil = map f l -> l = nil.
Proof. now intros H % eq_sym % map_eq_nil. Qed.

Lemma map_eq_cons (A B: Type) (f: A->B) (xs: list A) (y: B) (ys: list B) :
  map f xs = y :: ys ->
  exists x xs', xs = x :: xs' /\
          y = f x /\
          ys = map f xs'.
Proof. induction xs; intros H; cbn in *; inv H; eauto. Qed.

Lemma map_eq_cons' (A B: Type) (f: A -> B) (xs: list A) (y: B) (ys: list B) :
  y :: ys = map f xs ->
  exists x xs', xs = x :: xs' /\
          y = f x /\
          ys = map f xs'.
Proof. now intros H % eq_sym % map_eq_cons. Qed.


Lemma map_eq_app (A B: Type) (f: A -> B) (ls : list A) (xs ys : list B) :
  map f ls = xs ++ ys ->
  exists ls1 ls2, ls = ls1 ++ ls2 /\
             xs = map f ls1 /\
             ys = map f ls2.
Proof.
  revert xs ys. induction ls; intros; cbn in *.
  - symmetry in H. apply app_eq_nil in H as (->&->). exists nil, nil. cbn. tauto.
  - destruct xs; cbn in *.
    + exists nil. eexists. repeat split. cbn. now subst.
    + inv H. specialize IHls with (1 := H2) as (ls1&ls2&->&->&->).
      repeat econstructor. 2: instantiate (1 := a :: ls1). all: reflexivity.
Qed.

Lemma rev_eq_cons (A: Type) (ls: list A) (x : A) (xs: list A) :
  rev ls = x :: xs ->
  ls = rev xs ++ [x].
Proof. intros H. rewrite <- rev_involutive at 1. rewrite H. cbn. reflexivity. Qed.



(* Injectivity of [map], if the function is injective *)
Lemma map_injective (X Y: Type) (f: X -> Y) :
  (forall x y, f x = f y -> x = y) ->
  forall xs ys, map f xs = map f ys -> xs = ys.
Proof.
  intros HInj. hnf. intros x1. induction x1 as [ | x x1' IH]; intros; cbn in *.
  - now apply map_eq_nil' in H.
  - now apply map_eq_cons' in H as (l1&l2&->&->%HInj&->%IH).
Qed.

Instance map_ext_proper A B: Proper (@ pointwise_relation A B (@eq B) ==> (@eq (list A)) ==> (@eq (list B))) (@map A B).
Proof.
  intros f f' Hf a ? <-. induction a;cbn;congruence.
Qed.

(* ** Lemmas about [hd], [tl] and [removelast] *)

Lemma tl_map (A B: Type) (f: A -> B) (xs : list A) :
  tl (map f xs) = map f (tl xs).
Proof. now destruct xs; cbn. Qed.


(* Analogous to [removelast_app] *)

Lemma tl_app (A: Type) (xs ys : list A) :
  xs <> nil ->
  tl (xs ++ ys) = tl xs ++ ys.
Proof. destruct xs; cbn; congruence. Qed.

Lemma tl_rev (A: Type) (xs : list A) :
  tl (rev xs) = rev (removelast xs).
Proof.
  induction xs; cbn; auto.
  destruct xs; cbn in *; auto.
  rewrite tl_app; cbn in *.
  - now rewrite IHxs.
  - intros (H1&H2) % app_eq_nil; inv H2.
Qed.

Lemma hd_map (A B: Type) (f: A -> B) (xs : list A) (a : A) :
  hd (f a) (map f xs) = f (hd a xs).
Proof. destruct xs; cbn; auto. Qed.

Lemma hd_app (A: Type) (xs ys : list A) a :
  xs <> nil ->
  hd a (xs ++ ys) = hd a xs.
Proof. intros H. destruct xs; auto. now contradiction H. Qed.

Lemma hd_rev (A: Type) (xs : list A) (a : A) :
  hd a (rev xs) = last xs a.
Proof.
  induction xs; cbn; auto.
  destruct xs; cbn; auto.
  rewrite hd_app. now apply IHxs.
  intros (H1&H2)%app_eq_nil; inv H2.
Qed.

