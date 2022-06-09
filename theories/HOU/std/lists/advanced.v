Require Import List Arith Lia. 
Import ListNotations.
From Undecidability.HOU Require Import std.tactics std.lists.basics std.decidable. 

(* nth *)
Notation nth := nth_error. 
Section Nth.

  Variable (X Y: Type).

  Lemma nth_error_map_option n (f: X -> Y) (A: list X):
    nth_error (map f A) n = option_map f (nth_error A n).
  Proof.
    destruct (nth_error A n) eqn: H1.
    + eapply map_nth_error in H1. rewrite H1. reflexivity.
    + eapply nth_error_None in H1.
      eapply nth_error_None. now rewrite map_length. 
  Qed.



  Lemma nth_error_lt_Some Z m (L: list Z):
    m < length L -> exists a, nth L m = Some a.
  Proof.
    intros H % nth_error_Some.
    destruct nth; intuition. now (exists z).
  Qed.

  Lemma nth_error_Some_lt Z m a (L: list Z):
    nth L m = Some a -> m < length L.
  Proof.
    intros H; eapply nth_error_Some; rewrite H; discriminate. 
  Qed.    

End Nth.


(* nats *)
Section Nats.

  Fixpoint nats (n: nat) :=
    match n with
    | 0 => nil
    | S n => 0 :: map S (nats n)
    end.

  Lemma nats_lt: forall k i, i ∈ nats k -> i < k.
  Proof.
    induction k; cbn; intuition. lia.
    eapply in_map_iff in H0. destruct H0; intuition; subst.
    specialize (IHk x H1); lia.
  Qed.

  Lemma nth_nats m k:
    m < k -> nth (nats k) m = Some m.
  Proof.
    induction k in m |-*.
    - lia.
    - intros; destruct m; cbn in *; eauto.
      erewrite map_nth_error; eauto.
      eapply IHk; lia.
  Qed.
  
  Lemma lt_nats x k:
    x < k -> x ∈ nats k.
  Proof.
    now intros H % nth_nats % nth_error_In. 
  Qed.

  Lemma incl_nats I k:
    I ⊆ nats k -> forall i, i ∈ I -> i < k.
  Proof.
    firstorder using nats_lt.
  Qed.

  Lemma nats_incl I k:
    (forall i, i ∈ I -> i < k) -> I ⊆ nats k.
  Proof.
    firstorder using lt_nats.
  Qed.


  Lemma length_nats k: length (nats k) = k.
  Proof.
    induction k; cbn; lsimpl; congruence.
  Qed.

End Nats.
Global Hint Rewrite length_nats : listdb.



(* tabulate *)
Section Tabulate.
  Implicit Type  X: Type.

  Fixpoint tab {X} (f: nat -> X) k  :=
    match k with
    | 0 => nil
    | S n => tab f n ++ [f n]
    end.
  
  Lemma tab_length X (f: nat -> X) k: length (tab f k) = k.
  Proof.
    induction k; cbn; lsimpl; cbn; lsimpl; lia. 
  Qed.

  Lemma tab_map X Y (f: nat -> X) (g: X -> Y) k:
    map g (tab f k) = tab (fun x => g (f x)) k.
  Proof.
    induction k; cbn; eauto; lsimpl; now rewrite IHk.
  Qed.

  Lemma tab_S X (f: nat -> X) n:
    tab f (S n) = f 0 :: tab (fun k => f (S k)) n.
  Proof.
    induction n; cbn; eauto.
    cbn in *; now rewrite IHn.
  Qed.
   
  Lemma tab_plus X (f: nat -> X) n m:
    tab f (n + m) = tab f n ++ tab (fun k => f (n + k)) m.
  Proof.
    induction n in f |-*; eauto.  
    cbn [plus]; now rewrite tab_S, IHn, tab_S.
  Qed.

  Lemma tab_map_nats X k (f: nat -> X): tab f k = map f (nats k).
  Proof.
    induction k in f |-*; eauto.
    cbn [nats map]; now rewrite tab_S, IHk, map_map.
  Qed.

  Lemma tab_id_nats k: tab id k = nats k.
  Proof.
    rewrite tab_map_nats; now lsimpl. 
  Qed.


  Lemma tab_nth {X} n m (f: nat -> X):
    n < m -> nth (tab f m) n = Some (f n).
  Proof.
    induction 1; cbn.
    + rewrite nth_error_app2, tab_length, Nat.sub_diag; cbn; eauto.
      rewrite tab_length; eauto.
    + rewrite nth_error_app1; eauto.
      now rewrite tab_length. 
  Qed.


  Lemma tab_ext {X} (f g: nat -> X) n: (forall x, f x = g x) -> tab f n = tab g n.
  Proof.
    rewrite !tab_map_nats. intros; now apply map_ext.
  Qed.




End Tabulate.
Global Hint Rewrite tab_length tab_id_nats : listdb. 





(* Repeated *)
Section Repeated.
  Variable (X Y: Type).
  Implicit Types (x y: X) (n m: nat) (f: X -> Y). 

  Lemma repeated_in x n y: y ∈ repeat x n -> x = y.
  Proof.
    induction n; cbn; firstorder.
  Qed.

  Lemma repeated_plus n m x:
    repeat x (n + m) = repeat x n ++ repeat x m.
  Proof.
    induction n; cbn; congruence.
  Qed.
  
  Lemma repeated_rev n x: rev (repeat x n) = repeat x n.
  Proof.
    induction n; cbn; eauto.
    rewrite IHn. change [x] with (repeat x 1).
    rewrite <-repeated_plus.
    rewrite plus_comm. reflexivity.
  Qed.

  Lemma repeated_map n x f:
    map f (repeat x n) = repeat (f x) n.
  Proof.
    induction n; cbn; congruence.
  Qed.
  
  Lemma repeated_length n x: length (repeat x n) = n.
  Proof.
    induction n; cbn; congruence.
  Qed.
  

  Lemma repeated_equal n y A:
    (forall x, x ∈ A -> x = y) -> length A = n -> repeat y n = A.
  Proof.
    induction A in n |-*; destruct n; cbn; eauto; try discriminate.
    injection 2. rewrite IHA; eauto.
    intros. erewrite <-H; intuition.
  Qed.

  Lemma repeated_incl x n A:
    x ∈ A -> repeat x n ⊆ A.
  Proof.
    intros ? ? ? % repeated_in; subst; eauto.
  Qed.

  
  Lemma repeated_tab (x: X) n:
    repeat x n = tab (Basics.const x) n.
  Proof.
    induction n; eauto; cbn [tab].
    replace (S n) with (n + 1) by lia.
    rewrite repeated_plus; cbn.
    rewrite IHn; reflexivity. 
  Qed.



  Lemma nth_error_repeated (x: X) n k :
    k < n -> nth (repeat x n) k = Some x.
  Proof.
    intros H.
    erewrite repeated_tab, tab_map_nats, map_nth_error; eauto.
    now eapply nth_nats.
  Qed.


  Lemma repeated_app_inv n x A B:
    repeat x n = A ++ B ->
    n = length A + length B /\
    A = repeat x (length A) /\
    B = repeat x (length B).
  Proof.
    induction n in A, B |-*.
    - cbn; destruct A, B; try discriminate. intuition.
    - destruct A; cbn; try discriminate.
      + destruct B; try discriminate. 
        injection 1. intuition. cbn; now rewrite <-H0, repeated_length.
        subst. cbn; now rewrite repeated_length.
      + injection 1; intros; edestruct IHn; eauto. 
        intuition. f_equal; eauto. 
  Qed.         

End Repeated.


Global Hint Rewrite  repeated_length repeated_map repeated_plus repeated_rev: listdb.







(* select *)
Section Select.

  Context {X: Type}.

  Fixpoint select (A: list nat) (B: list X)  :=
    match A with
    | nil => nil
    | i :: A => match nth B i with
               | Some x => x :: select A B
               | None => select A B 
               end
    end.
  
  Lemma select_nil I:
    select I nil = nil.
  Proof.
    induction I; cbn.
    - reflexivity.
    - destruct nth eqn: H; eauto.
      eapply nth_error_In in H; cbn in H; intuition.
  Qed.

  Lemma select_S I (x: X) A:
    select (map S I) (x :: A) = select I A.
  Proof.
    induction I.
    - reflexivity.
    - cbn. rewrite IHI. reflexivity. 
  Qed.
  

  Lemma select_nats k A:
    select (nats k) A = firstn k A.
  Proof.
    induction k in A |-*.
    - reflexivity.
    - destruct A.
      + rewrite select_nil; reflexivity.
      + cbn. rewrite select_S, IHk. reflexivity.
  Qed.


  Lemma select_repeated n I x:
    I ⊆ nats n -> select I (repeat x n) = repeat x (length I).
  Proof.
    induction I; cbn; eauto; intros.
    rewrite IHI; eauto with listdb.
    edestruct (nth_error_lt_Some) as [y H']; try rewrite H'.
    eapply nats_lt; lsimpl; firstorder.
    now eapply nth_error_In, repeated_in in H'; subst.
  Qed.

  Lemma select_incl I A: select I A ⊆ A.
  Proof.
    induction I; cbn; intuition.
    destruct nth eqn: H1; intuition.
    eapply nth_error_In in H1. intuition.
  Qed.

  Lemma incl_select A B: A ⊆ B -> exists I, I ⊆ nats (length B) /\ select I B = A.
  Proof.
    induction A.
     + exists nil. lauto.
     + intros; destruct IHA as [I []]; lauto. specialize (H a). mp H; lauto.
        eapply In_nth_error in H as [i].
        exists (i::I). cbn. rewrite H, H1. split; lauto.
        eapply nth_error_Some_lt, lt_nats in H; lauto.
  Qed.
End Select.


Lemma select_map X Y (f: X -> Y) I A:
  map f (select I A) = select I (map f A).
Proof.
  induction I in A |-*; cbn; eauto.
  rewrite nth_error_map_option.
  destruct nth; cbn; now rewrite IHI.
Qed.
    





(* find *)
Section Find.
  
  Context {X: Type}.
  Context {D: Dis X}.

  Fixpoint find (x: X) (A: list X) : option nat :=
    match A with
    | nil => None
    | y :: A => if x == y then Some 0 else option_map S (find x A)
    end.

  Lemma find_Some x A n:
    find x A = Some n -> nth A n = Some x.
  Proof.
    induction A in n |-*; cbn.
    - discriminate.
    - destruct (x == a).
      injection 1; intros; subst. reflexivity.
      destruct find; try discriminate.
      cbn; injection 1; intros; subst.
      cbn. now rewrite IHA.
  Qed.


  Lemma find_in x A:
    x ∈ A -> exists n, find x A = Some n.
  Proof.
    induction A; cbn; intuition.  
    - exists 0. destruct (x == a); subst; intuition.
    - destruct (x == a).
      + subst; exists 0; intuition.
      + destruct H as [m]; exists (S m); intuition.
        rewrite H; reflexivity.
  Qed.

  Lemma find_Some_nth x A n:
    nth A n = Some x -> exists k, find x A = Some k. 
  Proof.
    now intros ? % nth_error_In % find_in. 
  Qed.
      

  Lemma find_not_in x A:
    find x A = None -> ~ x ∈ A.
  Proof.
    intros H [n H'] % find_in; rewrite H in H'; discriminate.
  Qed.


  Lemma find_map f A n x:
    find x A = Some n -> exists m, find (f x) (map f A) = Some m.
  Proof.
    induction A in n |-*; cbn; try discriminate.
    destruct eq_dec; intuition; subst.
    - exists 0; destruct eq_dec; intuition.
    - destruct (find x A); try discriminate.
      edestruct IHA as [m]; eauto.
      destruct eq_dec; eauto.
      exists (S m). now rewrite H0.
  Qed.




End Find.

Lemma find_map_inv X Y {D1: Dis X} {D2: Dis Y} y (f: X -> Y) (A: list X) (n: nat):
  find y (map f A) = Some n -> exists x, f x = y /\ find x A = Some n.
Proof.
  induction A in y, n  |-*; cbn; intuition; try discriminate.
  destruct eq_dec.
  + injection H as ?; subst; exists a; intuition. destruct eq_dec; intuition.
  + destruct find eqn: H1; try discriminate. injection H as ?; subst.
    eapply IHA in H1 as []; intuition; subst.
    exists x. intuition; destruct eq_dec; cbn; try congruence. now rewrite H1.
Qed.

Section Remove.

  Variable (X: Type) (D: Dis X).

  Lemma remove_remain  (x y: X) A:
    x ∈ A -> x <> y -> x ∈ remove eq_dec y A.
  Proof.
    induction A; cbn; intuition; subst.
    - destruct (y == x); subst; intuition.
    - destruct (y == a); subst; intuition.
  Qed.


  Lemma remove_prev (x y: X) (A: list X):
    y ∈ remove eq_dec x A -> y ∈ A.
  Proof.
    induction A; intuition.
    cbn in H. destruct (x == a); subst; intuition.
    cbn in *; intuition.
  Qed.

End Remove.


Section FlatMap.

  Variable (X Y: Type).
  Implicit Types (A B: list X) (f: X -> list Y).

  Lemma flat_map_app f A B:
    flat_map f (A ++ B) = flat_map f A ++ flat_map f B.
  Proof.
    induction A; cbn; eauto; now rewrite IHA, app_assoc.
  Qed.

  Lemma flat_map_incl (f: X -> list Y) A B:
    A ⊆ B -> flat_map f A ⊆ flat_map f B.
  Proof.
    intros H x [y []] % in_flat_map.
    eapply in_flat_map; exists y; intuition.
  Qed.

  Lemma flat_map_in_incl f a A:
    a ∈ A -> f a ⊆ flat_map f A.
  Proof.
    revert A; eapply in_ind; cbn; intuition.
  Qed.

End FlatMap.
