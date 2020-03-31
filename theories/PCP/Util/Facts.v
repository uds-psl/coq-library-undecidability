Require Import List Lia.
Import ListNotations.

Require Import Undecidability.PCP.PCP.

Set Implicit Arguments. 
Unset Strict Implicit.

Notation "x 'el' A" := (In x A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).
Notation "| A |" := (length A) (at level 65).

Ltac inv H := inversion H; subst; try clear H.

(** *Some basic things concerning lists *)

Lemma list_prefix_inv X (a : X) x u y v :
  ~ a el x -> ~ a el u -> x ++ a :: y = u ++ a :: v -> x = u /\ y = v.
Proof.
  intro. revert u.
  induction x; intros; destruct u; inv H1; try now firstorder.
    eapply IHx in H4; try now firstorder. intuition congruence.
Qed.

Lemma split_inv X (u z x y : list X) (s : X) :
  u ++ z = x ++ s :: y -> ~ s el u -> exists x' : list X, x = u ++ x'.
Proof.
  revert u. induction x; cbn; intros.
  - destruct u. cbn. eauto. inv H. firstorder.
  - destruct u. cbn. eauto. 
    inv H. edestruct IHx. cbn. rewrite H3. reflexivity. firstorder. subst. cbn. eauto.
Qed.

Lemma in_split X (a : X) (x : list X) :
  a el x -> exists y z, x = y ++ [a] ++ z.
Proof.
  induction x; cbn; intros.
  - firstorder.
  - destruct H as [-> | ].
    + now exists [], x.
    + destruct (IHx H) as (y & z & ->).
      now exists (a0 :: y), z.
Qed.

Definition is_cons X (l : list X) :=
  match l with
  | [] => false
  | _ => true
  end.

Lemma is_cons_true_iff X (l : list X) :
  is_cons l = true <-> l <> [].
Proof.
  destruct l; cbn; firstorder congruence.
Qed.


(** *** Fresh symbols *)

Fixpoint fresh (l : list nat) :=
  match l with
  | [] => 0
  | x :: l => S x + fresh l
  end.

Lemma fresh_spec' l a : a el l -> a < fresh l.
Proof.
  induction l.
  - firstorder.
  - cbn; intros [ | ]; firstorder lia.
Qed.

Lemma fresh_spec (a : nat) (l : list nat) : a el l -> fresh l <> a.
Proof.
  intros H % fresh_spec'. intros <-. lia.
Qed.

Section neList.

  Variable X : Type.
  Variable P : list X -> Prop.

  Hypothesis B : (forall x : X, P [x]).
  Hypothesis S : (forall x A, P A -> P (x :: A)).
  
  Lemma list_ind_ne A : A <> [] -> P A.
  Proof.
    intros H. destruct A. congruence. clear H.
    revert x. induction A; eauto.
  Qed.

End neList.

Fixpoint omap X Y (f : X -> option Y) l :=
  match l with
  | nil => nil
  | x :: l => match f x with Some y => y :: omap f l | None => omap f l end
  end.

Lemma in_omap_iff X Y (f : X -> option Y) l y : y el omap f l <-> exists x, x el l /\ f x = Some y.
Proof.
  induction l; cbn.
  - firstorder.
  - destruct (f a) eqn:E; firstorder (subst; firstorder congruence).
Qed.

Section Positions.
  Variables (X: Type) (d: forall x y : X, {x = y} + {x <> y}).
  Implicit Types (x y: X) (A B : list X).

  Fixpoint pos x A : option nat :=
    match A with
    | nil => None
    | y :: A' => if d x y then Some 0
                else match pos x A' with
                     | Some n => Some (S n)
                     | None => None
                     end
    end.

  Lemma el_pos x A :
    x el A -> { n | pos x A = Some n }.
  Proof.
    induction A as [|y A IH]; cbn; intros H.
    - destruct H as [].
    - destruct (d x y) as [<-|H1].
      + now exists 0.
      + destruct IH as [n IH].
        * destruct H as [->|H]; tauto.
        * rewrite IH. now exists (S n).
  Qed.

  Notation nthe n A := (nth_error A n).
  
  Lemma nthe_length A n :
    length A > n -> { x | nthe n A = Some x }.
  Proof.
    revert n.
    induction A as [|y A IH]; cbn; intros n H.
    - exfalso. lia.
    - destruct n as [|n]; cbn.
      + now exists y.
      + destruct (IH n) as [x H1]. lia. now exists x.
  Qed.
  
 Lemma pos_nthe x A n :
    pos x A = Some n -> nthe n A = Some x.
 Proof.
   revert n.
   induction A as [|y A IH]; cbn; intros n.
    - intros [=].
    - destruct (d x y) as [<-|H1].
      + now intros [= <-].
      + destruct (pos x A) as [k|]; intros [= <-]; cbn.
        now apply IH.
  Qed.
  
  Lemma nthe_app_l x n A B :
    nthe n A = Some x -> nthe n (A ++ B) = Some x.
  Proof.
    revert n.
    induction A as [|y A IH]; cbn; intros k H.
    - destruct k; discriminate H.
    - destruct k as [|k]; cbn in *. exact H.
      apply IH, H.
  Qed.

End Positions.

Notation nthe n A := (nth_error A n).

Lemma pos_nth X d (x : X) l n def : pos d x l = Some n -> nth n l def = x.
Proof.
  revert n; induction l; cbn; intros; try congruence.
  destruct (d x a); try destruct (pos d x l) eqn:E; inv H; eauto.
Qed.

Lemma pos_length X d (x : X) l n : pos d x l = Some n -> n < | l |.
Proof.
  revert n; induction l; cbn; intros; try congruence.
  destruct (d x a).
  - inv H. lia.
  - destruct (pos d x l) eqn:E; inv H; try lia. specialize (IHl _ eq_refl). lia.
Qed.

Lemma cons_incl X (a : X) (A B : list X) : a :: A <<= B -> A <<= B.
Proof.
  intros ? ? ?. eapply H. firstorder.
Qed.

Lemma app_incl_l X (A B C : list X) :
  A ++ B <<= C -> A <<= C.
Proof.
  intros H x Hx. eapply H. eapply in_app_iff. now left.
Qed.

Lemma app_incl_R X (A B C : list X) :
  A ++ B <<= C -> B <<= C.
Proof.
  intros H x Hx. eapply H. eapply in_app_iff. now right.
Qed.
