(* ** Vectors *)

(* This file defines operations on vectors and proves corresponding facts. *)

Require Import Undecidability.Shared.Dec.
Require Import Vector Lia.
Definition vec := t.

From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.

Definition Forall {X} (p : X -> Prop) := fix Forall {n} (v : vec X n) :=
  match v with
  | nil _ => True
  | cons _ x _ v => p x /\ Forall v
  end.

Definition ForallT {X} (p : X -> Type) := fix ForallT {n} (v : vec X n) :=
  match v with
  | nil _ => (unit : Type)
  | cons _ x _ v => (p x * ForallT v)%type
  end.

Definition Forall2 {X Y} (p : X -> Y -> Prop) := fix Forall2 {n} (v1 : vec X n) (v2 : vec Y n) :=
  match v1 in Vector.t _ n return vec Y n -> Prop with
  | nil _ => fun _ => True
  | cons _ x _ v1 => fun v2 => p x (hd v2) /\ Forall2 v1 (tl v2)
  end v2.

Fixpoint Forall2T {X Y n} (p : X -> Y -> Type) (v1 : vec X n) (v2 : vec Y n) :=
  match v1 in Vector.t _ n return vec Y n -> Type with
  | nil _ => fun _ => True
  | cons _ x _ v1 => fun v2 => (p x (hd v2) * Forall2T p v1 (tl v2))%type
  end v2.

Definition Any {X} (p : X -> Prop) := fix Forall {n} (v : vec X n) :=
  match v with
  | nil _ => False
  | cons _ x _ v => p x \/ Forall v
  end.

Fixpoint In {X n} x (v : vec X n) :=
  match v with
  | nil _ => False
  | cons _ y _ v => x = y \/ In x v
  end.


Lemma Forall2_Forall {X Y Z n} (p : Y -> Z -> Prop) (f1 : X -> Y) (f2 : X -> Z) v :
  @Forall2 Y Z p n (map f1 v) (map f2 v) <-> @Forall X (fun x => p (f1 x) (f2 x)) n v.
Proof.
  induction v; firstorder.
Qed.

Lemma Forall2_identical {X n} (v : vec X n) (p : X -> X -> Prop) :
  Forall2 p v v <-> Forall (fun x => p x x) v.
Proof.
  induction v; firstorder.
Qed.

Lemma Forall2_move_forall {X Y Z n} (v1 : vec X n) (v2 : vec Y n) (p : X -> Y -> Z -> Prop) :
  Forall2 (fun x y => forall z, p x y z) v1 v2 <-> forall z, Forall2 (fun x y => p x y z) v1 v2.
Proof.
  induction v1; dependent elimination v2; firstorder. apply IHv1, H.
Qed.

Lemma Forall2_eq {X n} (v1 : vec X n) (v2 : vec X n) :
  Forall2 eq v1 v2 -> v1 = v2.
Proof.
  induction v1; dependent elimination v2; intros H. reflexivity. f_equal; firstorder.
Qed.

Lemma Forall_ext {X n} (p q : X -> Prop) (v : vec X n) :
  (forall x, p x -> q x) -> Forall p v -> Forall q v.
Proof.
  induction v; firstorder.
Qed.

Lemma Forall_ext_Forall {X n} (p q : X -> Prop) (v : vec X n) :
  Forall (fun x => p x -> q x) v -> Forall p v -> Forall q v.
Proof.
  induction v; firstorder.
Qed.

Lemma Forall_ext_in {X n} (p q : X -> Prop) (v : vec X n) :
  (forall x, In x v -> p x -> q x) -> Forall p v -> Forall q v.
Proof.
  induction v; firstorder.
Qed.

Lemma Forall_in {X n} (p : X -> Prop) (v : vec X n) :
  Forall p v <-> forall x, In x v -> p x.
Proof.
  induction v. easy. split. intros H1 x [->|H2]; firstorder. firstorder.
Qed.

Lemma Forall_map {X Y n} (p : Y -> Prop) (f : X -> Y) (v : vec X n) :
  Forall p (map f v) <-> Forall (fun x => p (f x)) v.
Proof.
  induction v; firstorder.
Qed.

Require Import Decidable.

Lemma Forall_dec {X n}  (p : X -> Prop) (v : vec X n) :
  ForallT (fun x => dec (p x)) v -> dec (Forall p v).
Proof.
  induction v; firstorder.
Qed.

Lemma ForallT_translate {X Y n} (p : X -> Y -> Prop) (v : vec X n) :
  ForallT (fun x => { x' | p x x' }) v -> { v' : vec Y n | Forall2 p v v'}.
Proof.
  intros H. induction v.
  - now exists (nil _).
  - destruct H as [[x' H1] H2]. destruct IHv as [v' IHv]. easy. 
    now exists (cons _ x' _ v').
Qed.

Lemma ForallT_ext {X n} (p q : X -> Type) (v : vec X n) :
  (forall x, p x -> q x) -> ForallT p v -> ForallT q v.
Proof.
  induction v; firstorder.
Qed.

Lemma ForallT_general {X n} (p : X -> Type) (v : vec X n) :
  (forall x, p x) -> ForallT p v.
Proof.
  induction v; firstorder.
Qed.

Lemma map_ext {X Y Z : Type} {n} (v : vec X n) (v' : vec Y n) (f : X -> Z) (g : Y -> Z) :
  Forall2 (fun x x' => f x = g x') v v' -> map f v = map g v'.
Proof.
  induction v; dependent elimination v'; cbn; intros H.
  - reflexivity.
  - f_equal. apply H. now apply IHv.
Qed.

Lemma map_ext_in {X Y n} (f g : X -> Y) (v : vec X n):
  (forall x, In x v -> f x = g x) -> map f v = map g v.
Proof.
  induction v; cbn. reflexivity. intros. f_equal; firstorder.
Qed.

Lemma map_ext_forall {X Y n} (f g : X -> Y) (v : vec X n):
  Forall (fun x => f x = g x) v -> map f v = map g v.
Proof.
  induction v; cbn. reflexivity. intros. f_equal; firstorder.
Qed.

Lemma In_map {X Y n} (f : X -> Y) (v : vec X n) x :
  In x v -> In (f x) (map f v).
Proof.
  intros H. induction v; cbn. easy. destruct H as [->|]. now left. right. now apply IHv.
Qed.

Lemma In_map_iff {X Y n} (f : X -> Y) (v : vec X n) y :
  In y (map f v) <-> exists x, f x = y /\ In x v.
Proof.
  induction v; cbn.
  - split. easy. now intros [].
  - split.
    + intros [->|]. exists h. split. easy. now left. apply IHv in H as [x H]. exists x.
      split. apply H. now right.
    + intros [x [<- [->|]]]. now left. right. apply IHv. now exists x.
Qed.

Lemma In_compat {X n} x (v : vec X n) :
  In x v <-> Vector.In x v.
Proof.
  induction v; cbn.
  - split. easy. intros H. inversion H.
  - split. intros [->|]; constructor. now apply IHv. intros H.
    inversion H. now left. right. apply Eqdep_dec.inj_pair2_eq_dec in H3 as ->. now apply IHv.
    decide equality.
Qed. 


Fixpoint tabulate {X} n (f : nat -> X) : vec X n :=
  match n with
  | 0 => Vector.nil X
  | S n => Vector.cons _ (f n) _ (tabulate n f)
  end.

Fixpoint fold_left {X Y} (f: X -> Y -> Y) y {n} (v : vec X n) : Y := 
  match v with
  | Vector.nil _ => y
  | Vector.cons _ x _ v => fold_left f (f x y) v
  end.

Fixpoint fold_two_left {X Y} (f: X -> Y -> Y) y {n} (v1 v2 : vec X n) : Y := 
  match v1 in Vector.t _ n return vec X n -> Y with
  | Vector.nil _ => fun _ => y
  | Vector.cons _ x _ v1 =>  fun v2 => fold_two_left f (f (hd v2) (f x y)) v1 (tl v2)
  end v2.

Fixpoint nth_error {X m} n (v : vec X m) err := match v with
  | Vector.nil _ => err
  | Vector.cons _ x _ v => match n with 0 => x | S n => nth_error n v err end
end.


Lemma map_tabulate {X Y} n (f : X -> Y) (g : nat -> X) :
  map f (tabulate n g) = tabulate n (fun x => f (g x)).
Proof.
  induction n; cbn; congruence.
Qed.

Lemma tabulate_ext {X} n (f : nat -> X) (g : nat -> X) :
  (forall m, m < n -> f m = g m) -> tabulate n f = tabulate n g.
Proof.
  intros H. induction n; cbn. reflexivity. f_equal. apply H. lia.
  apply IHn. intros m H'. apply H. lia.
Qed.

Lemma tabulate_nth {X n} (v : vec X n) err :
  tabulate n (fun x => nth_error (n-S x) v err) = v.
Proof.
  induction v; cbn. reflexivity. f_equal. now replace (n-n) with 0 by lia.
  rewrite <- IHv at 1. apply tabulate_ext. intros x H. now replace (n - x) with (S (n - S x)) by lia.
Qed.

Lemma tabulate_Forall {X n} (f : nat -> X) (p : X -> Prop) :
  Forall p (tabulate n f) <-> forall x, x < n -> p (f x).
Proof.
  induction n; cbn.
  - split; intros; lia.
  - split.
    + intros [] x ?. assert (x = n \/ x < n) as [->|] by lia. easy. now apply IHn.
    + intros H. split. apply H. lia. apply IHn. intros ? ?. apply H. lia.
Qed.

Lemma nth_tabulate {X} n m (f : nat -> X) err :
  m < n -> nth_error m (tabulate n f) err = f (n-S m).
Proof.
  revert m. induction n; intros m; cbn -[minus].
  - lia.
  - intros H. destruct m; cbn. f_equal; lia. apply IHn. lia.
Qed.
