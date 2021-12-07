(* * Forall operations on ttors *)

Require Import Vector Lia.
Require Import Undecidability.Shared.Dec.
From Undecidability.Shared.Libs.PSL Require Import Vectors.


Definition Forall {X} (p : X -> Prop) := fix Forall {n} (v : t X n) :=
  match v with
  | nil _ => True
  | cons _ x _ v => p x /\ Forall v
  end.

Definition ForallT {X} (p : X -> Type) := fix ForallT {n} (v : t X n) :=
  match v with
  | nil _ => (unit : Type)
  | cons _ x _ v => (p x * ForallT v)%type
  end.

Definition Forall2 {X Y} (p : X -> Y -> Prop) := fix Forall2 {n} (v1 : t X n) (v2 : t Y n) :=
  match v1 in Vector.t _ n return t Y n -> Prop with
  | nil _ => fun _ => True
  | cons _ x _ v1 => fun v2 => p x (hd v2) /\ Forall2 v1 (tl v2)
  end v2.

Lemma Forall2_Forall {X Y Z n} (p : Y -> Z -> Prop) (f1 : X -> Y) (f2 : X -> Z) v :
  @Forall2 Y Z p n (map f1 v) (map f2 v) <-> @Forall X (fun x => p (f1 x) (f2 x)) n v.
Proof.
  induction v; firstorder.
Qed.

Lemma Forall2_identical {X n} (v : t X n) (p : X -> X -> Prop) :
  Forall2 p v v <-> Forall (fun x => p x x) v.
Proof.
  induction v; firstorder.
Qed.

Lemma Forall2_move_forall {X Y Z n} (v1 : t X n) (v2 : t Y n) (p : X -> Y -> Z -> Prop) :
  Forall2 (fun x y => forall z, p x y z) v1 v2 <-> forall z, Forall2 (fun x y => p x y z) v1 v2.
Proof.
  induction v1; dependent destruct v2; firstorder. apply IHv1, H.
Qed.

Lemma Forall2_eq {X n} (v1 : t X n) (v2 : t X n) :
  Forall2 eq v1 v2 -> v1 = v2.
Proof.
  induction v1; dependent destruct v2. reflexivity. f_equal; firstorder.
Qed.

Lemma Forall_ext {X n} (p q : X -> Prop) (v : t X n) :
  (forall x, p x -> q x) -> Forall p v -> Forall q v.
Proof.
  induction v; firstorder.
Qed.

Lemma Forall_ext_Forall {X n} (p q : X -> Prop) (v : t X n) :
  Forall (fun x => p x -> q x) v -> Forall p v -> Forall q v.
Proof.
  induction v; firstorder.
Qed.

Lemma Forall_ext_in {X n} (p q : X -> Prop) (v : t X n) :
  (forall x, In x v -> p x -> q x) -> Forall p v -> Forall q v.
Proof.
  intros H1 H2. induction v; cbn. easy. split. apply H1. constructor.
  apply H2. apply IHv. intros x H3. apply H1. now constructor. apply H2.
Qed.

Lemma Forall_in {X n} (p : X -> Prop) (v : t X n) :
  Forall p v <-> forall x, In x v -> p x.
Proof.
  induction v. easy. split. intros H1 x H. destruct_vector_in; firstorder.
  intros H. split. apply H. constructor. apply IHv. intros x H1. apply H. now constructor.
Qed.

Lemma Forall_map {X Y n} (p : Y -> Prop) (f : X -> Y) (v : t X n) :
  Forall p (map f v) <-> Forall (fun x => p (f x)) v.
Proof.
  induction v; firstorder.
Qed.

Lemma Forall_dec {X n}  (p : X -> Prop) (v : t X n) :
  ForallT (fun x => dec (p x)) v -> dec (Forall p v).
Proof.
  induction v; firstorder.
Qed.

Lemma ForallT_translate {X Y n} (p : X -> Y -> Prop) (v : t X n) :
  ForallT (fun x => { x' | p x x' }) v -> { v' : t Y n | Forall2 p v v'}.
Proof.
  intros H. induction v.
  - now exists (nil _).
  - destruct H as [[x' H1] H2]. destruct IHv as [v' IHv]. easy. 
    now exists (cons _ x' _ v').
Qed.

Lemma ForallT_ext {X n} (p q : X -> Type) (v : t X n) :
  (forall x, p x -> q x) -> ForallT p v -> ForallT q v.
Proof.
  induction v; firstorder.
Qed.

Lemma ForallT_general {X n} (p : X -> Type) (v : t X n) :
  (forall x, p x) -> ForallT p v.
Proof.
  induction v; firstorder.
Qed.

Lemma map_ext_forall {X Y n} (f g : X -> Y) (v : t X n):
  Forall (fun x => f x = g x) v -> map f v = map g v.
Proof.
  induction v; cbn. reflexivity. intros. f_equal; firstorder.
Qed.

Lemma map_ext_forall2 {X Y Z : Type} {n} (v : t X n) (v' : t Y n) (f : X -> Z) (g : Y -> Z) :
  Forall2 (fun x x' => f x = g x') v v' -> map f v = map g v'.
Proof.
  induction v; dependent destruct v'; cbn.
  - reflexivity.
  - f_equal. apply H. apply IHv. apply H.
Qed.
