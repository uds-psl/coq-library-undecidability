Require Import PslBase.Base PslBase.FiniteTypes Undecidability.TM.Prelim.
Require Import PslBase.Vectors.Vectors.

(** * Relations *)

Definition Rel (X : Type) (Y : Type) := X -> Y -> Prop.

Definition rcomp X Y Z (R : Rel X Y) (S : Rel Y Z) : Rel X Z :=
  fun x z => exists y, R x y /\ S y z.
Notation "R1 '∘' R2" := (rcomp R1 R2) (at level 40, left associativity).
Arguments rcomp {X Y Z} (R S) x y /.

Definition runion X Y (R : Rel X Y) (S : Rel X Y) : Rel X Y := fun x y => R x y \/ S x y.
Notation "R '∪' S" := (runion R S) (at level 42).
Arguments runion { X Y } ( R S ) x y /.

Definition rintersection X Y (R : Rel X Y) (S : Rel X Y) : Rel X Y := fun x y => R x y /\ S x y.
Notation "R '∩' S" := (rintersection R S) (at level 41).
Arguments rintersection { X Y } ( R S ) x y /.


Definition rimplication X Y (R : Rel X Y) (S : Rel X Y) : Rel X Y := fun x y => R x y -> S x y.
Notation "R '⊂' S" := (rimplication R S) (at level 41).
Arguments rimplication { X Y } ( R S ) x y /.

Definition ignoreParam X Y Z (R : Rel X Z) : Rel X (Y * Z)  := fun x '(y,z) => R x z.
Arguments ignoreParam {X Y Z} ( R ) x y /.

Definition rUnion (X Y : Type) (F : Type) (R : F -> Rel X Y) : Rel X Y := 
  fun x y => exists f, R f x y.
Notation "'⋃_' f R" := (rUnion (fun f => R)) (at level 50, f at level 9, R at next level, format "'⋃_' f  R"). (* Todo: This does not work if f is higher than 9. Why? *)
Arguments rUnion { X Y F } ( R ) x y /.

Definition rIntersection (X Y : Type) (F : Type) (R : F -> Rel X Y) : Rel X Y := 
  fun x y => forall f, R f x y.
Notation "'⋂_' f R" := (rIntersection (fun f => R)) (at level 50, f at level 9, R at next level, format "'⋂_' f  R"). (* Todo: This does not work if f is higher than 9. Why? *)
Arguments rIntersection { X Y F } ( R ) x y /.


Definition surjective X Z (R : Rel X Z) :=
  forall x, exists y, R x y.

Definition functional X Z (R : Rel X Z) :=
  forall x z1 z2, R x z1 -> R x z2 -> z1 = z2.

Definition subrel X Y (R S: Rel X Y) := (forall x y, R x y -> S x y).
Notation "R1 <<=2 R2" := (subrel R1 R2) (at level 60).

Instance eqrel_pre X Y : PreOrder (subrel (X := X) (Y := Y)).
Proof. constructor; firstorder. Qed.

Fact subrel_and X Y (R1 R2 R3 : Rel X Y) :
  R1 <<=2 R3 \/ R2 <<=2 R3 -> R1 ∩ R2 <<=2 R3.
Proof. firstorder. Qed.

Fact subrel_or X Y (R1 R2 R3 : Rel X Y) :
  R1 <<=2 R3 /\ R2 <<=2 R3 -> R1 ∪ R2 <<=2 R3.
Proof. firstorder. Qed.

Fact subrel_and2 X Y (R1 R2 R3 R4 : Rel X Y) :
  R1 <<=2 R3 /\ R2 <<=2 R4 -> R1 ∩ R2 <<=2 R3 ∩ R4.
Proof. firstorder. Qed.

Fact subrel_or2 X Y (R1 R2 R3 R4 : Rel X Y) :
  R1 <<=2 R3 /\ R2 <<=2 R4 -> R1 ∪ R2 <<=2 R3 ∪ R4.
Proof. firstorder. Qed.

Definition eqrel X Y (R S: Rel X Y) := (R <<=2 S /\ S <<=2 R) .

Notation "R '=2' S"  := (eqrel R S) (at level 70).

Instance eqrel_eq X Y : Equivalence (eqrel (X := X) (Y := Y)).
Proof. constructor; firstorder. Qed.

(** ** Relational operators on labelled relations *)

(** Restrict the label of a labelled relation and return an unlabelled relation *)
Definition restrict X Y Z (R : Rel X (Y * Z)) f : Rel X Z := (fun x1 x2 => R x1 (f, x2)).
Notation "R '|_' f" := (restrict R f) (at level 30, format "R '|_' f").
Arguments restrict { X Y Z } ( R f ) x y /.

(** Introduce a label that is fixed to a value *)
Definition rfix X Y Z (R : Rel X Z) (p : Y) : Rel X (Y*Z) := (fun x '(y, z) =>
y = p /\ R x z).
Notation "R '||_' f" := (rfix R f) (at level 30, format "R '||_' f").
Arguments rfix { X Y Z } ( R p ) x y /.


(** ** Relations over Vectors *)

Section Fix_X2.
  Variable X Y Z : Type.
  Variable n : nat.

  Local Notation "'V' Z" := (Vector.t Z n) (at level 10).

  Definition Eq_in (f : Fin.t n -> Prop) : Rel (V X) (V X) :=
    fun vx vy => forall i : Fin.t n, f i -> vy[@i] = vx[@i].

  Global Instance Eq_in_equivalence (f : Fin.t n -> Prop) :
    Equivalence (@Eq_in f).
  Proof.
    econstructor.
    - econstructor.
    - hnf. intros. hnf in *. intros. rewrite <- H; eauto.
    - hnf. intros. hnf in *. intros. rewrite <- H, <- H0; eauto.
  Qed.

End Fix_X2.

Arguments Eq_in { X n } P x y / : rename.


(** ** Reflexive transitive closure and relational power *)
Section Star_Pow.
  Variable X : Type.
  Variable R : Rel X X.

  Inductive pow : nat -> Rel X X :=
  | pow_0 x : pow 0 x x
  | pow_S k x y z : R x y -> pow k y z -> pow (S k) x z.

  Inductive star : Rel X X :=
  | starR x : star x x
  | starC x y z : R x y -> star y z -> star x z.

  Lemma star_trans : transitive _ star.
  Proof. induction 1; eauto using star. Qed.

  Global Instance star_preorder : PreOrder star.
  Proof. constructor. constructor. apply star_trans. Qed.

  Lemma pow_plus k1 k2 x y z :
    pow k1 x y -> pow k2 y z -> pow (k1 + k2) x z.
  Proof. induction 1; cbn; eauto using pow. Qed.

  Lemma star_pow x y :
    star x y <-> exists n, pow n x y.
  Proof.
    split.
    - induction 1; firstorder eauto using pow.
    - intros (n&H). induction H; eauto using star.
  Qed.

End Star_Pow.
