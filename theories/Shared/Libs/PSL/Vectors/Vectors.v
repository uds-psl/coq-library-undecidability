(* * Addendum for Vectors ([Vector.t]) *)
(* Author: Maximilian Wuttke *)


From Undecidability.Shared.Libs.PSL Require Import Prelim Tactics.Tactics EqDec.
From Coq.Vectors Require Import Fin Vector.
From Undecidability.Shared.Libs.PSL Require Import Vectors.FinNotation.
From Undecidability.Shared.Libs.PSL Require Export Vectors.Fin.

(* Vector.nth should not reduce with simpl, except the index is given with a constructor *)
Arguments Vector.nth {A} {m} (v') !p. 
Arguments Vector.map {A B} f {n} !v. 
Arguments Vector.map2 {A B C} g {n} !v1 !v2.

Delimit Scope vector_scope with vector.
Local Open Scope vector.

Module VectorNotations2.

Notation "[ | | ]" := (nil _) (format "[ |  | ]"): vector_scope.
Notation "h ':::' t" := (cons _ h _ t) (at level 60, right associativity) : vector_scope.

Notation "[ | x | ]" := (x ::: [| |]) : vector_scope.
Notation "[ | x ; y ; .. ; z | ] " := (cons _ x _ (cons _ y _ .. (cons _ z _ (nil _)) ..))
   (format "[ | x ;  y ;  .. ;  z | ] ") : vector_scope.
Notation "v [@ p ]" := (nth v p) (at level 1, format "v [@ p ]") : vector_scope.

End VectorNotations2.

Import VectorNotations2.



Ltac existT_eq :=
  match goal with
  | [ H: existT ?X1 ?Y1 ?Z1 = existT ?X2 ?Y2 ?Z2 |- _] =>
    apply EqdepFacts.eq_sigT_iff_eq_dep in H; inv H
  end.

Ltac existT_eq' :=
  match goal with
  | [ H: existT ?X1 ?Y1 ?Z1 = existT ?X2 ?Y2 ?Z2 |- _] =>
    apply EqdepFacts.eq_sigT_iff_eq_dep in H; induction H
  end.



Lemma destruct_vector_nil (X : Type) :
  forall v : Vector.t X 0, v = [| |].
Proof.
  now apply case0.
Qed.

Lemma destruct_vector_cons (X : Type) (n : nat) :
  forall v : Vector.t X (S n), { h : X & { v' : Vector.t X n | v = h ::: v' }}.
Proof.
  revert n. apply caseS. eauto.
Qed.


Lemma In_nil (X : Type) (x : X) :
  ~ In x [| |].
Proof. intros H. inv H. Qed.

Lemma In_cons (X : Type) (n : nat) (x y : X) (xs : Vector.t X n) :
  In y (x ::: xs) -> x = y \/ In y xs.
Proof.
  intros H. inv H; existT_eq'; tauto.
Qed.

Ltac destruct_vector_in :=
  lazymatch goal with
  | [ H: Vector.In _ [| |] |- _ ] => solve [exfalso;simple apply In_nil in H;exact H]
  | [ H: Vector.In _ (?x ::: _) |- _ ] => simple apply In_cons in H as [H| H] ; try (is_var x;move H at bottom;subst x) 
  end.

Section In_Dec.
  Variable X : Type.
  Hypothesis X_dec : eq_dec X.

  Fixpoint in_dec (n : nat) (x : X) (xs : Vector.t X n) { struct xs } : bool :=
    match xs with
    | [| |] => false
    | y ::: xs' => if Dec (x = y) then true else in_dec x xs'
    end.

  Lemma in_dec_correct (n : nat) (x : X) (xs : Vector.t X n) :
    in_dec x xs = true <-> In x xs.
  Proof.
    split; intros.
    {
      induction xs; cbn in *.
      - congruence.
      - decide (x = h) as [ -> | D].
        + constructor.
        + constructor. now apply IHxs.
    }
    {
      induction H; cbn.
      - have (x = x).
      - decide (x = x0).
        + reflexivity.
        + apply IHIn.
    }
  Qed.

  Global Instance In_dec (n : nat) (x : X) (xs : Vector.t X n) : dec (In x xs).
  Proof using X_dec. eapply dec_transfer. eapply in_dec_correct. auto. Defined.

End In_Dec.

  

(* Destruct a vector of known size *)
Ltac destruct_vector :=
  repeat match goal with
         | [ v : Vector.t ?X 0 |- _ ] =>
           let H  := fresh "Hvect" in
           pose proof (@destruct_vector_nil X v) as H;
           subst v
         | [ v : Vector.t ?X (S ?n) |- _ ] =>
           let h  := fresh "h" in
           let v' := fresh "v'" in
           let H  := fresh "Hvect" in
           pose proof (@destruct_vector_cons X n v) as (h&v'&H);
           subst v; rename v' into v
         end.

Section tabulate_vec.
  Variable X : Type.

  Fixpoint tabulate (n : nat) (f : Fin.t n -> X) {struct n} : Vector.t X n.
  Proof.
    destruct n.
    - apply Vector.nil.
    - apply Vector.cons.
      + apply f, Fin.F1.
      + apply tabulate. intros m. apply f, Fin.FS, m.
  Defined.

  Lemma nth_tabulate n (f : Fin.t n -> X) (m : Fin.t n) :
    Vector.nth (tabulate f) m = f m.
  Proof.
    induction m.
    - cbn. reflexivity.
    - cbn. rewrite IHm. reflexivity.
  Qed.

  Lemma in_tabulate n (f : Fin.t n -> X) (x : X) :
    In x (tabulate (n := n) f) <-> exists i : Fin.t n, x = f i.
  Proof.
    split.
    {
      revert f x. induction n; intros f x H.
      - cbn in *. inv H.
      - cbn in *. apply In_cons in H as [ <- | H ].
        + eauto.
        + specialize (IHn (fun m => f (Fin.FS m)) _ H) as (i&IH). eauto.
    }
    {
      intros (i&Hi). induction i; cbn in *; subst; econstructor; eauto.
    }
  Qed.

End tabulate_vec.

Lemma Vector_map_tabulate {X Y n} (f : X -> Y) g :
  Vector.map (n:=n) f (tabulate g) = tabulate (fun x => f (g x)).
Proof.
induction n; cbn.
- reflexivity.
- f_equal. eapply IHn.
Qed.


#[global]
Instance Vector_eq_dec n A: eq_dec A -> eq_dec (Vector.t A n).
Proof.
  intros H x y. eapply VectorEq.eq_dec with (A_beq := fun x y => proj1_sig (Sumbool.bool_of_sumbool (H x y))).
  intros ? ?. destruct (Sumbool.bool_of_sumbool).
  cbn.  destruct x1;intuition.
Defined.

#[global]
Instance Fin_eq_dec n : eq_dec (Fin.t n).
Proof.
  intros; hnf.
  destruct (Fin.eqb x y) eqn:E.
  - left. now eapply Fin.eqb_eq.
  - right. intros H. eapply Fin.eqb_eq in H. congruence.
Defined.


Import VectorNotations.
Lemma Vector_map_app {X Y k1 k2} (v1 : Vector.t X k1) (v2 : Vector.t X k2) (f : X -> Y) :
  Vector.map f (v1 ++ v2)%vector = Vector.map f v1 ++ Vector.map f v2.
Proof.
  induction v1; cbn; congruence.
Qed.

(* Conversion between vectors and lists *)
Module VecToListCoercion.
  Coercion Vector.to_list : Vector.t >-> list.
End VecToListCoercion.

Arguments Vector.eqb {_}  _ {_ _}.

Lemma vector_eqb_spec X n eqb:
  (forall (x1 x2 : X) , reflect (x1 = x2) (eqb x1 x2))
  -> forall x y , reflect (x=y) (Vector.eqb (n:=n) eqb x y).
Proof with try (constructor;congruence).
  intros Hf x y.
  apply iff_reflect. symmetry. apply Vector.eqb_eq. symmetry. apply reflect_iff. eauto.
Qed.
