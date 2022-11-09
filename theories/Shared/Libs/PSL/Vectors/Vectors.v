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

Tactic Notation "dependent" "destruct" constr(V) :=
  match type of V with
  | Vector.t ?Z (S ?n) =>
    revert all except V;
    pattern V; revert n V;
    eapply caseS; intros
  | Vector.t ?Z 0 =>
    revert all except V;
    pattern V; revert V;
    eapply case0; intros
  | Fin.t 0 => inv V
  | Fin.t (S ?n) =>
    let pos := V in
    revert all except pos;
    pattern pos; revert n pos;
    eapply Fin.caseS; intros
  | _ => fail "Wrong type"
  end.

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

(*
Goal ~ Vector.In 10 [|1;2;4|].
Proof.
  intros H. repeat destruct_vector_in; congruence.
Qed.
*)


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



Section In_nth.
  Variable (A : Type) (n : nat).

  Lemma vect_nth_In (v : Vector.t A n) (i : Fin.t n) (x : A) :
    Vector.nth v i = x -> Vector.In x v.
  Proof.
    induction n; cbn in *.
    - inv i.
    - dependent destruct v. dependent destruct i; cbn in *; subst; econstructor; eauto.
  Qed.

  Lemma vect_nth_In' (v : Vector.t A n) (x : A) :
    Vector.In x v -> exists i : Fin.t n, Vector.nth v i = x.
  Proof.
    induction n; cbn in *.
    - inversion 1.
    - dependent destruct v. destruct_vector_in.
      + exists Fin.F1. auto.
      + specialize (IHn0 _ H) as (i&<-). exists (Fin.FS i). auto.
  Qed.

End In_nth.



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

Lemma Vector_in_app {X n1 n2} (x : X) (v1 : Vector.t X n1) (v2 : Vector.t X n2):
  Vector.In x (v1 ++ v2) <-> Vector.In x v1 \/ Vector.In x v2.
Proof.
  induction v1; cbn.
  - firstorder. inversion H.
  - split.
    + intros [-> | H] % In_cons.
      * left. econstructor.
      * eapply IHv1 in H as [ | ]; eauto. left. now econstructor.
    + intros [ [ -> | ] % In_cons | ]; econstructor; intuition.
Qed.

Lemma vect_in_map (X Y : Type) (n : nat) (f : X -> Y) (V : Vector.t X n) (x : X) :
  In x V -> In (f x) (map f V).
Proof. induction 1; cbn; constructor; auto. Qed.

Lemma vect_in_map_iff (X Y : Type) (n : nat) (f : X -> Y) (V : Vector.t X n) (y : Y) :
  In y (map f V) <-> (exists x : X, f x = y /\ In x V).
Proof.
  split.
  - intros H. induction V; cbn in *.
    + inv H.
    + apply In_cons in H as [ <- | H].
      * exists h. split; auto. now constructor 1.
      * specialize (IHV H) as (x&Hx1&Hx2). exists x. split; auto. now constructor 2.
  - intros (x&<-&H). now apply vect_in_map.
Qed.

(* Tactic for simplifying a hypothesis of the form [In x v] *)


Ltac simpl_vector_inv :=
  repeat match goal with
         | [ H : [| |] = (_ ::: _) |- _ ] => solve [discriminate H]
         | [ H : (_ ::: _) = [| |]  |- _ ] => solve [discriminate H]
         | [ H : Fin.F1 = Fin.FS _ |- _] => solve [discriminate H]
         | [ H : Fin.FS _ = Fin.F1 |- _] => solve [discriminate H]
         | [ H : Fin.FS ?i = Fin.FS ?j |- _] =>
           simple apply Fin.FS_inj in H;
           first [is_var i;move H at bottom;subst i | is_var j;move H at bottom;subst j | idtac]
         end.


Ltac simpl_vector_in :=
  repeat
    match goal with
    | _ => first
            [ progress destruct_vector_in
            | progress simpl_vector_inv
            | progress auto
            | congruence
            ]
    | [ H : Vector.In _ (Vector.map _ _) |- _] =>
      let x := fresh "x" in
      eapply vect_in_map_iff in H as (x&<-&H)
    | [ H : Vector.In _ (Vector.map _ _) |- _] =>
      let x := fresh "x" in
      let H' := fresh H in
      eapply vect_in_map_iff in H as (x&H&H')
    | [ H : Vector.In _ (tabulate _) |- _ ] =>
      let i := fresh "i" in
      apply in_tabulate in H as (i&->)
    | [ H : Vector.In _ (tabulate _) |- _ ] =>
      let i := fresh "i" in
      let H := fresh "H" in
      apply in_tabulate in H as (i&H)
    end.

Ltac vector_not_in :=
  let H := fresh "H" in
  intros H; simpl_vector_in.

Goal Vector.In (Fin.F1 (n := 10)) [|Fin1; Fin2; Fin3 |] -> False.
Proof. intros H. simpl_vector_in. Qed.

Goal Vector.In (Fin.F1 (n := 10)) (map (Fin.FS) [|Fin0; Fin1; Fin2|]) -> False.
Proof. intros H. simpl_vector_in. Qed.


(* Conversion between vectors and lists *)
Module VecToListCoercion.
  Coercion Vector.to_list : Vector.t >-> list.
End VecToListCoercion.

Import VecToListCoercion.

Arguments Vector.eqb {_}  _ {_ _}.

Lemma vector_eqb_spec X n eqb:
  (forall (x1 x2 : X) , reflect (x1 = x2) (eqb x1 x2))
  -> forall x y , reflect (x=y) (Vector.eqb (n:=n) eqb x y).
Proof with try (constructor;congruence).
  intros Hf x y.
  apply iff_reflect. symmetry. apply Vector.eqb_eq. symmetry. apply reflect_iff. eauto.
Qed.

Lemma vector_fold_left_right (A B : Type) (f : A -> B -> A) (n : nat) (v : VectorDef.t B n) (a : A):
  Vector.fold_left f a v = Vector.fold_right (fun x y => f y x) (Vector.rev v) a.
Proof.
  now rewrite to_list_fold_right, to_list_fold_left, to_list_rev, List.fold_left_rev_right.
Qed.

Local Arguments Fin.of_nat_lt _ {_} _.

Lemma vector_nth_to_list {X n} (v : Vector.t X n) i d :
  v[@ i] = List.nth (proj1_sig (to_nat i)) (Vector.to_list v) d.
Proof.
  revert v. induction i as [|n i IH].
  - intros v. pattern n, v. now apply Vector.caseS.
  - intros v. revert i IH. pattern n, v. apply Vector.caseS.
    intros ???? IH.
    assert (proj1_sig (to_nat (FS i)) = S (proj1_sig (to_nat i))) as ->.
    { cbn. now destruct Fin.to_nat. }
    now apply IH.
Qed.

Lemma vector_nth_rev X n (v : Vector.t X n) i H':
  (Vector.rev v) [@ i] = v[@ Fin.of_nat_lt (n -1-proj1_sig (Fin.to_nat i)) H'].
Proof.
  assert (x : X). { destruct v; [apply (Fin.case0 _ i)|assumption]. }
  rewrite !(vector_nth_to_list _ _ x), to_nat_of_nat. cbn.
  rewrite Vector.to_list_rev, rev_nth; rewrite length_to_list.
  - f_equal. lia.
  - destruct Fin.to_nat. cbn in *. lia.
Qed.

Lemma Vector_nth_L {X k1 k2} (v1 : Vector.t X k1) (v2 : Vector.t X k2) i :
  (v1 ++ v2)[@ Fin.L k2 i] = v1[@i].
Proof.
  revert k2 v2 i.
  induction v1; intros.
  - pattern i. apply Fin.case0.
  - apply (Fin.caseS' i).
    + reflexivity.
    + cbn. eapply IHv1.
Qed.

Lemma Vector_nth_R {X k1 k2} (v1 : Vector.t X k1) (v2 : Vector.t X k2) i :
  (v1 ++ v2)[@ Fin.R k1 i] = v2[@i].
Proof.
  revert k2 v2 i.
  induction v1; intros.
  - reflexivity.
  - cbn. eapply IHv1.
Qed.
