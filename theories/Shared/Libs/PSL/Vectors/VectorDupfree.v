(* * Dupfree vector *)
(* Author: Maximilian Wuttke *)

From Undecidability.Shared.Libs.PSL Require Import Prelim.
From Undecidability.Shared.Libs.PSL Require Import Tactics.Tactics.
From Undecidability.Shared.Libs.PSL Require Import Vectors.Vectors.
From Undecidability.Shared.Libs.PSL Require Import FiniteTypes.FinTypes.
From Undecidability.Shared.Libs.PSL Require Lists.Dupfree.
Require Import Coq.Vectors.Vector.

Open Scope vector_scope.
Import VectorNotations2.


Inductive dupfree X : forall n, Vector.t X n -> Prop :=
  dupfreeVN :
    dupfree (@Vector.nil X)
| dupfreeVC n (x : X) (V : Vector.t X n) :
    ~ Vector.In x V -> dupfree V -> dupfree (x ::: V).


Ltac vector_dupfree :=
  match goal with
  | [ |- dupfree (Vector.nil _) ] =>
    constructor
  | [ |- dupfree (?a ::: ?bs)] =>
    constructor; [vector_not_in | vector_dupfree]
  end.

Goal dupfree [| 4; 8; 15; 16; 23; 42 |].
Proof. vector_dupfree. Qed.

Goal dupfree [| Fin.F1 (n := 1) |].
Proof. vector_dupfree. Qed.

(*
(* This also works, but needs a bit to comile *)
From Undecidability.Shared.Libs.PSL Require Import Vectors.FinNotation.
Goal dupfree ([| Fin4; Fin8; Fin15; Fin16; Fin23; Fin42 |] : Vector.t (Fin.t 43) _).
Proof. vector_dupfree. Qed.
*)

Lemma dupfree_singleton (X : Type) (x : X) : dupfree [| x |].
Proof. now constructor; [|constructor]. Qed. 

Lemma dupfree_cons (X : Type) (n : nat) (x : X) (xs : Vector.t X n) :
  dupfree (x ::: xs) -> dupfree xs /\ ~ In x xs.
Proof.
  intros H1. inv H1. now existT_eq'.
Qed.

Lemma dupfree_replace (X : Type) (n : nat) (xs : Vector.t X n) (x : X) :
  dupfree xs -> ~ In x xs -> forall i, dupfree (replace  xs i x).
Proof.
  revert x. induction xs; intros; cbn.
  - inv i.
  - dependent destruct i; cbn.
    + constructor; auto.
      * intros H1. contradict H0. now econstructor.
      * inv H. existT_eq'. assumption.
    + apply dupfree_cons in H as (H&H').
      assert (~In x xs).
      {
        intros H1. contradict H0. now constructor.
      }
      specialize (IHxs x H H1 p). constructor.
      * intros [ -> | H2] % In_replace. contradict H0. constructor. tauto.
      * tauto.
Qed.


Lemma dupfree_tabulate_injective (X : Type) (n : nat) (f : Fin.t n -> X) :
  (forall x y, f x = f y -> x = y) ->
  dupfree (tabulate f).
Proof.
  intros H. revert f H. induction n; intros; cbn.
  - constructor.
  - constructor.
    + intros (x & H2 % H) % in_tabulate. congruence.
    + eapply IHn. now intros x y -> % H % Fin.FS_inj.
Qed.

Lemma dupfree_map_injective (X Y : Type) (n : nat) (f : X -> Y) (V : Vector.t X n) :
  (forall x y, f x = f y -> x = y) ->
  dupfree V ->
  dupfree (map f V).
Proof.
  intros HInj. induction 1.
  - cbn. constructor.
  - cbn. constructor; auto. now intros (? & -> % HInj & ?) % vect_in_map_iff.
Qed.

Import VecToListCoercion.

Lemma tolist_dupfree (X : Type) (n : nat) (xs : Vector.t X n) :
  dupfree xs -> Dupfree.dupfree xs.
Proof.
  induction 1.
  - cbn. constructor.
  - cbn. constructor; auto. intros H1. contradict H. now apply tolist_In.
Qed.

Section Count.
  Variable (X : eqType).

  Definition count (n : nat) (x : X) (xs : t X n) :=
    fold_right (fun y c => if Dec (x = y) then S c else c) xs 0.

  Lemma count0_notIn (n : nat) (x : X) (xs : t X n) :
    count x xs = 0 -> ~ In x xs.
  Proof.
    revert x. induction xs; intros; cbn in *.
    - vector_not_in.
    - intros H1. decide (x=h); try congruence.
      apply In_cons in H1 as [-> | H1]; try tauto.
      eapply IHxs; eauto.
  Qed.

  Lemma count0_notIn' (n : nat) (x : X) (xs : t X n) :
    ~ In x xs -> count x xs = 0.
  Proof.
    induction xs; intros; cbn in *.
    - reflexivity.
    - decide (x = h) as [ -> | D ].
      + contradict H. constructor.
      + apply IHxs. intros H2. contradict H. now constructor.
  Qed.

  Lemma countDupfree (n : nat) (xs : t X n) :
    (forall x : X, In x xs -> count x xs = 1) <-> dupfree xs.
  Proof.
    split; intros H.
    {
      induction xs; cbn -[count] in *.
      - constructor.
      - constructor.
        + intros H2. specialize (H h ltac:(now constructor)). cbn in H.
          decide (h = h); try tauto. inv H.
          contradict H2. now eapply count0_notIn.
        + apply IHxs. intros x Hx. specialize (H x ltac:(now constructor)).
          cbn in H. decide (x = h); inv H; auto. rewrite H1.
          contradict Hx. now eapply count0_notIn.
    }
    {
      induction H as [ | n x' xs HIn HDup IH ]; intros; cbn in *.
      - inv H.
      - decide (x = x') as [ -> | D].
        + f_equal. exact (count0_notIn' HIn).
        + apply (IH x). now apply In_cons in H as [ -> | H].
    }
  Qed.


(* (* Test *)
End Count.
Compute let xs := [|1;2;3;4;5;6|] in
        let x  := 2 in
        let y  := 1 in
        let i  := Fin.F1 in
        Dec (x = y) + count x xs = Dec (x = xs[@i]) + count x (replace xs i y).
*)

  Lemma replace_nochange (n : nat) (xs : Vector.t X n) (p : Fin.t n) :
    replace xs p xs[@p] = xs.
  Proof.
    eapply eq_nth_iff. intros ? ? <-.
    decide (p = p1) as [ -> | D].
    - now rewrite replace_nth.
    - now rewrite replace_nth2.
  Qed.
  
  Lemma count_replace (n : nat) (xs : t X n) (x y : X) (i : Fin.t n) :
    bool2nat (Dec (x = y)) + count x xs = bool2nat (Dec (x = xs[@i])) + count x (replace xs i y).
  Proof.
    induction xs; intros; cbn -[nth count] in *.
    - inv i.
    - dependent destruct i; cbn -[nth count] in *.
      + decide (x = y) as [ D | D ]; cbn -[nth count] in *; cbn -[bool2nat dec2bool count].
        * rewrite <- D in *. decide (x = h) as [ -> | D2]; cbn [dec2bool bool2nat plus]; auto.
          cbv [count]. cbn. rewrite D. decide (y = y); try tauto. decide (y = h); congruence.
        * decide (x = h); subst; cbn [bool2nat dec2bool plus]; cbv [count]; try reflexivity.
          -- cbn. decide (h = h); try tauto. decide (h = y); tauto.
          -- cbn. decide (x = h); try tauto. decide (x = y); tauto.
      + cbn. decide (x = y); cbn.
        * decide (x = h); cbn; f_equal.
          -- decide (x = xs[@p]); cbn; repeat f_equal; subst.
             ++ symmetry. now apply replace_nochange.
             ++ cbn in *. specialize (IHxs p). decide (h = xs[@p]); tauto.
          -- decide (x = xs[@p]); cbn; repeat f_equal; subst.
             ++ symmetry. now apply replace_nochange.
             ++ cbn in *. specialize (IHxs p). decide (y = xs[@p]); tauto.
        * decide (x = h); cbn; f_equal.
          -- decide (x = xs[@p]); cbn; f_equal; subst.
             ++ cbn in *. specialize (IHxs p). decide (xs[@p] = xs[@p]); cbn in *; try tauto.
             ++ specialize (IHxs p). cbn in *. decide (h = xs[@p]); cbn in *; tauto.
          -- decide (x = xs[@p]); cbn; auto.
             ++ specialize (IHxs p). cbn in *. decide (x = xs[@p]); cbn in *; tauto.
             ++ specialize (IHxs p). cbn in *. decide (x = xs[@p]); cbn in *; tauto.
  Qed.
  
End Count.

Lemma dupfree_nth_injective (X : Type) (n : nat) (xs : Vector.t X n) :
  dupfree xs -> forall (i j : Fin.t n), xs[@i] = xs[@j] -> i = j.
Proof.
  induction 1; intros; cbn -[nth] in *.
  - inv i.
  - dependent destruct i; dependent destruct j; cbn -[nth] in *; auto.
    + cbn in *. contradict H. eapply vect_nth_In; eauto.
    + cbn in *. contradict H. eapply vect_nth_In; eauto.
    + f_equal. now apply IHdupfree.
Qed.


Lemma Vector_dupfree_app {X n1 n2} (v1 : Vector.t X n1) (v2 : Vector.t X n2) :
  VectorDupfree.dupfree (Vector.append v1 v2) <-> VectorDupfree.dupfree v1 /\ VectorDupfree.dupfree v2 /\ forall x, Vector.In x v1 -> Vector.In x v2 -> False.
Proof.
  induction v1; cbn.
  - firstorder. econstructor. inversion H0.
  - split.
    + intros [] % VectorDupfree.dupfree_cons. repeat split.
      * econstructor. intros ?. eapply H0. eapply Vector_in_app. eauto. eapply IHv1; eauto.
      * eapply IHv1; eauto.
      * intros ? [-> | ?] % In_cons ?.
        -- eapply H0. eapply Vector_in_app. eauto.
        -- eapply IHv1; eauto.
    + intros (? & ? & ?). econstructor. 2:eapply IHv1; repeat split.
      * intros [? | ?] % Vector_in_app.
        -- eapply VectorDupfree.dupfree_cons in H as []. eauto.
        -- eapply H1; eauto. econstructor.
      * eapply VectorDupfree.dupfree_cons in H as []. eauto.
      * eauto.
      * intros. eapply H1. econstructor 2. eauto. eauto.
Qed.
