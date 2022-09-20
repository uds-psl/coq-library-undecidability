(* * Dupfree vector *)
(* Author: Maximilian Wuttke *)

From Undecidability.Shared.Libs.PSL Require Import Prelim.
From Undecidability.Shared.Libs.PSL Require Import Tactics.Tactics.
From Undecidability.Shared.Libs.PSL Require Import Vectors.Vectors.
From Undecidability.Shared.Libs.PSL Require Import FiniteTypes.FinTypes.
From Undecidability.Shared.Libs.PSL Require Import Lists.BaseLists.
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

(*
Goal dupfree [| 4; 8; 15; 16; 23; 42 |].
Proof. vector_dupfree. Qed.

Goal dupfree [| Fin.F1 (n := 1) |].
Proof. vector_dupfree. Qed.
*)

Lemma dupfree_cons (X : Type) (n : nat) (x : X) (xs : Vector.t X n) :
  dupfree (x ::: xs) -> dupfree xs /\ ~ In x xs.
Proof.
  intros H1. inv H1. now existT_eq'.
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

Import VecToListCoercion.

Lemma tolist_dupfree (X : Type) (n : nat) (xs : Vector.t X n) :
  dupfree xs -> List.NoDup xs.
Proof.
  induction 1.
  - cbn. constructor.
  - cbn. constructor; auto. intros H1. contradict H. now apply Vector.to_list_In.
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
