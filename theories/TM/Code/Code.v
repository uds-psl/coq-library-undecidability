From Undecidability Require Import TM.Util.Prelim.
From Stdlib Require Import Lists.List.

Set Default Goal Selector "!".

Ltac build_eq_dec :=
  let x := fresh "x" in
  let y := fresh "y" in
  intros x y; hnf; decide equality;
  apply Dec; auto.


Lemma countMap_injective (X Y : eqType) (x : X) (A : list X) (f : X -> Y) :
  (forall x y, f x = f y -> x = y) ->
  FinTypesDef.count (map f A) (f x) = FinTypesDef.count A x.
Proof.
  intros HInj. revert x. induction A as [ | a A IH]; intros; cbn in *; auto.
  decide (f x = f a) as [ -> % HInj | He].
  - decide (a = a) as [_ | Ha]; auto. congruence.
  - decide (x = a) as [-> | Hx]; auto. congruence.
Qed.

Lemma countMap_zero (X Y : eqType) (A : list X) (y : Y) (f : X -> Y) :
  (forall x, f x <> y) ->
  FinTypesDef.count (map f A) y = 0.
Proof.
  revert y. induction A as [ | a A IH]; intros; cbn in *; auto.
  decide (y = f a) as [-> | ?]; auto. now contradiction (H a).
Qed.

Section Encode_list.

  Inductive sigList (sigX : Type) : Type :=
  | sigList_X (s : sigX)
  | sigList_nil
  | sigList_cons
  .

  Arguments sigList_nil {sigX}. Arguments sigList_cons {sigX}. Arguments sigList_X {sigX}.

  #[export] Instance sigList_dec sigX (decX : eq_dec sigX) :
    eq_dec (sigList sigX) := ltac:(build_eq_dec).

  #[export] Instance sigList_fin (sigX : finType) : finTypeC (EqType (sigList sigX)).
  Proof.
    split with (enum := sigList_nil :: sigList_cons :: map sigList_X enum).
    intros [x| | ]; cbn; f_equal.
    - rewrite countMap_injective. { apply enum_ok. }
      now intros ?? [= ?].
    - now apply countMap_zero.
    - now apply countMap_zero.
  Qed.

  Variable sigX: Type.
  Variable (X : Type) (encode : X -> list sigX).

  Fixpoint encode_list (xs : list X) : list (sigList sigX) :=
    match xs with
    | nil => [sigList_nil]
    | x :: xs' => sigList_cons :: (map sigList_X (encode x)) ++ encode_list xs'
    end.

  Lemma encode_list_app (xs ys : list X) :
    encode_list (xs ++ ys) = removelast (encode_list xs) ++ encode_list ys.
  Proof.
    revert ys. induction xs; intros; cbn in *; f_equal.
    rewrite IHxs. rewrite app_assoc, app_comm_cons; f_equal.
    destruct (map (fun x : sigX => sigList_X x) (encode a)) eqn:E; cbn.
    - destruct xs; cbn; auto.
    - f_equal. destruct (encode a) eqn:E2; cbn in E. { congruence. }
      rewrite removelast_app.
      + destruct (l ++ encode_list xs) eqn:E3; cbn; auto.
        apply app_eq_nil in E3 as (E3&E3'). destruct xs; inv E3'.
      + destruct xs; cbn; congruence.
  Qed.

  Lemma encode_list_neq_nil (xs : list X) :
    encode_list xs <> nil.
  Proof. destruct xs; cbn; congruence. Qed.

  Lemma encode_list_remove (xs : list X) :
    removelast (encode_list xs) ++ [sigList_nil] = encode_list xs.
  Proof.
    induction xs.
    - reflexivity.
    - cbn [encode_list].
      change (sigList_cons :: map sigList_X (encode a) ++ encode_list xs) with
        ((sigList_cons :: map sigList_X (encode a)) ++ encode_list xs).
      rewrite removelast_app by apply encode_list_neq_nil.
      rewrite <- app_assoc. f_equal. auto.
  Qed.

End Encode_list.

Arguments sigList_nil {sigX}. Arguments sigList_cons {sigX}. Arguments sigList_X {sigX}.

#[export] Hint Extern 4 (finTypeC (EqType (sigList _))) => eapply sigList_fin : typeclass_instances.
