From Undecidability Require Import TM.Util.Prelim.
Require Import Undecidability.Shared.Libs.PSL.Retracts.
Require Import Coq.Lists.List.

(* * Codable Class **)


(* Class of minimally codable types *)
Class codable (sig: Type) (X: Type) := {
  encode : X -> list sig;
}.
Arguments encode {sig} {X} {_}.

(* either the type or the alphabet must be know at head: *)
#[export] Hint Mode codable - ! : typeclass_instances.
#[export] Hint Mode codable ! - : typeclass_instances.

(* right side must be fully known, left side at head *)
#[export] Hint Mode Retract ! + : typeclass_instances.

(* (* Both sides must be known at head. *)
#[export] Hint Mode Retract ! - : typeclass_instances.
#[export] Hint Mode Retract - ! : typeclass_instances. *)

#[export] Hint Extern 4 (codable (FinType(EqType ?sigX)) ?X) => cbn : typeclass_instances.

(* We often use the above coercion to write [cX x] instead of [encode x], because [encode x] can be ambigious, see [Encode_map] *)
Coercion encode : codable >-> Funclass.

Definition size (sig X : Type) (cX : codable sig X) (x : X) := length (cX x).
Arguments size {sig X cX} x, {_ _} _ _ (*legacy with two arguments*).

#[global]
Instance Encode_unit : codable Empty_set unit :=
  {|
    encode x := nil
  |}.

#[global]
Instance Encode_bool : codable bool bool:=
  {|
    encode x := [x]
  |}.

#[global]
Instance Encode_Fin n : codable (Fin.t n) (Fin.t n):=
  {|
    encode i := [i]
  |}.

Section Encode_Finite.
  Variable sig : finType.

  (* This instance is not declared globally, because of overlaps *)
  Local Instance Encode_Finite : codable sig sig :=
    {|
      encode x := [x];
    |}.

End Encode_Finite.



(* [Encode_map] is no longer an instance for [codable] *)

Section Encode_map.
  Variable (X : Type).
  Variable (sig tau : Type).
  Hypothesis (cX : codable sig X).

  Variable inj : Retract sig tau.

  Definition Encode_map : codable tau X :=
    {|
      encode x := map Retr_f (encode x);
    |}.

End Encode_map.

(* Builds simple retract functions like [sigSum -> option sigX] in the form
[fun x => match x with constructor_name y => Retr_g y | _ => None] *)

Local Hint Mode Retract - - : typeclass_instances.
Ltac build_simple_retract_g :=
  once lazymatch goal with
  | [ |- ?Y -> option ?X ] =>
    (* idtac "Retract function" X Y; *)
    let x := fresh "x" in
    intros x; destruct x; intros; try solve [now apply Retr_g ]; right
  end.

Ltac build_simple_retract :=
  once lazymatch goal with
  | [ |- Retract ?X ?Y ] =>
    (* idtac "Retract from" X "to" Y; *)
    let x := fresh "x" in
    let y := fresh "y" in
    let f := (eval simpl in (ltac:(intros x; constructor; now apply Retr_f) : X -> Y)) in
    (* idtac "f:" f; *)
    let g := (eval simpl in (ltac:(build_simple_retract_g) : Y -> option X)) in
    (* idtac "g:" g; *)
    apply Build_Retract with (Retr_f := f) (Retr_g := g);
    abstract now hnf; intros x y; split;
    [ destruct y; try congruence; now intros -> % retract_g_inv
    | now intros ->; now retract_adjoint
    ]
  end
.

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

(* Compute Encode_pair Encode_bool (Encode_sum Encode_unit Encode_bool) (true, inl tt). *)

(* Check _ : codable (sigPair bool (sigSum Empty_set bool)) unit. *)

Section Encode_list.

  Inductive sigList (sigX : Type) : Type :=
  | sigList_X (s : sigX)
  | sigList_nil
  | sigList_cons
  .

  Arguments sigList_nil {sigX}. Arguments sigList_cons {sigX}. Arguments sigList_X {sigX}.

  Global Instance Retract_sigList_X (sig tau : Type) (retr : Retract sig tau) : Retract sig (sigList tau).
  Proof. build_simple_retract. Defined. (* because definition *)

  Global Instance sigList_dec sigX (decX : eq_dec sigX) :
    eq_dec (sigList sigX) := ltac:(build_eq_dec).

  Global Instance sigList_fin (sigX : finType) : finTypeC (EqType (sigList sigX)).
  Proof.
    split with (enum := sigList_nil :: sigList_cons :: map sigList_X enum).
    intros [x| | ]; cbn; f_equal.
    - rewrite countMap_injective. 2: apply retract_f_injective with (I := Retract_sigList_X (Retract_id _)).
      now apply enum_ok.
    - rewrite countMap_zero. lia. congruence.
    - rewrite countMap_zero. lia. congruence.
  Qed.

  Variable sigX: Type.
  Variable (X : Type) (cX : codable sigX X).

  Fixpoint encode_list (xs : list X) : list (sigList sigX) :=
    match xs with
    | nil => [sigList_nil]
    | x :: xs' => sigList_cons :: Encode_map _ _ x ++ encode_list xs'
    end.

  Global Instance Encode_list : codable (sigList sigX) (list X) :=
    {|
      encode := encode_list;
    |}.

  Lemma encode_list_app (xs ys : list X) :
    encode_list (xs ++ ys) = removelast (encode_list xs) ++ encode_list ys.
  Proof.
    revert ys. induction xs; intros; cbn in *; f_equal.
    rewrite IHxs. rewrite app_assoc, app_comm_cons; f_equal.
    destruct (map (fun x : sigX => sigList_X x) (cX a)) eqn:E; cbn.
    - destruct xs; cbn; auto.
    - f_equal. destruct (cX a) eqn:E2; cbn in E. congruence.
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
      change (sigList_cons :: Encode_map _ _ a ++ encode_list xs)
        with ((sigList_cons :: Encode_map _ _ a) ++ encode_list xs).
      rewrite removelast_app by apply encode_list_neq_nil.
      rewrite <- app_assoc. f_equal. auto.
  Qed.

End Encode_list.

Arguments sigList_nil {sigX}. Arguments sigList_cons {sigX}. Arguments sigList_X {sigX}.

#[export] Hint Extern 4 (finTypeC (EqType (sigList _))) => eapply sigList_fin : typeclass_instances.
(* Check FinType(EqType (sigList bool)). *)


(* Compute Encode_list Encode_bool (nil). *)
(* This cannot reduce to [sigList_cons :: sigList_X true :: Encode_list _] *)
(* Eval cbn in Encode_list Encode_bool (true :: _). *)
(* Compute Encode_list Encode_bool (true :: false :: nil). *)
