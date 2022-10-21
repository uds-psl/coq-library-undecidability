From Undecidability Require Import TM.Util.Prelim.
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


(* Hint database for encoding compatibility lemmas. For example, size functions are usually parametrised over an encoding. It doesn't matter for the size, whether we apply [Encode_map] on this encoding. This kind of lemmas is encodable in this HintDb. *)
Create HintDb encode_comp.

Ltac simpl_comp := autorewrite with encode_comp.


#[global]
Instance Encode_unit : codable Empty_set unit :=
  {|
    encode x := nil
  |}.

Lemma Encode_unit_hasSize (t:unit) :
  size t = 0.
Proof. cbn. reflexivity. Qed.

Lemma Encode_unit_injective : injective Encode_unit.
Proof. now intros [] [] _. Qed.


#[global]
Instance Encode_bool : codable bool bool:=
  {|
    encode x := [x]
  |}.

Lemma Encode_bool_hasSize (b:bool) :
  size Encode_bool b = 1.
Proof. cbn. reflexivity. Qed.

Lemma Encode_bool_injective : injective Encode_bool.
Proof. intros [ | ] [ | ] H; cbn in *; congruence. Qed.

#[global]
Instance Encode_Fin n : codable (Fin.t n) (Fin.t n):=
  {|
    encode i := [i]
  |}.

Lemma Encode_Fin_hasSize n i :
  size (Encode_Fin n) i = 1.
Proof. cbn. reflexivity. Qed.

Lemma Encode_Fin_injective n : injective (Encode_Fin n).
Proof. intros i1 i2. cbn. congruence. Qed.

(*
Compute encode true.
(* This works thanks to the coercion above *)
Compute Encode_bool true.
Compute encode tt.
Check encode Fin0.
Compute encode Fin0 : list (Fin.t 10).
*)


Section Encode_Finite.
  Variable sig : finType.

  (* This instance is not declared globally, because of overlaps *)
  Local Instance Encode_Finite : codable sig sig :=
    {|
      encode x := [x];
    |}.

  Lemma Encode_Finite_hasSize f :
    size Encode_Finite f = 1.
  Proof. reflexivity. Qed.

  Lemma Encode_Finite_injective : injective Encode_Finite.
  Proof. intros x1 x2. cbn. congruence. Qed.

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

  Lemma Encode_map_hasSize x :
    size Encode_map x =size x.
  Proof. cbn. now rewrite map_length. Qed.

  Lemma Encode_map_injective :
    injective cX -> injective Encode_map.
  Proof. intros H. hnf in H; hnf. cbn in *. intros x1 x2 ? % map_injective; auto. apply retract_f_injective. Qed.

End Encode_map.

(* Hint Rewrite Encode_map_hasSize : encode_comp. *)

Section Encode_map_comp.
  Variable (X : Type).
  Variable (sig1 sig2 sig3 : Type).
  Variable (cX : codable sig1 X).
  Variable (I1 : Retract sig1 sig2) (I2 : Retract sig2 sig3).

  Lemma Encode_map_id x :
    Encode_map cX (Retract_id _) x = cX x.
  Proof. cbn. now rewrite map_id. Qed.

  Lemma Encode_map_comp x :
    Encode_map (Encode_map cX I1) I2 x = Encode_map cX (ComposeRetract I2 I1) x.
  Proof. cbn. rewrite List.map_map. reflexivity. Qed.

End Encode_map_comp.


Global Hint Rewrite Encode_map_id Encode_map_comp : encode_comp.


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

(* TODO: ~> Base *)
Lemma skipn_0 (A:Type) (xs : list A) : skipn 0 xs = xs. Proof. reflexivity. Qed.

(* TODO: ~> Base *)
Lemma skipn_tl (A:Type) (xs : list A) (n : nat) : skipn (S n) xs = skipn n (tl xs).
Proof. induction n; cbn; destruct xs; auto. Qed.




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

  Lemma encode_list_concat l:
    encode_list l = concat (map (fun t => sigList_cons :: map sigList_X (encode t)) l) ++[sigList_nil].
  Proof.
    induction l;cbn. reflexivity.
    rewrite IHl. cbn. now autorewrite with list.
  Qed.

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

  Corollary Encode_list_app (xs ys : list X) :
    Encode_list (xs ++ ys) = removelast (Encode_list xs) ++ Encode_list ys.
  Proof. cbn. now apply encode_list_app. Qed.

  Lemma encode_list_neq_nil (xs : list X) :
    encode_list xs <> nil.
  Proof. destruct xs; cbn; congruence. Qed.

  Corollary Encode_list_neq_nil (xs : list X) :
    Encode_list xs <> nil.
  Proof. cbn. apply encode_list_neq_nil. Qed.

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

  Corollary Encode_list_remove (xs : list X) :
    removelast (Encode_list xs) ++ [sigList_nil] = Encode_list xs.
  Proof. cbn. apply encode_list_remove. Qed.

  Fixpoint Encode_list_size (xs : list X) : nat :=
    match xs with
    | nil => 1
    | x :: xs' => S (size x + Encode_list_size xs')
    end.

  Lemma Encode_list_hasSize (xs : list X) : size xs = Encode_list_size xs.
  Proof.
    induction xs as [ | x xs IH]; cbn; f_equal.
    rewrite app_length, !map_length. fold (size x). now rewrite <- IH.
  Qed.

  Lemma Encode_list_hasSize_skipn (xs : list X) (n : nat) :
    Encode_list_size (skipn n xs) <= Encode_list_size xs.
  Proof.
    revert n. induction xs as [ | x xs' IH]; intros n.
    - cbn. rewrite skipn_nil. cbn. reflexivity.
    - cbn. destruct n.
      + rewrite skipn_0. cbn. reflexivity.
      + cbn. rewrite IH. lia.
  Qed.

  Lemma Encode_list_hasSize_ge1 (xs : list X) :
    1 <= Encode_list_size xs.
  Proof. induction xs; cbn; lia. Qed.

  Lemma Encode_list_hasSize_app (xs ys : list X) :
    Encode_list_size (xs ++ ys) = Encode_list_size xs + Encode_list_size ys - 1.
  Proof.
    induction xs as [ | x xs IH] in xs,ys|-*; cbn.
    - lia.
    - rewrite IH. enough (1 <= Encode_list_size xs) by lia. apply Encode_list_hasSize_ge1.
  Qed.

  Lemma encode_list_eq_nil (xs : list X) : encode_list xs = [sigList_nil] -> xs = nil.
  Proof. destruct xs; cbn; congruence. Qed.

End Encode_list.

Arguments sigList_nil {sigX}. Arguments sigList_cons {sigX}. Arguments sigList_X {sigX}.

#[export] Hint Extern 4 (finTypeC (EqType (sigList _))) => eapply sigList_fin : typeclass_instances.
(* Check FinType(EqType (sigList bool)). *)


(* Compute Encode_list Encode_bool (nil). *)
(* This cannot reduce to [sigList_cons :: sigList_X true :: Encode_list _] *)
(* Eval cbn in Encode_list Encode_bool (true :: _). *)
(* Compute Encode_list Encode_bool (true :: false :: nil). *)
