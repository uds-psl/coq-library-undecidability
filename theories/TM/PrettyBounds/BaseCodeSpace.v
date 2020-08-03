(** * Case Study: Place usage for list machines *)

From Undecidability Require Import ProgrammingTools.
From Undecidability Require Export SpaceBounds PrettyBounds.
From Undecidability Require Import CaseNat CaseList.
From Undecidability Require Import ListTM.


(** This really ougth to be global *)
Global Arguments size : simpl never.


Lemma Constr_S_size_nice :
  forall (n : nat) (s : nat),
    pred s + size(S n) = max (size n + s) (size (S n)).
Proof.
  intros. rewrite !Encode_nat_hasSize. nia.
Qed.

(** We only apply the size function of [CaseNat], which is [S], if [n>0]. For [n=0], we just have the identity. See [CaseNat_Rel]. *)
Lemma CaseNat_size_nice :
  forall (n : nat) (s : nat),
    (* let k := s + size (S n) in *)
    1 <= n ->
    S s + size (pred n) = s + size n.
    (* (S s + size (pred n) = k). *)
Proof.
  intros.
  ring_simplify. rewrite !Encode_nat_hasSize. ring_simplify. replace (pred (1 + n)) with n by nia.
  nia.
Qed.

Section CaseList_nice.
  Variable (sigX X : Type) (cX : codable sigX X).

  Lemma CaseList_size0_nice (x : X) (xs : list X) (s : nat) :
    CaseList_size0 x s + size xs = s + size (x :: xs).
  Proof. cbn. unfold CaseList_size0. rewrite !Encode_list_hasSize; cbn. nia. Qed.

  (** This lemma looks more reasonable. Note that this kind of the case is actually like a constructor. *)
  Lemma CaseList_size1_nice (x : X) (s : nat) :
    CaseList_size1 x s + size x = max (pred s) (size x).
  Proof. intros. cbn. unfold CaseList_size1. cbn. nia. Qed.

  (** We can move the [+1] inside the [max] *)
  (** This is, because the tape is initial empty, and a start symbol had to be added. If there was already a start symbol, we don't need to allocate new memory for this *)
  Lemma CaseList_size1_nice' (x : X) (s : nat) :
    CaseList_size1 x s + size x + 1 = max s (size x + 1).
  Proof. intros. cbn. unfold CaseList_size1. cbn. nia. Qed.

  Lemma Constr_cons_size_nice (xs : list X) (x : X) (s : nat) :
    Constr_cons_size x s + size (x::xs) = max (size xs + s) (size (x::xs)).
  Proof. unfold Constr_cons_size. rewrite Encode_list_hasSize; cbn. rewrite <- !Encode_list_hasSize. ring_simplify. nia. Qed.

End CaseList_nice.


Section Copy_size_nice.
  Variable (sigX X : Type) (cX : codable sigX X).

  Lemma CopyValue_size_nice :
    forall (x : X) (s : nat), CopyValue_size x s + size x = max (pred s) (size x).
  Proof. intros. unfold CopyValue_size. nia. Qed.

  Lemma CopyValue_size_nice' :
    forall (x : X) (s : nat), CopyValue_size x s + size x + 1 = max s (size x + 1).
  Proof. intros. unfold CopyValue_size. nia. Qed.

  (** We can't simplify a lot here; [Reset] isn't nicer *)
  Lemma Reset_size_nice :
    forall (x : X) (s : nat), Reset_size x s = (s + size x) + 1.
  Proof. intros. unfold Reset_size. nia. Qed.

  (** Same as [Reset_size] *)
  Lemma MoveValue_size_x_nice :
    forall (x : X) (s : nat), MoveValue_size_x x s = (s + size x) + 1.
  Proof. intros. apply Reset_size_nice. Qed.

  Variable (sigY Y : Type) (cY : codable sigY Y).

  (** Replace [y] by [x] *)
  Lemma MoveValue_size_y_nice :
    forall (x : X) (y : Y) (s : nat), MoveValue_size_y x y s + size x = max (s + size y) (size x).
  Proof. intros. unfold MoveValue_size_y. nia. Qed.

End Copy_size_nice.

Section CasePair_size_nice.
  Variable (sigX sigY X Y : Type) (cX : codable sigX X) (cY : codable sigY Y).

  Lemma CasePair_size0_nice (x : X) (y : Y) (s0 : nat) :
    CasePair_size0 x s0 + size y = s0 + size (x,y).
  Proof. unfold CasePair_size0. rewrite Encode_pair_hasSize; cbn. nia. Qed.

  Lemma CasePair_size1_nice (x : X) (s1 : nat) :
    CasePair_size1 x s1 + size x = max (pred s1) (size x).
  Proof. unfold CasePair_size1. nia. Qed.

  (** The same issue as for [CaseList_size1_nice'] *)
  Lemma CasePair_size1_nice' (x : X) (s1 : nat) :
    CasePair_size1 x s1 + size x + 1 = max s1 (size x + 1).
  Proof. unfold CasePair_size1. nia. Qed.

  Lemma Constr_pair_size_nice (x : X) (y : Y) (s : nat) :
    Constr_pair_size x s + size (x,y) = max (s + size y) (size (x,y)).
  Proof. unfold Constr_pair_size. rewrite Encode_pair_hasSize; cbn. ring_simplify. nia. Qed.

End CasePair_size_nice.




Lemma size_S (n : nat) :
  size (S n) = S (size n).
Proof. now rewrite !Encode_nat_hasSize. Qed.


Lemma Forall2_map (A B C D : Type) (f : A -> C) (g : B -> D) (P : C -> D -> Prop) (xs : list A) (ys : list B) :
  Forall2 (fun a b => P (f a) (g b)) xs ys ->
  Forall2 P (map f xs) (map g ys).
Proof. induction 1; cbn; constructor; auto. Qed.

Lemma Forall_Forall2 (A : Type) (P : A -> A -> Prop) (xs : list A) :
  (Forall (fun x => P x x) xs) ->
  Forall2 P xs xs.
Proof. induction 1; constructor; auto. Qed.


(** ** Common combinations *)

(** Deteach the head and delete the tail *)
Lemma CaseList_size0_Reset_nice (sigX X : Type) (cX : codable sigX X) :
  forall (x : X) (xs : list X) (s : nat), (CaseList_size0 x >> Reset_size xs) s = s + size (x :: xs) + 1. (* plus one, because the tape is emptied *)
Proof.
  intros. cbn. rewrite Reset_size_nice. rewrite CaseList_size0_nice. rewrite !Encode_list_hasSize; cbn. nia.
Qed.


(** Remove the copied head *)
Lemma CaseList_size1_Reset_nice (sigX X : Type) (cX : codable sigX X) :
  forall (x : X) (s : nat), (CaseList_size1 x >> Reset_size x) s = Init.Nat.max s (size x + 1).
Proof.
  intros. cbn.
  rewrite Reset_size_nice.
  now rewrite CaseList_size1_nice'.
Qed.


(** Delete the first part of the tuple after copying it *)
Lemma CasePair_size1_Reset_nice (sigX X : Type) (cX : codable sigX X) :
  forall (x : X) (s : nat), (CasePair_size1 x >> Reset_size x) s = max s (size x + 1).
(* (* works: *) Proof. intros. cbn. unfold Reset_size, CasePair_size1. ring_simplify. nia. *)
Proof. intros. cbn. rewrite Reset_size_nice. rewrite CasePair_size1_nice. nia. Qed.

(** Delete the second part of the tuple removing the first part *)
Lemma CasePair_size0_Reset_nice (sigX X sigY Y : Type) (cX : codable sigX X) (cY : codable sigY Y) :
  forall (x : X) (y : Y) (s : nat), (CasePair_size0 x >> Reset_size y) s = s + size (x, y) + 1.
Proof. intros. cbn. rewrite Reset_size_nice. now rewrite CasePair_size0_nice. Qed.



(** ** Simple List functions *)


Section Length_size_nice.
  Variable (sigX X : Type) (cX : codable sigX X).

  (** There is only the [cons] case *)
  Lemma Length_Step_size_nice :
    (forall (x : X) (xs : list X) (s0 : nat), Length_Step_size x @>Fin0 s0 + size xs    = s0 + size (x::xs)) /\
    (forall (x : X) (n : nat) (s1 : nat),       Length_Step_size x @>Fin1 s1 + size (S n) = max (size n + s1) (size (S n))) /\
    (forall (x : X) (s2 : nat),               Length_Step_size x @>Fin2 s2              = max s2 (size x + 1)).
  Proof.
    repeat split; unfold Length_Step_size; cbn; intros.
    - now rewrite CaseList_size0_nice.
    - now rewrite Constr_S_size_nice.
    - apply CaseList_size1_Reset_nice.
  Qed.

  Local Arguments Length_Step_size : simpl never.


  Lemma Length_Loop_size_nice (xs : list X) :
    (forall (s0 : nat),         Length_Loop_size xs @>Fin0 s0 + size nil             = s0 + size xs) /\
    (forall (n : nat) (s1 : nat), Length_Loop_size xs @>Fin1 s1 + size (n + length xs) = max (size n + s1) (size (n + length xs)))  /\
    (forall (s2 : nat),         Length_Loop_size xs @>Fin2 s2                        = max_list_rec s2 (map (fun x => size x + 1) xs)).
  Proof.
    induction xs as [ | x xs (IH0&IH1&IH2)].
    {
      repeat split; cbn; intros.
      - rewrite !Encode_nat_hasSize. ring_simplify. cbv [id]. ring_simplify. nia.
    }
    {
      repeat split; cbn; intros.
      - rewrite IH0. projk_rewrite Length_Step_size_nice 0. rewrite !Encode_list_hasSize; cbn. nia.
      - replace (n + S (|xs|)) with (S n + |xs|) by lia.
        rewrite IH1. rewrite Nat.add_comm. cbn.
        projk_rewrite (Length_Step_size_nice) 1.
        rewrite !Encode_nat_hasSize. cbn. nia.
      - rewrite IH2. projk_rewrite (Length_Step_size_nice) 2. f_equal. nia.
    }
  Qed.

  Lemma Length_size_nice (xs : list X) :
    (forall (s0 : nat), Length_size xs @>Fin0 s0                        = s0) /\ (* Input tape doesn't change *)
    (forall (s1 : nat), Length_size xs @>Fin1 s1 + size (length xs) + 1 = max s1 (size (length xs) + 1)) /\ (* I think we have to add [+1] here, because this is an output tape; the tape was empty before and contains a value afterwards *)
    (forall (s2 : nat), Length_size xs @>Fin2 s2                        = max_list_rec s2 (map (fun x => size x + 1) xs)) /\ (* Internal tape: allocate no more memory than needed *)
    (forall (s3 : nat), Length_size xs @>Fin3 s3                        = max s3 (size xs + 1)). (* Internal tape *)
  Proof.
    unfold Length_size; cbn. repeat split; intros; auto.
    - change (|xs|) with (0 + |xs|). projk_rewrite (Length_Loop_size_nice xs) 1. unfold Constr_O_size. cbn.
      rewrite !Encode_nat_hasSize. nia.
    - projk_rewrite (Length_Loop_size_nice xs) 2. cbn. auto.
    - rewrite Reset_size_nice.
      projk_rewrite (Length_Loop_size_nice xs) 0.
      now rewrite CopyValue_size_nice'.
  Qed.

End Length_size_nice.
