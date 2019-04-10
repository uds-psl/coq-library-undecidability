Require Export PrettyBounds.

Require Export Code.CaseNat.
Require Export Code.CasePair.

Require Export TM.Code.CodeTM TM.Code.Copy.


(* This definition doesn't work, because we need the quantifier for all values after [(s: nat)] *)
(*
Definition dominatedWith_vec (n : nat) (f : Vector.t (nat->nat) n) (g : Vector.t (nat->nat) n) :=
  { c | forall (i : Fin.t n) (s : nat), f @>i s <=(c[@i]) g @>i s }.
*)


Require Import ListTM CaseList.

Require Export MaxList.


Fixpoint sum_list_rec (s : nat) (xs : list nat) :=
  match xs with
  | nil => s
  | x :: xs' => sum_list_rec (s + x) xs'
  end.

Lemma sum_list_rec_plus (s1 s2 : nat) (xs : list nat) :
  sum_list_rec (s1 + s2) xs = s1 + sum_list_rec s2 xs.
Proof.
  revert s1 s2. induction xs as [ | x xs IH]; intros; cbn in *.
  - reflexivity.
  - rewrite IH. rewrite IH. omega.
Qed.

Lemma sum_list_rec_S (s : nat) (xs : list nat) :
  sum_list_rec (S s) xs = S (sum_list_rec s xs).
Proof. change (S s) with (1 + s). apply sum_list_rec_plus. Qed.

Lemma sum_list_rec_ge (s : nat) (xs : list nat) :
  s <= sum_list_rec s xs.
Proof.
  induction xs as [ | x xs]; cbn in *.
  - reflexivity.
  - rewrite sum_list_rec_plus. omega.
Qed.


(*
Lemma Constr_pair_size_nice :
  { c | forall (s : nat) Constr_pair_size
*)

Global Arguments Encode_list_size {sigX X cX}.
Global Arguments size : simpl never.


(** Do something with the [k]th element in a chain of conjunctions *) 
Ltac projk_fix C H k :=
  lazymatch k with
  | 0 => C (proj1 H) + C H
  | 1 => projk_fix C (proj2 H) 0
  | S ?k' => projk_fix C (proj2 H) k'
  end.

(** Try to do something with every element in the chain of conjunctions *)
Ltac proj_fix C H :=
  lazymatch type of H with
  | ?P1 /\ ?P2 => C (proj1 H) + proj_fix C (proj2 H)
  | _ => C H
  end.

Tactic Notation "projk_rewrite"     constr(H) constr(k) := projk_fix ltac:(fun c => erewrite   c) H k.
Tactic Notation "projk_rewrite" "->" constr(H) constr(k) := projk_fix ltac:(fun c => erewrite <- c) H k.
Tactic Notation "projk_rewrite" "<-" constr(H) constr(k) := projk_fix ltac:(fun c => erewrite <- c) H k.

(** If we leave out the number, just try every proposition in the conjunction chain *)
Tactic Notation "projk_rewrite"     constr(H) := proj_fix ltac:(fun c => erewrite   c) H.
Tactic Notation "projk_rewrite" "->" constr(H) := proj_fix ltac:(fun c => erewrite -> c) H.
Tactic Notation "projk_rewrite" "<-" constr(H) := proj_fix ltac:(fun c => erewrite <- c) H.

Lemma tam : 42 = 40 + 2 /\ 50 = 25 + 25.
Proof. omega. Qed.

Goal 42 = 40 + 2.
Proof.
  projk_rewrite -> tam 0. reflexivity.
Restart.
  projk_rewrite tam. reflexivity.
Qed.

Lemma tam' : forall x, x - x = 0 /\ x + x = 2 * x.
Proof. intros. omega. Qed.

Goal 42 + 42 = 2 * 42.
Proof.
  projk_rewrite (tam' 42) 1. reflexivity.
Restart.
  projk_rewrite (tam' 42). reflexivity.
Qed.


(*
Module ApproachThatProbablyDoesntWork.

  (** [Length] *)
  Section Length_size_nice.
    Variable (sigX X : Type) (cX : codable sigX X).

    (* What do we actually want to prove? *)

    Lemma CaseList_size0_Reset_eq : forall (x : X) (xs : list X) (s : nat), (CaseList_size0 x >> Reset_size xs) s = 1 + s + size (x::xs).
    Proof. intros. rewrite Encode_list_hasSize. cbn. unfold Reset_size, CaseList_size0. ring_simplify. rewrite <- Encode_list_hasSize. nia. Qed.
    
    Lemma CaseList_size1_Reset_eq : forall (x : X) (s : nat), (CaseList_size1 x >> Reset_size x) s = Init.Nat.max s (1 + size x). (* [S (size x + (s - S (size x)))] *)
    Proof. intros. cbn. unfold Reset_size, CaseList_size1. nia. Qed.
    (* I think the above lemma is the only simplification we can do for [Length_Step_size] *)

    Lemma Length_Loop_size_nice (xs : list X) :
      (forall s0 : nat, (Length_Loop_size xs)@>Fin0 s0 = sum_list_rec s0 (map (fun x => 1 + size x) xs)) /\
      (forall s1 : nat, (Length_Loop_size xs)@>Fin1 s1 = s1 - length xs) /\
      (forall s2 : nat, (Length_Loop_size xs)@>Fin2 s2 = max_list_rec s2 (map (fun x => 1 + size x) xs)).
    Proof.
      repeat setoid_rewrite Encode_list_hasSize.
      induction xs as [ | x xs (IH0&IH1&IH2)].
      - split; [>|split]; cbn in *; intros.
        all: cbv [id]; nia.
      - repeat split; cbn in *; intros.
        + rewrite IH0. cbn. unfold CaseList_size0. f_equal. nia.
        + rewrite IH1. nia.
        + rewrite IH2. setoid_rewrite CaseList_size1_Reset_eq. f_equal. nia.
    Qed.


    Lemma Encode_list_size_eq_sum_list_rec (xs : list X) :
      Encode_list_size xs = sum_list_rec 1 (map (fun x => 1 + size x) xs).
    Proof.
      induction xs as [ | x xs IH]; cbn in *.
      - reflexivity.
      - rewrite IH. setoid_rewrite sum_list_rec_S at 2. replace (S (size x)) with (size x + 1) by omega. rewrite sum_list_rec_plus. omega.
    Qed.

    
    Print Length_size.

    (** We shouldn't touch this any more *)
    Local Arguments Length_Loop_size : simpl never.

    (** This lemma is not really nice... *)
    Lemma Length_size_nice' (xs : list X) :
      (forall s0 : nat, (Length_size xs)@>Fin0 s0 = s0) /\
      (forall s1 : nat, (Length_size xs)@>Fin1 s1 = s1 - 2 - length xs) /\
      (forall s2 : nat, (Length_size xs)@>Fin2 s2 = max_list_rec s2 (map (fun x => 1 + size x) xs)) /\
      (forall s3 : nat, (Length_size xs)@>Fin3 s3 = 1 + size nil + sum_list_rec (s3 - (1 + size xs)) (map (fun x => 1 + size x) xs)).
    Proof.
      unfold Length_size; cbn. intros. repeat split; intros.
      - rewrite (proj1 (proj2 (Length_Loop_size_nice xs))). unfold Constr_O_size. cbn. nia.
      - now rewrite (proj2 (proj2 (Length_Loop_size_nice xs))).
      - unfold Reset_size, CopyValue_size. now rewrite (proj1 (Length_Loop_size_nice xs)).
    Qed.

    Lemma tam : forall (xs : list X) (s2 : nat), max_list_rec s2 (map (fun x : X => 1 + size x) xs) <= Init.Nat.max s2 (size xs).
    Proof.
      repeat setoid_rewrite Encode_list_hasSize.
      induction xs as [ | x xs IH]; intros; cbn in *.
      - nia.
      - rewrite IH. nia.
    Qed.
      

    Lemma Length_size_nice (xs : list X) :
      (forall s0 : nat, (Length_size xs)@>Fin0 s0 = s0) /\
      (forall s1 : nat, (Length_size xs)@>Fin1 s1 <= s1 - size (length xs)) /\
      (forall s2 : nat, (Length_size xs)@>Fin2 s2 <= max s2 (size xs)) /\
      (forall s3 : nat, (Length_size xs)@>Fin3 s3 = 1 + size nil + sum_list_rec (s3 - (1 + size xs)) (map (fun x => 1 + size x) xs)) (*TODO*).
    Proof.
      repeat split; intros.
      - rewrite (proj1 (proj2 (Length_size_nice' xs))). rewrite Encode_nat_hasSize. nia.
      - rewrite (proj1 (proj2 (proj2 (Length_size_nice' xs)))). apply tam.
      - now rewrite (proj2 (proj2 (proj2 (Length_size_nice' xs)))).
    Qed.

  End Length_size_nice.

  Local Arguments skipn : simpl never.
    

  (** [Nth'] *)
  Section Nth'_size_nice.
    Variable (sigX X : Type) (cX : codable sigX X).

    Print Nth'_Loop_size.
    Print Nth'_Step_size.

    Lemma Nth'_Loop_size_nice (n : nat) :
      (forall xs s0, (Nth'_Loop_size n xs)@>Fin0 s0 = sum_list_rec s0 (map (fun x => 1 + size x) (firstn (S n) xs))) /\
      (forall xs s1, (Nth'_Loop_size n xs)@>Fin1 s1 <= max_list_rec s1 (map (fun x => 1 + size x) (firstn (n) xs))) /\ (* TODO *)
      (forall xs s2, (Nth'_Loop_size n xs)@>Fin2 s2 <= (Nth'_Loop_size n xs)@>Fin2 s2) (* TODO *).
    Proof.
      induction n as [ | n (IH0&IH1&IH2)]; intros; cbn in *.
      - repeat split; intros.
        + destruct xs as [ | x xs]; cbn.
          * unfold id. reflexivity.
          * unfold CaseList_size0. nia.
        + destruct xs as [ | x xs]; cbn; auto.
        + destruct xs as [ | x xs]; cbn; auto. (* TODO *)
      - repeat split; intros.
        + destruct xs as [ | x xs]; cbn.
          * unfold id. reflexivity.
          * change (skipn (S (S n)) (x :: xs)) with (skipn (S n) xs).
            rewrite IH0. unfold CaseList_size0. repeat rewrite !sum_list_rec_S + rewrite !sum_list_rec_plus. nia.
        + destruct xs as [ | x xs]; cbn; auto. (* TODO *)
          all: admit.
        + destruct xs as [ | x xs]; cbn; auto. (* TODO *)
    Abort.


  End Nth'_size_nice.


  Lemma CasePair_size0_Reset_eq (sigX sigY X Y : Type) (cX : codable sigX X) (cY : codable sigY Y) :
    forall (x : X) (y : Y) (s : nat), (CasePair_size0 x >> Reset_size y) s = 1 + s + size (x,y).
  Proof. intros. cbn. unfold Reset_size, CasePair_size0. rewrite Encode_pair_hasSize; cbn. nia. Qed.
  
  Lemma CasePair_size1_Reset_eq (sigX sigY X Y : Type) (cX : codable sigX X) (cY : codable sigY Y) :
    forall (x : X) (y : Y) (s : nat), (CasePair_size1 x >> Reset_size y) s = S (size y + (s - size x)). (* TODO: is there a term with [max] for this? *)
  Proof. intros. cbn. unfold Reset_size, CasePair_size1. nia. Qed.

  Section LookupAssociativeList_nice.
    Variable (sigX sigY : finType).
    Variable (X : eqType) (Y : Type) (cX : codable sigX X) (cY : codable sigY Y).


    Print Lookup_Loop_size.
    Print Lookup_Step_size.


    Lemma Lookup_Loop_size_nice (xs : list (X*Y)) :
      (forall x s0, Lookup_Loop_size xs x @>Fin0 s0 <= 1 + s0 + size xs) /\
      (forall x s1, Lookup_Loop_size xs x @>Fin1 s1 <= size x + max_list_rec s1 (map (fun xy => 1 + size (fst xy)) xs)) /\
      (forall x s2, Lookup_Loop_size xs x @>Fin2 s2 <= max s2 (size xs)) /\
      (forall x s3, Lookup_Loop_size xs x @>Fin3 s3 <= 1 + max s3 (size x + size xs))
    .
    Proof.
      rewrite Encode_list_hasSize.
      induction xs as [ | [x' y] xs (IH0&IH1&IH2&IH3)]; intros; cbn in *.
      - repeat split; intros; cbn in *.
        + unfold ResetEmpty1_size. cbn. nia.
        + unfold id. omega.
        + unfold id. nia.
        + unfold id. nia.
      - repeat split; intros; cbn in *.
        + decide (x=x') as [<-|Hdec]; cbn.
          * setoid_rewrite CaseList_size0_Reset_eq. rewrite !Encode_list_hasSize; cbn. ring_simplify. nia.
          * rewrite IH0. ring_simplify. unfold CaseList_size0. nia.
        + decide (x=x') as [<-|Hdec]; cbn.
          * unfold MoveValue_size_y. rewrite <- max_list_rec_ge. nia.
          * rewrite IH1. ring_simplify. unfold id. apply plus_le_compat_l. apply max_list_rec_monotone. nia.
        + decide (x=x') as [<-|Hdec]; cbn.
          * unfold MoveValue_size_x. unfold CasePair_size0. unfold CaseList_size1. rewrite !Encode_pair_hasSize; cbn. nia.
          * rewrite IH2. setoid_rewrite CasePair_size0_Reset_eq. unfold CaseList_size1. rewrite !Encode_pair_hasSize; cbn. nia.
        + decide (x=x') as [<-|Hdec]; cbn.
          * setoid_rewrite CasePair_size1_Reset_eq. rewrite Encode_pair_hasSize; cbn.
            transitivity (1 + max s3 (size x)); [ apply Nat.eq_le_incl; nia | ].
            ring_simplify. apply plus_le_compat_r. nia.
          * rewrite IH3. setoid_rewrite CasePair_size1_Reset_eq. rewrite Encode_pair_hasSize; cbn.
            ring_simplify. apply plus_le_compat_r.
            transitivity (max (1 + max s3 (size x')) (size x + Encode_list_size xs)); [ apply Nat.eq_le_incl; nia | ].
            apply Nat.max_le_compat.
            -- admit.
            -- try nia.
    Admitted. (* TODO *)

    Print Lookup_size.

  End LookupAssociativeList_nice.


End ApproachThatProbablyDoesntWork.



(** Another approach: consider the term [restSize + size(X)] *)

Lemma Constr_S_size_nice :
  forall (n : nat) (rest : nat),
    let k := rest + size n in (* [k] is the "total number of symbols" (w/o start/stop symbols) *)
    (pred rest) + size(1+n) = max k (size (S n)).
Proof.
  intros.
  transitivity ((k - size(n) - 1) + size(1 + n)).
  - subst k. rewrite !Encode_nat_hasSize. nia.
  - transitivity ((k - n - 2) + 2 + n).
    + subst k. rewrite !Encode_nat_hasSize. ring_simplify. nia.
    + rewrite Encode_nat_hasSize. nia.
Qed.
  
Lemma CaseNat_size_nice :
  forall (n : nat) (rest : nat),
    let k := rest + size n in
    (1 <= n -> S rest + size (pred n) = max k (size (pred n))) /\
    (n = 0 -> S rest + size (pred n) = 1 + k).
    (* (S rest + size (pred n) = k). *)
Proof.
  intros. subst k. repeat split.
  - intros. rewrite !Encode_nat_hasSize. ring_simplify. transitivity (rest + (max 1 n) + 1); [ nia | ]. nia.
  - intros ->. cbn. rewrite !Encode_nat_hasSize. nia.
  (* - rewrite !Encode_nat_hasSize.  *)
Qed.


Definition CaseNat_size (n : nat) (s : nat) :=
  match n with
  | 0 => s
  | _ => S s
  end.

Lemma CaseNat_size_nice' :
  forall (n : nat) (rest : nat),
    let k := rest + size n in
    CaseNat_size n rest + size (pred n) = max k (size (pred n)).
    (* (S rest + size (pred n) = k). *)
Proof.
  intros. subst. repeat split.
  destruct n; cbn.
  - subst k. rewrite !Encode_nat_hasSize. nia.
  - subst k. rewrite !Encode_nat_hasSize. nia.
Qed.


Lemma ConstrS_CaseNat_size_nice :
  forall (n : nat) (rest : nat),
    let k := rest + size n in
    (S >> pred) rest + size n = max k 1.
Proof.
  intros. cbn. destruct n; cbn.
  - subst k. rewrite !Encode_nat_hasSize. nia.
  - subst k. rewrite !Encode_nat_hasSize. nia.
Qed.

Lemma ConstrS_CaseNat_size_nice' :
  forall (n : nat) (rest : nat),
    let k := rest + size n in
    (CaseNat_size n >> pred) rest + size n <= max k 1.
Proof.
  intros. cbn. destruct n; cbn.
  - subst k. rewrite !Encode_nat_hasSize. nia.
  - subst k. rewrite !Encode_nat_hasSize. nia.
Qed.


*)