(* * Maximum element in a list *)

From Undecidability Require Export TM.Util.Prelim TM.Util.ArithPrelim.

(* ** Basic lemmas about upper bounds *)

(* An upper bound of a list is either in the list, or it is not in the list and is a strict upper bound *)
Lemma upperBound_In (xs : list nat) (u : nat) :
  (forall x, In x xs -> x <= u) ->
  (In u xs) \/
  (~ In u xs /\ forall x, In x xs -> x < u).
Proof.
  intros HUb. induction xs as [ | x xs IH]; intros; cbn in *.
  - right. auto.
  - spec_assert IH as [IH | [IH1 IH2]] by auto.
    + auto.
    + decide (x = u) as [ <- | Hdec].
      * left. auto.
      * right. split.
        -- intros [<- | H]; congruence.
        -- intros y [-> | H].
           ++ specialize (HUb y ltac:(now left)). lia.
           ++ specialize (IH2 y H). lia.
Qed.

(* We assume that [M] is an upper bound of [s] and [xs]. We also assume that [M] is either in xs, or every element of [x] is smaller than [s]. Then, if [M] is actually a strict upper bound of [xs], then [s] is also a strict upper bound of [xs]. *)
Lemma strict_greatest_upper_bound : forall (xs : list nat) (M s : nat),
    (In M xs \/ (M = s /\ forall x, In x xs -> x <= s)) ->
    (s <= M) ->
    (forall x, In x xs -> x < M) ->
    (forall x, In x xs -> x < s).
Proof.
  intros xs. induction xs as [ | x xs IH]; intros M s HM1 Hs HM2 y Hy; cbn in *.
  - auto.
  - destruct Hy as [ <- | Hy].
    + destruct HM1 as [ [ <- | HM1] | (->&HM1)]; eauto.
      * exfalso. specialize (HM2 x ltac:(eauto)). nia.
      * rewrite HM2; eauto.
    + destruct HM1 as [ [ <- | HM1] | (->&HM1)]; eauto.
      exfalso. specialize (HM2 x ltac:(eauto)). nia.
Qed.



(* ** Tail Recursive Definition *)

(* Compute the maximum of a list and a start-value tail-recursively *)
Fixpoint max_list_rec (s : nat) (xs : list nat) { struct xs } : nat :=
  match xs with
  | nil => s
  | x :: xs' => max_list_rec (max x s) xs'
  end.

(* We can remove the tail-recursion *)
Lemma max_list_rec_max (xs : list nat) (s1 s2 : nat) :
  max_list_rec (max s1 s2) xs = max (max_list_rec s1 xs) (max_list_rec s2 xs).
Proof.
  induction xs as [ | x xs IH] in s1,s2|-*; cbn in *.
  - reflexivity.
  - rewrite Max.max_assoc. rewrite !IH. nia.
Qed.

(* If the list is not empty, and every element in the list is greater than start-values [s1] and [s2], then the choice of start-value [s1] or [s2] doesn't matter *)
Lemma max_list_rec_irrelevant (xs : list nat) (s1 s2 : nat) :
  xs <> nil ->
  (forall x, In x xs -> s1 <= x /\ s2 <= x) ->
  max_list_rec s1 xs = max_list_rec s2 xs.
Proof.
  induction xs as [ | x xs IH]; intros Hneq Hxs; cbn in *.
  - congruence.
  - pose proof (Hxs x ltac:(auto)) as [Hxs1 Hxs2].
    destruct xs as [ | x' xs].
    + cbn. nia.
    + rewrite !max_list_rec_max. rewrite IH; eauto. congruence.
Qed.

(* The maximum is always greater or equal than the start-value *)
Lemma max_list_rec_ge (xs : list nat) (s : nat) :
  s <= max_list_rec s xs.
Proof.
  induction xs as [ | x' xs IH] in s|-*; cbn.
  - reflexivity.
  - rewrite <- IH. nia.
Qed.

(* The maximum is greater or equal than every element in the list *)
Lemma max_list_rec_ge_el (xs : list nat) (s : nat) (x : nat) :
  In x xs ->
  x <= max_list_rec s xs.
Proof.
  induction xs as [ | x' xs IH] in s,x|-*; intros Hel; cbn in *.
  - tauto.
  - destruct Hel as [ <- | Hel].
    + rewrite max_list_rec_max. rewrite <- Nat.le_max_l. apply max_list_rec_ge.
    + rewrite max_list_rec_max. rewrite <- IH; eauto. nia.
Qed.

Corollary max_list_rec_ge_el_ge (xs : list nat) (s : nat) (x y : nat) :
  In y xs ->
  x <= y ->
  x <= max_list_rec s xs.
Proof. intros. rewrite <- (max_list_rec_ge_el _ H); eauto. Qed.


(* [max_list_rec] is monotone w.r.t. the start value *)
Lemma max_list_rec_monotone (xs : list nat) (s0 s1 : nat) :
  s0 <= s1 ->
  max_list_rec s0 xs <= max_list_rec s1 xs.
Proof.
  revert s0 s1. induction xs as [ | x' xs' IH]; intros; cbn in *.
  - assumption.
  - rewrite IH; eauto. nia.
Qed.

(* ... and also w.r.t. the lists *)
Lemma max_list_rec_monotone' (xs1 xs2 : list nat) (s0 s1 : nat) :
  (Forall2 le xs1 xs2) ->
  s0 <= s1 ->
  max_list_rec s0 xs1 <= max_list_rec s1 xs2.
Proof.
  intros H. revert s0 s1. induction H; intros; cbn.
  - assumption.
  - rewrite IHForall2. apply max_list_rec_monotone.
    instantiate (1 := Init.Nat.max x s0). all:nia. 
Qed.

(* [max_list_rec] is a lower bound of [z], if every element is smaller than [z]. *)
Lemma max_list_rec_lower_bound (xs : list nat) (s : nat) (z : nat) :
  s <= z ->
  (forall x, In x xs -> x <= z) ->
  max_list_rec s xs <= z.
Proof.
  revert s z. induction xs as [ | x xs IH]; intros s z Hz Hxs; cbn in *.
  - assumption.
  - pose proof (Hxs x ltac:(eauto)) as Hxs'.
    rewrite max_list_rec_max. rewrite !IH by eauto. nia.
Qed.

Corollary max_list_rec_max' (xs : list nat) (s1 s2 : nat) :
  max_list_rec (Init.Nat.max s1 s2) xs = Init.Nat.max s1 (max_list_rec s2 xs).
Proof.
  apply Nat.le_antisymm.
  - apply max_list_rec_lower_bound; eauto.
    + apply Nat.max_le_compat_l. apply max_list_rec_ge.
    + intros x Hx. rewrite <- Max.le_max_r. now apply max_list_rec_ge_el.
  - rewrite max_list_rec_max.
    apply Nat.max_le_compat; auto.
    apply max_list_rec_ge.
Qed.

Corollary max_list_rec_max'' (xs : list nat) (s1 s2 : nat) :
  max_list_rec (Init.Nat.max s1 s2) xs = Init.Nat.max (max_list_rec s1 xs) s2.
Proof.
  apply Nat.le_antisymm.
  - apply max_list_rec_lower_bound; eauto.
    + apply Nat.max_le_compat_r. apply max_list_rec_ge.
    + intros x Hx. rewrite <- Max.le_max_l. now apply max_list_rec_ge_el.
  - rewrite max_list_rec_max.
    apply Nat.max_le_compat; auto.
    apply max_list_rec_ge.
Qed.

Corollary max_list_rec_idem s xs :
  max_list_rec (max_list_rec s xs) xs = max_list_rec s xs.
Proof.
  apply Nat.le_antisymm.
  - apply max_list_rec_lower_bound; eauto. intros. now apply max_list_rec_ge_el.
  - apply max_list_rec_lower_bound; eauto.
    + now rewrite <- !max_list_rec_ge.
    + intros. rewrite <- max_list_rec_ge. now apply max_list_rec_ge_el.
Qed.

(* Either the maximum (with start-value [s]) is in the list, or it is equal to [s] and [s] is greater (or equal) than every element *)
Lemma max_list_rec_el_or_eq xs s :
  max_list_rec s xs el xs \/ max_list_rec s xs = s /\ (forall x : nat, x el xs -> x <= s).
Proof.
  revert s. induction xs as [ | x xs IH]; intros; cbn in *; eauto.
  rewrite !max_list_rec_max.
  assert (max_list_rec s xs <= max_list_rec x xs \/ max_list_rec x xs <= max_list_rec s xs) as [H|H] by lia.
  - rewrite !max_l by assumption.
    specialize (IH x) as [IH|[<- IH]].
    + left. eauto.
    + rewrite !max_list_rec_idem. auto.
  - rewrite !max_r by assumption.
    specialize (IH s) as [IH|[<- IH]].
    + left. eauto.
    + right. split.
      * apply max_list_rec_idem.
      * intros y [<-|Hy].
        -- rewrite <- H. apply max_list_rec_ge.
        -- now apply IH.
Qed.

(* This, is [max_list_rec s xs] is a strict upper bound, so is [s] *)
Corollary max_list_rec_gt xs s :
  (forall y : nat, y el xs -> y < max_list_rec s xs) ->
  forall y : nat, y el xs -> y < s.
Proof.
  intros.
  apply strict_greatest_upper_bound with (M := max_list_rec s xs) (xs := xs); eauto.
  - apply max_list_rec_el_or_eq.
  - apply max_list_rec_ge.
Qed.

(* ... and also [s] is equal to [max_list_rec s xs]. *)
Corollary max_list_rec_gt' xs s :
  (forall x : nat, x el xs -> x < max_list_rec s xs) ->
  max_list_rec s xs = s /\ (forall x : nat, x el xs -> x < s).
Proof.
  split.
  - revert H. generalize (max_list_rec_ge xs s) as L1.
    set (m := (max_list_rec s xs)). intros.
    enough (m <= s) by nia.
    apply max_list_rec_lower_bound; auto.
    intros x Hx.
    apply Nat.lt_le_incl.
    eapply max_list_rec_gt; eauto.
  - now apply max_list_rec_gt.
Qed.

(* To conclude, either the maximum is euqal to the start value (and s is a strict upper bound), or the maximum is actually in the list *)
Corollary max_list_rec_In (xs : list nat) (s : nat) :
  (max_list_rec s xs = s /\ forall x, In x xs -> x < s) \/
  In (max_list_rec s xs) xs.
Proof.
  pose proof @upperBound_In xs (max_list_rec s xs).
  spec_assert H as [H | [H1 H2]].
  - intros. now apply max_list_rec_ge_el.
  - now right.
  - left. now apply max_list_rec_gt'.
Qed.


(* ** Definition of the maximum of a list *)


(* We simply instantiate the accu to [0] *)
Definition max_list (xs : list nat) := max_list_rec 0 xs.

(* The main lemmas can be simplified now *)
Lemma max_list_ge (xs : list nat) (x : nat) :
  In x xs ->
  x <= max_list xs.
Proof. intros. unfold max_list. rewrite <- max_list_rec_ge_el; eauto. Qed.

Lemma max_list_lower_bound (xs : list nat) (z : nat) :
  (forall x, In x xs -> x <= z) ->
  max_list xs <= z.
Proof. intros. unfold max_list. apply max_list_rec_lower_bound. lia. auto. Qed.

Lemma max_list_monotone (f : nat -> nat) (xs : list nat) :
  (forall x, x <= f x) ->
  max_list xs <= max_list (map f xs).
Proof.
  intros. apply max_list_lower_bound.
  intros x Hx. rewrite H. apply max_list_ge. apply in_map_iff. eauto.
Qed.

(* If the list is not empty, then the maximum is in the list *)
Lemma max_list_In (xs : list nat) :
  xs <> nil ->
  In (max_list xs) xs.
Proof.
  destruct xs as [ | x xs]; [ congruence | intros _].
  pose proof max_list_rec_In (x :: xs) 0 as [ (_&Absurd) | NotSoAbsurd ].
  - exfalso. specialize (Absurd x ltac:(auto)). lia.
  - apply NotSoAbsurd.
Qed.


(* ** Maximum of a function *)

(* A size of a largest element in a list, w.r.t. to a size function *)
Section max_list_map.
  Variable (X : Type) (f : X -> nat).

  Definition max_list_map (xs : list X) := max_list (map f xs).

  (* This version may be useful sometimes *)
  Definition max_list_map_rec (s : nat) (xs : list X) := max_list_rec s (map f xs).

  Lemma max_list_map_ge (xs : list X) (x : X) :
    In x xs ->
    f x <= max_list_map xs.
  Proof. intros. unfold max_list_map. apply max_list_ge. apply in_map_iff. eauto. Qed.

  Lemma max_list_map_lower_bound (xs : list X) (z : nat) :
    (forall x, In x xs -> f x <= z) ->
    max_list_map xs <= z.
  Proof. intros. unfold max_list_map. apply max_list_lower_bound. intros ? (?&<-&?) % in_map_iff. auto. Qed.

  Lemma max_list_map_In (xs : list X) :
    xs <> nil ->
    exists x, f x = max_list_map xs /\ In x xs.
  Proof.
    intros Hnil.
    apply in_map_iff.
    apply max_list_In.
    destruct xs; cbn in *; congruence.
  Qed.

End max_list_map.

(* [max_list_map] is monotone w.r.t. the function *)
Lemma max_list_map_monotone (X : Type) (f1 f2 : X -> nat) (xs : list X) :
  (forall (x : X), In x xs -> f1 x <= f2 x) ->
  max_list_map f1 xs <= max_list_map f2 xs.
Proof.
  intros. unfold max_list_map. apply max_list_lower_bound.
  intros ? (x&<-&?) % in_map_iff. rewrite H. apply max_list_ge. apply in_map_iff. eauto. auto.
Qed.
