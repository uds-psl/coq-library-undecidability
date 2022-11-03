From Undecidability.Shared.Libs.PSL Require Export BasicDefinitions FinTypesDef.

(* ** Formalisation of finite types using canonical structures and type classes *)

Definition elem (F: finType) := @enum (type F) (class F).
#[export] Hint Unfold elem : core.
#[export] Hint Unfold class : core.

Lemma elem_spec (X: finType) (x:X) : x el (elem X).
Proof.
  apply countIn.  pose proof (enum_ok x) as H. unfold elem. lia. 
Qed.

#[export] Hint Resolve elem_spec : core.
#[export] Hint Resolve enum_ok : core.

#[global]
Instance Fin_eq_dec n : eq_dec (Fin.t n).
Proof.
  intros; hnf.
  destruct (Fin.eqb x y) eqn:E.
  - left. now eapply Fin.eqb_eq.
  - right. intros H. eapply Fin.eqb_eq in H. congruence.
Defined.

Definition finType_cc (X: finType) (p: X -> Prop) (D: forall x, dec (p x)) : (exists x, p x) -> {x | p x}.
Proof.
  intro H.
  assert(exists x, x el (elem X) /\ p x) as E by firstorder.
  pose proof (list_cc D E) as [x G].
  now exists x.
Defined.

Definition pickx (X: finType): X + (X -> False).
Proof.
  destruct X as [X [enum ok]]. induction enum.
  - right. intro x. discriminate (ok x).
  - tauto.
Defined.

(* Index is an injective function *)


Fixpoint  getPosition {E: eqType} (A: list E) x := match A with
                                                   | nil => 0
                                                   | cons x' A' => if Dec (x=x') then 0 else 1 + getPosition A' x end.

Lemma getPosition_correct {E: eqType} (x:E) A: if Dec (x el A) then forall z, (nth (getPosition A x) A z) = x else getPosition A x = |A |.
Proof.
  induction A;cbn.
  -repeat destruct Dec;tauto.
  -repeat destruct Dec;intuition; congruence.
Qed.

Lemma getPosition_nth (X:eqType) k (d :X) xs:
  dupfree xs ->
  k < length xs ->
  getPosition xs (nth k xs d) = k.
Proof.
  induction xs in k|-*. now cbn.
  intros H1 H2. inv H1.
  cbn. destruct k.
  -decide _. all:easy.
  -decide _.
   +subst a. cbn in H2. edestruct H3. eapply nth_In. lia.
   + cbn in H2. rewrite IHxs. all:try easy;lia.
Qed.

Definition index {F: finType} (x:F) := getPosition (elem F) x.

Lemma index_nth {F : finType} (x:F) y: nth (index x) (elem F) y = x.
Proof.
  unfold index, elem, enum.
  destruct F as [[X E] [A all_A]];cbn.
  pose proof (getPosition_correct x A) as H.
  destruct Dec. auto. apply notInZero in n. now setoid_rewrite all_A in n.
Qed.
 
Lemma injective_index (A: finType) (x1 x2 : A) : index x1 = index x2 -> x1 = x2.
Proof.
  destruct (elem A) eqn:E.
  - hnf. intros. assert (x1 el elem A) by eauto using elem_spec. rewrite E in H0. auto.
  - clear E. intros E.
    apply (f_equal (fun y => nth y (elem A) e)) in E.
    now rewrite !index_nth in E.
Qed.

Lemma index_le (A:finType) (x:A): index x < length (elem A).
Proof.
  unfold index.
  assert (H:x el elem A) by apply elem_spec.
  revert H.
  generalize (elem A). intros l H.
  induction l;cbn;[|decide _].
  -easy.
  -lia.
  -destruct H. congruence. apply IHl in H. lia.
Qed.

Lemma finite_n (F : finType) :
    { n & { f : F -> Fin.t n & { g : Fin.t n -> F | (forall i, f (g i) = i) /\ forall x, g (f x) = x }}}.
Proof.
  destruct (pickx F) as [z|f].
  - exists (length (elem F)).
    exists (fun x => Fin.of_nat_lt (index_le x)).
    exists (fun i => List.nth (proj1_sig (Fin.to_nat i)) (elem F) z).
    split.
    + intros i. apply Fin.to_nat_inj. rewrite Fin.to_nat_of_nat.
      cbn. destruct (Fin.to_nat i) as [n Hn].
      apply (getPosition_nth); [|easy].
      apply (NoDup_count_occ' (@eqType_dec F)).
      intros x _. rewrite <-count_count_occ. now apply enum_ok.
    + intros x. rewrite Fin.to_nat_of_nat. now apply index_nth.
  - exists 0, (fun x => match f x with end), (fun i => Fin.case0 _ i). split.
    + intros i. apply (Fin.case0 _ i).
    + intros x. destruct (f x).
Qed.

Lemma fintype_choice (F : finType) (Y : Type) (P : F -> Y -> Prop) :
  (forall x : F, exists y, P x y) -> exists f : F -> Y, forall x, P x (f x).
Proof.
  intros FE.
  enough (forall l, exists f : F -> Y, forall x : F, x el l -> P x (f x)) as H.
  { destruct (H (elem F)) as [f Hf]. eexists. now eauto using elem_spec. }
  intros l. destruct (pickx F) as [x'|f].
  2: { exists (fun x => match f x with end). intros x. destruct (f x). }
  induction l as [|x l [f Hf]].
  - destruct (FE x') as [y' _]. now exists (fun _ => y').
  - destruct (FE x) as [y Hxy]. exists (fun z => if Dec (x = z) then y else f z).
    intros z [?|?]; destruct (Dec _); now (congruence || auto).
Qed.
