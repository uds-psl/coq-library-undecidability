(** * PrettyBounds for Machines in TM/Code *)

Require Export TM.PrettyBounds.PrettyBounds.
Require Export TM.Code.ProgrammingTools.
Require Export TM.Code.ListTM TM.Code.CaseList TM.Code.CaseNat TM.Code.CaseSum.


(** We want to give proofs without building constants/the need to manually unfold "_ <=( _ ) _" *)
(** So every intermediate goal shall have the shape "x <=(?c) y", and we use lemmas to simplify this depending on the shape of x *)
(* Sadly, this approach works only for non-recursive functions*)

Section CaseList_nice.

  Variable (sigX X : Type) (cX : codable sigX X).

  Lemma CaseList_steps_nice :
    { c | forall xs, CaseList_steps xs
                <=(c) match xs with
                     | nil => 1
                     | x :: _ => size x + 1
                     end }.
  Proof. eexists. intros. unfold CaseList_steps, CaseList_steps_nil,CaseList_steps_cons. domWith_approx. Qed.

  Lemma CaseList_steps_nil_nice :
    { c | CaseList_steps_nil <=(c) 1 }.
  Proof. eexists. apply dominatedWith_const. omega. Qed.

  Lemma CaseList_steps_cons_nice :
    { c | forall (x : X), CaseList_steps_cons x <=(c) size x + 1 }.
  Proof. eexists. intros. unfold CaseList_steps_cons. domWith_approx. Qed.

  Lemma Constr_nil_steps_nice :
    { c | Constr_nil_steps <=(c) 1 }.
  Proof. eexists. domWith_approx. Qed.

  Lemma Constr_cons_steps_nice :
    { c | forall (x : X), Constr_cons_steps x <=(c) size x + 1 }.
  Proof. eexists. intros. unfold Constr_cons_steps. domWith_approx. Qed.

End CaseList_nice.

Section CaseNat_steps_nice.

  Lemma CaseNat_steps_nice :
    { c | CaseNat_steps <=(c) 1 }.
  Proof. eexists. apply dominatedWith_const. omega. Qed.

  Lemma Constr_O_steps_nice :
    { c | Constr_O_steps <=(c) 1 }.
  Proof. eexists. apply dominatedWith_const. omega. Qed.

  Lemma Constr_S_steps_nice :
    { c | Constr_S_steps <=(c) 1 }.
  Proof. eexists. apply dominatedWith_const. omega. Qed.

End CaseNat_steps_nice.


(** Sadly, we need more ugly approach for recursive functions: *)

Section encodeList_size_eq.
  Variable X : Type.
  Variable sigX : Type.
  Context {cX : codable sigX X}.

  Lemma encodeList_size_app (l1 l2 : list X) :
    size (l1 ++ l2) <= size l1 + size l2.
  Proof.
    rewrite !Encode_list_hasSize in *.
    cbn. induction l1;cbn. eauto. cbn. cbn. autorewrite with list. omega.
  Qed.

  Lemma encodeList_size_app_eq (l1 l2 : list X) :
    size (l1 ++ l2) = size l1 + size l2 - 1.
  Proof.
    rewrite !Encode_list_hasSize in *.
    cbn. induction l1;cbn. omega. autorewrite with list. rewrite IHl1.
    assert ((Encode_list_size cX l2) > 0) by (induction l2;cbn;omega). omega.
  Qed.

  Lemma encodeList_size_cons  x (l : list X) :
    size (x::l) = 1 + size x + size l.
  Proof.
    rewrite !Encode_list_hasSize in *.
    cbn. unfold size. autorewrite with list. omega.
  Qed.

  Lemma encodeList_size_nil:
    size (@nil X) = 1.
  Proof.
    rewrite !Encode_list_hasSize in *.
    reflexivity.
  Qed.

End encodeList_size_eq.

Create HintDb size_eqs.
Hint Rewrite encodeList_size_app encodeList_size_cons encodeList_size_nil encodeList_size_app: size_eqs.

Ltac rewrite_sizes := rewrite_strat (innermost (hints size_eqs)).


(** ** Copy steps functions *)

(* Copy steps functions are very nice! *)
Section Copy_very_nice.
  Variable (sigX X : Type) (cX : codable sigX X).

  (* This holds for every encoding. We should maybe add this to the typeclass. *)
  Hypothesis (sizeGt1 : forall (x : X), 1 <= size x).

  Lemma CopyValue_steps_nice :
    { c | forall x, CopyValue_steps x <=(c) size x + 1 }.
  Proof.
    eexists. intros x. unfold CopyValue_steps. domWith_approx.
    (*
    - apply dominatedWith_const; auto.
    - apply dominatedWith_refl. instantiate (1 := 1). omega.
*)
  Qed.

  Lemma Reset_steps_nice :
    { c | forall x, Reset_steps x <=(c) size x + 1 }.
  Proof.
    eexists. intros x. unfold Reset_steps. domWith_approx.
    (*
    - apply dominatedWith_const; auto.
    - apply dominatedWith_refl. instantiate (1 := 1). omega.
*)
  Qed.

  Lemma Translate_steps_nice :
    { c | forall x, Translate_steps x <=(c) size x + 1 }.
  Proof. eexists. intros x. unfold Translate_steps. domWith_approx. Qed.

  Variable (sigY Y : Type) (cY : codable sigY Y).
  Hypothesis (sizeGt1' : forall (y : Y), 1 <= size y).

  Lemma MoveValue_steps_nice :
    { c | forall (x : X) (y : Y), MoveValue_steps x y <=(c) size x + size y + 1 }.
  Proof.
    eexists. intros x y. unfold MoveValue_steps. domWith_approx.
  Qed.

  (* "Better" version *)
  Lemma MoveValue_steps_nice' :
    { c | forall (x : X) (y : Y), MoveValue_steps x y <=(c) size x + size y }.
  Proof.
    eexists. intros x y. unfold MoveValue_steps.
    rewrite <- Nat.add_assoc. eapply dominatedWith_add_l.
    - apply dominatedWith_add.
      + apply dominatedWith_mult_l. apply dominatedWith_solve.
        enough (1 <= size y) by omega. apply sizeGt1'.
      + apply dominatedWith_mult_l. apply dominatedWith_solve.
        enough (1 <= size x) by omega. apply sizeGt1.
    - enough (1 <= size x) by omega. apply sizeGt1.
  Qed.

End Copy_very_nice.




(** With this set-up, we can tackle recursive functions. *)

Arguments size {sig X cX} : simpl never.



Section Nth'_nice.
  Variable (sigX X : Type) (cX : codable sigX X).

  (*
  Lemma Nth'_Step_steps_nice :
    { c | forall (xs : list X) (n : nat), Nth'_Step_steps xs n <=(c) size _ xs }.
  Proof.
    evar (c:nat). exists c.
    intros. unfold Nth'_Step_steps.
    apply dominatedWith_match_nat.
    - intros ->. apply dominatedWith_match_list.
      + intros ->. cbn. unfold dominatedWith. unfold CaseList_steps_nil. do 11 instantiate (1 := S _). instantiate (1 := 0). omega.
      + intros x xs' ->. unfold CaseNat_steps, CaseList_steps_cons. hnf. rewrite Encode_list_hasSize. cbn [Encode_list_size].
        ring_simplify. instantiate (1 := 48). lia.
    - intros x ->. apply dominatedWith_match_list.
      + intros ->. ring_simplify. rewrite Encode_list_hasSize; cbn [Encode_list_size].
        apply dominatedWith_const. omega.
      + intros x' xs' ->. rewrite Encode_list_hasSize; cbn [Encode_list_size].
        unfold CaseList_steps_cons, Reset_steps, CaseNat_steps. ring_simplify. instantiate (1 := 100). hnf. ring_simplify. nia.
  Qed.
*)

  Lemma Nth'_Step_steps_nice_nil :
    { c | forall (n : nat), Nth'_Step_steps nil n <=(c) 1 }.
  Proof.
    evar (c:nat). exists c.
    intros. unfold Nth'_Step_steps. apply dominatedWith_match_nat.
    - intros ->. unfold CaseNat_steps, CaseList_steps_cons. ring_simplify. hnf. apply dominatedWith_const. omega.
    - intros n' ->. unfold CaseNat_steps, CaseList_steps_cons. ring_simplify. hnf. apply dominatedWith_const. omega.
  Qed.

  Lemma Nth'_Step_steps_nice_cons :
    { c | forall (x : X) (xs : list X) (n : nat), Nth'_Step_steps (x :: xs) n <=(c) size x+1 }.
  Proof.
    evar (c:nat). exists c.
    intros. unfold Nth'_Step_steps. apply dominatedWith_match_nat.
    - intros ->. unfold CaseNat_steps, CaseList_steps_cons. ring_simplify. hnf. instantiate (1 := 57). nia.
    - intros n' ->. unfold CaseNat_steps, CaseList_steps_cons, Reset_steps. ring_simplify. hnf. instantiate (1 := 57). ring_simplify. nia.
  Qed.

  Lemma max_plus_l a b c :
    max a (c + max b a) <= c + max b a.
  Proof.
    assert (a <= b \/ b <= a) as [H | H] by omega.
    - replace (max b a) with b.
      rewrite max_r by omega. omega.
      now rewrite max_l by omega.
    - replace (max b a) with a.
      rewrite max_r by omega. omega.
      now rewrite max_r by omega.
  Qed.

  Lemma Nth'_Loop_steps_nice :
    { c | forall (xs : list X) (n : nat), Nth'_Loop_steps xs n <=(c) size xs }.
  Proof.
    pose_nice Nth'_Step_steps_nice_nil  HStep_nil  c_nil.
    pose_nice Nth'_Step_steps_nice_cons HStep_cons c_cons.
    pose (c := 1 + max c_nil c_cons).
    exists c.
    intros xs. induction xs as [ | x xs' IH]; intros.
    - eapply dominatedWith_mono_c. cbn [Nth'_Loop_steps].
      destruct n; apply HStep_nil. constructor; apply Max.le_max_l || auto with arith. (* Why is [rewrite Max.le_max_l] not working? *)
    - cbn [Nth'_Loop_steps]. eapply dominatedWith_mono_c; [..|shelve]. eapply dominatedWith_match_nat.
      + intros ->. hnf.
        specialize (HStep_cons x xs' 0).
        instantiate (1 := c_cons). rewrite Encode_list_hasSize; cbn [Encode_list_size]. ring_simplify. lia.
      + intros n' ->. hnf.
        specialize (HStep_cons x xs' (S n')).
        instantiate (1 := c). rewrite Encode_list_hasSize; cbn [Encode_list_size].
        rewrite HStep_cons. specialize (IH n'). hnf in IH. rewrite IH. ring_simplify. rewrite Encode_list_hasSize; cbn [Encode_list_size].
        ring_simplify. subst c. nia.
    Unshelve.
    apply max_plus_l.
  Qed.


  (* Three different proofs! I consider only the third compositional, because we don't unfold any constants. *)
  Lemma Nth'_steps_nice :
    { c | forall (xs : list X) (n : nat), Nth'_steps xs n <=(c) size xs + n + 1 }.
  Proof.
    pose_nice Nth'_Loop_steps_nice H c.
    eexists. intros xs n. specialize (H xs n).
    hnf. unfold Nth'_steps. ring_simplify.
    (* At this point, ultimate domination would be better, because we would not have to look in the values of [CopyValue_steps] and [Reset_steps], because we already know that they are Θ(size _ xs). Below, [28] has been chosen in dependence of these constants. *)
    unfold CopyValue_steps, Reset_steps.
    instantiate (1 := 12 + c + 4 + 4 + _).
    rewrite !Encode_list_hasSize. rewrite Encode_list_hasSize_skipn.
    rewrite Encode_nat_hasSize. rewrite H, Encode_list_hasSize.
    ring_simplify.
    assert (n - (1 + |xs|) <= n) as H' by omega; rewrite H'; clear H'.
    (* Encode_list_size cX xs * c + 16 * Encode_list_size cX xs + 4 * n + 48 <=
       Encode_list_size cX xs * c + Encode_list_size cX xs * ?m + 20 * Encode_list_size cX xs + c * n + c + ?m * n + ?m + 20 * n + 20 *)
    instantiate (1 := 28).
    nia.
  Restart.
    (* Another proof with more automation *)
    pose_nice Nth'_Loop_steps_nice H c.
    eexists. intros xs n. specialize (H xs n).
    hnf. unfold Nth'_steps.
    repeat eapply dominatedWith_add.
    (* Compositional part is more or less automatic *)
    all: ring_simplify.
    (* The second tactic can solve more and is faster *)
    all: domWith_approx.
    all: try solve [ eauto | apply dominatedWith_const; omega | apply dominatedWith_solve; omega
                   | eapply dominatedWith_trans; eauto; apply dominatedWith_solve; omega ].
    (* Specific part for [Nth'] *)
    1-4: apply dominatedWith_solve; rewrite !Encode_list_hasSize; etransitivity; [ apply (Encode_list_hasSize_skipn _ xs (1+n)) | omega ].
    1-4: assert (1 <= size xs) by (rewrite Encode_list_hasSize; apply Encode_list_hasSize_ge1);
      apply dominatedWith_solve; rewrite Encode_nat_hasSize; omega.
  Restart.
    (* Another proof with more automation *)
    pose_nice Nth'_Loop_steps_nice H c.
    eexists. intros xs n. specialize (H xs n).
    hnf. unfold Nth'_steps.
    (* Automated Compositionality! *)
    domWith_approx.
    - eapply dominatedWith_trans.
      apply (proj2_sig (@CopyValue_steps_nice _ _ (Encode_list cX))).
      domWith_approx.
    - eapply dominatedWith_trans.
      eauto. domWith_approx.
    - eapply dominatedWith_trans.
      apply (proj2_sig (@Reset_steps_nice _ _ (Encode_list cX))).
      (* This is the [Nth']-specific complication *)
      apply dominatedWith_S''.
      2: omega.
      2: { apply dominatedWith_solve. rewrite !Encode_list_hasSize.
           hnf. rewrite Encode_list_hasSize_skipn. omega. }
      pose proof (Encode_list_hasSize_ge1 _ xs). rewrite Encode_list_hasSize. omega.
    - eapply dominatedWith_trans.
      apply (proj2_sig (@Reset_steps_nice _ _ Encode_nat)).
      (* This is the [Nth']-specific complication *)
      apply dominatedWith_S''.
      2: omega.
      2: { apply dominatedWith_solve. rewrite !Encode_list_hasSize. rewrite Encode_nat_hasSize.
           pose proof (Encode_list_hasSize_ge1 _ xs). omega. }
      pose proof (Encode_list_hasSize_ge1 _ xs). rewrite Encode_list_hasSize. omega.
  Qed.

End Nth'_nice.

Print Assumptions Nth'_steps_nice.


Section Length_steps_nice.

  Variable (sigX X : Type) (cX : codable sigX X).

  Print Length_Step_steps.

  Lemma Length_Step_steps_nice_nil :
    {c | Length_Step_steps nil <=(c) 1 }.
  Proof. eexists. cbn. intros. apply dominatedWith_const. omega. Qed.

  Lemma Length_Step_steps_nice_cons :
    {c | forall (xs : list X) (x : X), Length_Step_steps (x :: xs) <=(c) size x + 1 }.
  Proof.
    pose_nice (CaseList_steps_nice cX) Hc_CaseList c_CaseList.
    pose_nice (Reset_steps_nice cX) Hc_Reset c_Reset.
    eexists. intros. cbn.
    ring_simplify. domWith_approx.
    - apply (Hc_CaseList [x]).
    - apply Hc_Reset.
  Qed.

  Lemma Length_Loop_steps_nice :
    { c | forall (xs : list X), Length_Loop_steps xs <=(c) size xs }.
  Proof.
    pose_nice Length_Step_steps_nice_nil Hc_nil c_nil.
    pose_nice Length_Step_steps_nice_cons Hc_cons c_cons.
    pose (c := 1 + max c_nil c_cons). exists c.
    setoid_rewrite Encode_list_hasSize; cbn [Encode_list_size].
    induction xs as [ | x xs' IH].
    - eapply dominatedWith_mono_c. apply Hc_nil. subst c. lia.
    - specialize Hc_cons with (xs := xs').
      (* eapply dominatedWith_mono_c; [..|shelve]. *)
      hnf. cbn [Length_Loop_steps]. rewrite (Hc_cons x). ring_simplify.
      (* instantiate (1 := c). *) subst c. ring_simplify.
      hnf in IH. cbn. rewrite IH. ring_simplify.
      enough (c_cons * size x + c_cons <=
              size x * Init.Nat.max c_nil c_cons + size x +
              Init.Nat.max c_nil c_cons) by omega.
      enough (c_cons * size x <=
              size x * Init.Nat.max c_nil c_cons + size x) by lia.
      enough (c_cons * size x <= size x * max c_nil c_cons) by omega.
      Fail enough (c_cons <= max c_nil c_cons) by lia.
      rewrite Nat.mul_comm.
      apply Nat.mul_le_mono_l.
      auto with arith.
      (* TODO: This needs to be more automated! *)
  Qed.

  Lemma Length_steps_nice :
    { c | forall (xs : list X), Length_steps xs <=(c) size xs }.
  Proof.
    pose_nice Length_Loop_steps_nice Hc_loop c_loop.
    eexists. intros.
    unfold Length_steps. (* ring_simplify. *)
    (* This OUGHT to be easy! https://xkcd.com/1349/ *)
    (* 36 + 12 * size (Encode_list cX) xs + Length_Loop_steps xs <=(?c)
       size (Encode_list cX) xs *)
    rewrite <- Nat.add_assoc. eapply dominatedWith_add_l.
    2:{ rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1. }
    domWith_approx.
    - hnf. apply Hc_loop.
  Qed.


End Length_steps_nice.

Section App_nice.
  Variable (sigX X : Type) (cX : codable sigX X).

  Lemma App'_steps_nice :
    { c | forall (xs : list X), App'_steps xs <=(c) size xs }.
  Proof.
    eexists. intros xs. unfold App'_steps.
    eapply dominatedWith_add_l.
    - domWith_approx.
    - rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1.
  Qed.

  (* [App] is not used *)
End App_nice.


Lemma Encode_pair_hasSize_ge1 (sigX sigY X Y : Type) (cX : codable sigX X) (cY : codable sigY Y) (p : X * Y) :
  1 <= size (fst p) \/ 1 <= size (snd p) ->
  1 <= Encode_pair_size _ _ p.
Proof. destruct p as (x,y). cbn in *. intros [H|H]; cbn; rewrite H; omega. Qed.

Lemma Encode_nat_hasSize_ge1 (n : nat) :
  1 <= size n.
Proof. rewrite Encode_nat_hasSize. omega. Qed.

Lemma Encode_option_hasSize_ge1 (sigX X : Type) (cX : codable sigX X) (o : option X) :
  1 <= Encode_option_size _ o.
Proof. destruct o; cbn; omega. Qed.

(** *** CasePair *)

Require Import CasePair.

Section CasePair_steps_nice.
  Variable (sigX X : Type) (cX : codable sigX X).

  Lemma CasePair_steps_nice :
    { c | forall (x : X), CasePair_steps x <=(c) size x + 1 }.
  Proof. eexists. intros. unfold CasePair_steps. domWith_approx. Qed.

  Lemma Constr_pair_steps_nice :
    { c | forall (x : X), Constr_pair_steps x <=(c) size x + 1 }.
  Proof. eexists. intros. unfold Constr_pair_steps. domWith_approx. Qed.

End CasePair_steps_nice.

(** *** CaseSum and CaseOption *)

Require Import CaseSum.

Section CaseSum_steps_nice.

  Lemma CaseSum_steps_nice :
    { c | CaseSum_steps <=(c) 1 }.
  Proof. eexists. unfold CaseSum_steps. domWith_approx. Qed.

  Lemma Constr_inl_steps_nice :
    { c | Constr_inl_steps <=(c) 1 }.
  Proof. eexists. unfold Constr_inl_steps. domWith_approx. Qed.

  Lemma Constr_inr_steps_nice :
    { c | Constr_inr_steps <=(c) 1 }.
  Proof. eexists. unfold Constr_inr_steps. domWith_approx. Qed.

  Lemma CaseOption_steps_nice :
    { c | CaseOption_steps <=(c) 1 }.
  Proof. eexists. unfold CaseOption_steps. domWith_approx. Qed.

  Lemma Constr_Some_steps_nice :
    { c | Constr_Some_steps <=(c) 1 }.
  Proof. eexists. unfold Constr_Some_steps. domWith_approx. Qed.

  Lemma Constr_None_steps_nice :
    { c | Constr_None_steps <=(c) 1 }.
  Proof. eexists. unfold Constr_None_steps. domWith_approx. Qed.

End CaseSum_steps_nice.

Lemma Encode_list_hasSize_el (sigX X : Type) (cX : codable sigX X) (xs : list X) (x : X) :
  In x xs ->
  size x < Encode_list_size _ xs.
Proof.
  induction xs as [ | x' xs' IH].
  - intros [].
  - intros [<- | H].
    + cbn. omega.
    + specialize IH with (1 := H). cbn. omega.
Qed.




(** *** CompareValue(s) *)
Require Import Code.CompareValue.

Section CompareValues_nice.

  Variables (sigX X : Type) (cX : codable sigX X).

  Lemma CompareValues_steps_nice :
    { c | forall (x1 x2 : X), CompareValues_steps x1 x2 <=(c) size x1 + size x2 + 1 }.
  Proof. eexists. intros. unfold CompareValues_steps. domWith_approx. Qed.

End CompareValues_nice.

