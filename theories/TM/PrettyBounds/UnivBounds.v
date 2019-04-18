(** * PrettyBound for Univ *)


From Undecidability Require Import TM.PrettyBounds.PrettyBounds.
From Undecidability Require Import TM.PrettyBounds.BaseCode.


Lemma Encode_list_hasSize_gt_length (sigX X : Type) (cX : codable sigX X) (xs : list X) :
  length xs < Encode_list_size _ xs.
Proof. induction xs as [ | x xs' IH]; cbn in *; omega. Qed.

Lemma Encode_list_hasSize_ge_length (sigX X : Type) (cX : codable sigX X) (xs : list X) :
  length xs <= Encode_list_size _ xs.
Proof. apply Nat.lt_le_incl. apply Encode_list_hasSize_gt_length. Qed.


(** *** Assoc List Lookup *)


(* Don't [Import] it globally here, or there will be name clashes with LM Lookup *)
From Undecidability Require Univ.LookupAssociativeListTM Univ.StepTM.


Module Univ_nice.

  Import Univ.LookupAssociativeListTM.

  Section LookupAssociativeList_nice.

    Variable (sigX sigY : Type) (X : eqType) (Y : Type) (cX : codable sigX X) (cY : codable sigY Y).

    Lemma Lookup_Step_steps_Compare_nice :
      { c | forall (x x' : X) (y : Y) (xs : list (X * Y)),
          Lookup_Step_steps_Compare x x' y xs
          <=(c)
             if Dec (x=x')
             then size x + size y + size xs + 1
             else size x' + size y + 1 }.
    Proof.
      eexists. intros. unfold Lookup_Step_steps_Compare. domWith_match.
      - subst. clear H. ring_simplify. domWith_approx.
        + eapply dominatedWith_trans. eapply (proj2_sig (MoveValue_steps_nice cY cX) y x'). apply dominatedWith_solve. omega.
        + eapply dominatedWith_trans. eapply (proj2_sig (Reset_steps_nice _)). apply dominatedWith_solve. omega.
        + eapply dominatedWith_trans. eapply (proj2_sig (Reset_steps_nice _)). apply dominatedWith_solve. omega.
      - ring_simplify. domWith_approx.
        + eapply dominatedWith_trans. eapply (proj2_sig (Reset_steps_nice _)). apply dominatedWith_solve. omega.
        + eapply dominatedWith_trans. eapply (proj2_sig (Reset_steps_nice _)). apply dominatedWith_solve. omega.
    Qed.

    Lemma Lookup_Step_steps_CaseList_nice :
      { c | forall (xs : list (X * Y)) (x : X),
          Lookup_Step_steps_CaseList xs x
          <=(c)
             match xs with
             | [] => 1
             | (x', y) :: xs' =>
               if Dec (x=x')
               then size x + size y + size xs + 1
               else size x + size x' + size y + 1
             end }.
    Proof.
      eexists. intros. unfold Lookup_Step_steps_CaseList. domWith_match. domWith_approx. rename H into EqXs, xs0 into xs'. destruct x0 as (x',y).
      ring_simplify. apply dominatedWith_add_r. 1: domWith_approx.
      - eapply dominatedWith_trans. apply (proj2_sig (CompareValues_steps_nice _)). decide (x = x') as [ -> | Hd].
        + apply dominatedWith_solve. rewrite Encode_list_hasSize. cbn. rewrite Encode_pair_hasSize. cbn. omega.
        + apply dominatedWith_solve. omega.
      - eapply dominatedWith_trans. apply (proj2_sig (CasePair_steps_nice _)). decide (x = x') as [ -> | Hd].
        + apply dominatedWith_solve. rewrite Encode_list_hasSize. cbn. rewrite Encode_pair_hasSize. cbn. omega.
        + apply dominatedWith_solve. omega.
      - eapply dominatedWith_trans. apply (proj2_sig Lookup_Step_steps_Compare_nice). decide (x = x') as [ -> | Hd].
        + apply dominatedWith_solve. setoid_rewrite Encode_list_hasSize. cbn. rewrite Encode_pair_hasSize. cbn. ring_simplify. omega.
        + apply dominatedWith_solve. omega.
      - decide (x = x') as [ -> | Hd]; omega.
    Qed.

    Lemma Lookup_Step_steps_nice :
      { c | forall (xs : list (X * Y)) (x : X),
          Lookup_Step_steps xs x
          <=(c)
             match xs with
             | [] => 1
             | (x', y) :: xs' =>
               if Dec (x=x')
               then size x + size y + size xs + 1
               else size x + size x' + size y + 1
             end }.
    Proof.
      eexists. intros. unfold Lookup_Step_steps. ring_simplify. apply dominatedWith_add_r. 1: domWith_approx.
      - eapply dominatedWith_trans. apply (proj2_sig (CaseList_steps_nice _)). destruct xs as [ | (x',y) ? ].
        + domWith_approx.
        + apply dominatedWith_solve. rewrite Encode_list_hasSize. cbn. rewrite Encode_pair_hasSize. cbn. decide (x = x') as [ -> | Hd]; omega.
      - eapply dominatedWith_trans. apply (proj2_sig (Lookup_Step_steps_CaseList_nice)). destruct xs as [ | (x',y) ? ].
        + domWith_approx.
        + apply dominatedWith_solve. rewrite Encode_list_hasSize. cbn. rewrite Encode_pair_hasSize. cbn. decide (x = x') as [ -> | Hd]; omega.
      - destruct xs as [ | (x',y) ? ]. omega. decide (x = x') as [ -> | Hd]; omega.
    Qed.

    Lemma Lookup_Step_steps_nice' :
      { c | forall (xs : list (X * Y)) (x : X),
          Lookup_Step_steps xs x
          <=(c)
             match xs with
             | [] => 1
             | (x', y) :: xs' =>
               if Dec (x=x')
               then (size x + 1) + size xs (* Size of the full list *)
               else (size x + 1) + size (x', y) (* Size of the head *)
             end }.
    Proof.
      eexists. intros. eapply dominatedWith_trans. apply (proj2_sig Lookup_Step_steps_nice).
      domWith_match.
      - domWith_approx.
      - rename xs0 into xs'. destruct x0 as (x',y).
        decide (x = x') as [-> | Hd].
        + rewrite Encode_list_hasSize. cbn. rewrite Encode_pair_hasSize. cbn. ring_simplify. domWith_approx.
        + hnf. rewrite Encode_pair_hasSize. cbn. omega.
    Qed.

    Lemma Lookup_Loop_steps_eq (x : X) (xs : list (X*Y)) :
      Lookup_Loop_steps x xs =
      match xs with
      | nil => Lookup_Step_steps xs x
      | (x',y) :: xs' => if Dec(x=x')
                        then Lookup_Step_steps xs x
                        else 1 + Lookup_Step_steps xs x + Lookup_Loop_steps x xs'
      end.
    Proof. now destruct xs. Qed.

    Lemma Lookup_Loop_steps_nice' :
      { c | forall (x : X) (xs : list (X*Y)), Lookup_Loop_steps x xs <=(c) (size x + 1) * (size xs + 1) }.
    Proof.
      pose_nice Lookup_Step_steps_nice' Hc_Step c_Step.
      exists (c_Step + 1). intros. induction xs as [ | (x',y) xs' IH]; cbn [Lookup_Step_steps] in *.
      - rewrite Lookup_Loop_steps_eq. eapply dominatedWith_mono_c; [..|shelve].
        eapply dominatedWith_trans.
        + hnf. apply Hc_Step.
        + apply dominatedWith_solve. unfold size. cbn. omega.
          Unshelve. omega.
      - rewrite Lookup_Loop_steps_eq. specialize (Hc_Step ((x',y) :: xs') x). cbn [Lookup_Loop_steps] in *. decide (x = x') as [ Heq | Hd].
        + hnf. rewrite Hc_Step. ring_simplify. clear_all. nia.
        + hnf. rewrite Hc_Step. hnf in IH. rewrite IH. ring_simplify. rewrite !Encode_list_hasSize. cbn. ring_simplify. clear_all. nia.
    Qed.

    (* Hypothesis (size_X_ge1 : forall (x : X), 1 <= size x). *)

    Lemma Lookup_Loop_steps_nice :
      { c | forall (x : X) (xs : list (X*Y)), Lookup_Loop_steps x xs <=(c) (size x + 1) * size xs }.
    Proof.
      eexists. intros. eapply dominatedWith_trans. apply (proj2_sig Lookup_Loop_steps_nice'). ring_simplify. domWith_approx.
      - apply dominatedWith_solve. enough (1 <= size xs) by nia. rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1.
      (* - apply dominatedWith_solve. enough (1 <= size x) by nia. apply size_X_ge1. *)
      - apply dominatedWith_solve. enough (1 <= size xs) by nia. rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1.
      (* - apply dominatedWith_solve. enough (1 <= size x /\ 1 <= size xs) by nia. split.
        + apply size_X_ge1.
        + rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1. *)
    Qed.

    Lemma Lookup_steps_nice :
      { c | forall (x : X) (xs : list (X*Y)), Lookup_steps x xs <=(c) (size x + 1) * size xs }.
    Proof.
      eexists. intros. unfold Lookup_steps. ring_simplify. apply dominatedWith_add_r. domWith_approx.
      - eapply dominatedWith_trans. apply (proj2_sig (CopyValue_steps_nice _)). domWith_approx. apply dominatedWith_solve. enough (1 <= size xs) by nia. rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1.
      - eapply dominatedWith_trans. apply (proj2_sig (Lookup_Loop_steps_nice)). domWith_approx.
      - enough (1 <= size xs) by nia. rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1.
    Qed.

    Hypothesis (size_X_ge1 : forall (x : X), 1 <= size x).

    Lemma Lookup_steps_nice' :
      { c | forall (x : X) (xs : list (X*Y)), Lookup_steps x xs <=(c) size x * size xs }.
    Proof.
      eexists. intros. eapply dominatedWith_trans. apply (proj2_sig Lookup_steps_nice). ring_simplify. domWith_approx.
      apply dominatedWith_solve. enough (1 <= size x) by nia. apply size_X_ge1.
    Qed.

  End LookupAssociativeList_nice.


  (** Some lemmas about the index position in a finite enumeration *)

  Lemma getPosition_le (X : finType) (A : list X) (x : X) :
    In x A ->
    getPosition A x < length A.
  Proof.
    intros. induction A as [ | a A' IH]; cbn in *.
    - tauto.
    - destruct H as [ <- | H].
      + decide (a = a) as [_ | ?]; [ | tauto]. omega.
      + decide (x = a) as [<- | HDec].
        * omega.
        * specialize IH with (1 := H). omega.
  Qed.

  Lemma index_le (E : finType) (x : E) : index x < length (enum : list E).
  Proof.
    unfold enum. unfold index.
    apply getPosition_le.
    apply countIn. setoid_rewrite enum_ok. omega.
  Qed.

  Arguments enum type {_}.

  Lemma fin_empty_or_element (X : finType) :
    ((forall (x : X), False) /\ enum X = nil) \/ (exists (x : X), enum X <> nil).
  Proof.
    destruct (enum X) eqn:E.
    - left. split; eauto. intros.
      enough (BasicDefinitions.count (enum X) x = 0).
      { rewrite enum_ok in H. congruence. }
      rewrite E. cbn. reflexivity.
    - right. exists e. congruence.
  Qed.

  Lemma prodLists_length (X Y : Type) (xs : list X) (ys : list Y) :
    length (prodLists xs ys) = length xs * length ys.
  Proof.
    induction xs as [ | x xs' IH]; cbn in *.
    - reflexivity.
    - simpl_list. omega.
  Qed.

  Lemma prodLists_nil_Y_nil (X Y : Type) (xs : list X) (ys : list Y) :
    xs <> nil ->
    prodLists xs ys = nil ->
    ys = nil.
  Proof.
    intros.
    pose proof prodLists_length xs ys.
    assert (0 < length xs) by (destruct xs; cbn in *; congruence||omega).
    rewrite H0 in H1; cbn in H1.
    assert (|ys| = 0) by nia.
    destruct ys; cbn in *; congruence||omega.
  Qed.

  Lemma fin_prod_nil_Y_nil (X Y : finType) :
    enum X <> nil ->
    enum (EqType(X*Y)) = nil ->
    enum Y = nil.
  Proof.
    pose proof fin_empty_or_element X as [ [H1 H2] | [x H] ].
    - cbn. unfold elem. rewrite !H2. cbn. congruence.
    - cbn. unfold elem. intros. eapply prodLists_nil_Y_nil; eauto.
  Qed.

  Lemma enum_not_nil (X : finType) (x : X) :
    enum X <> nil.
  Proof. pose proof fin_empty_or_element X as [ [H1 H2] | [x' H]]; auto. Qed.


  Lemma enum_length_ge1 (X : finType) :
    enum X <> [] ->
    1 <= | enum X |.
  Proof. destruct (enum X) eqn:E; cbn; congruence || omega. Qed.


  Import Univ.StepTM.

  Section Univ_nice.

    (** Note that [Univ] actually needs to be instantiated with some retraction, but we don't need to do it here for the running time bounds *)

    (** The alphabet of the simulated machine *)
    Variable (sigM : finType).
    (** The simulated machine *)
    Variable (M : mTM sigM 1).


    Lemma DoAction'_steps_nice :
      { c | DoAction'_steps <=(c) 1 }.
    Proof. eexists. domWith_approx. Qed.

    Lemma ReadCurrent'_steps_nice :
      { c | ReadCurrent'_steps <=(c) 1 }.
    Proof. eexists. domWith_approx. Qed.


    Lemma Univ_Step_steps_CasePair_nice :
      { c | forall (a : option sigM * move), Univ_Step_steps_CasePair a <=(c) 1 }.
    Proof.
      eexists. unfold Univ_Step_steps_CasePair. intros (w,m). eapply dominatedWith_trans. apply (proj2_sig (CasePair_steps_nice _)).
      domWith_approx. apply dominatedWith_solve. reflexivity.
    Qed.

    Definition number_of_states : nat := length (enum (states M)).

    Lemma size_state_index_lt (q : states M) : size (index q) < size number_of_states.
    Proof. hnf. rewrite !Encode_nat_hasSize. enough (index q < number_of_states) by omega. apply index_le. Qed.

    Lemma size_state_index_le (q : states M) : size (index q) <= size number_of_states.
    Proof. apply Nat.lt_le_incl. apply size_state_index_lt. Qed.

    Lemma Univ_Step_steps_ConstrPair_nice :
      { c | forall (tp : tape sigM), Univ_Step_steps_ConstrPair tp <=(c) 1 }.
    Proof.
      eexists. intros. unfold Univ_Step_steps_ConstrPair. eapply dominatedWith_trans. apply (proj2_sig (Constr_pair_steps_nice _)).
      domWith_approx. apply dominatedWith_solve. reflexivity.
    Qed.

    Lemma Univ_Step_steps_ResetSymbol_nice :
      { c | forall (tp : tape sigM), Univ_Step_steps_ResetSymbol tp <=(c) 1 }.
    Proof.
      eexists. intros. unfold Univ_Step_steps_ResetSymbol. eapply dominatedWith_trans. apply (proj2_sig (Reset_steps_nice _)).
      domWith_approx. apply dominatedWith_solve. reflexivity.
    Qed.


    Lemma Encode_state_hasSize (q : states M) :
      size (halt q, index q) <= size number_of_states.
    Proof.
      setoid_rewrite Encode_pair_hasSize. cbn. setoid_rewrite Encode_bool_hasSize. cbn. hnf.
      pose proof size_state_index_lt q. hnf in H. nia.
    Qed.

    Lemma IsFinal_steps_nice :
      { c | forall (b : bool), IsFinal_steps b <=(c) 1 }.
    Proof.
      eexists. intros. unfold IsFinal_steps. ring_simplify. apply dominatedWith_add_r; [ domWith_approx | reflexivity ].
      eapply dominatedWith_trans. apply (proj2_sig (CasePair_steps_nice _)). domWith_approx.
      rewrite Encode_bool_hasSize. domWith_approx.
    Qed.

    Local Existing Instance Encode_graph.

    Lemma graph_of_fun_length (A : finType) (B : Type) (f : A -> B) :
      length (graph_of_fun f) = length (enum A).
    Proof. unfold graph_of_fun. now simpl_list. Qed.

    Lemma length_graph_is_number_of_states :
      length (graph_of_TM M) = number_of_states * (1 + length (elem sigM)).
    Proof.
      unfold graph_of_TM, number_of_states. simpl_list. setoid_rewrite graph_of_fun_length. cbn -[enum]. cbn. simpl_list.
      rewrite prodLists_length. simpl_list. ring_simplify. now rewrite Nat.mul_comm.
    Qed.

    Instance tam (x : nat) : Proper (lt --> Basics.flip Basics.impl) (le x).
    Proof. hnf. intros. cbn in *. hnf in *. intros. omega. Qed.

    Lemma Encode_graph_ge_number_of_states :
      number_of_states <= size (graph_of_TM M).
    Proof.
      (* We can show that the number of entries in [number_of_states] is equal to [number_of_states] *)
      enough (number_of_states <= length (graph_of_TM M)).
      {
        setoid_rewrite Encode_list_hasSize.
        setoid_rewrite <- Encode_list_hasSize_ge_length.
        auto.
      }
      setoid_rewrite length_graph_is_number_of_states.
      try rewrite Encode_nat_hasSize. ring_simplify.
      nia.
    Qed.

    Lemma Encode_graph_hasSize_ge1 :
      1 <= size (graph_of_TM M).
    Proof. setoid_rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1. Qed.

    Lemma number_of_states_nice :
      { c | size number_of_states <=(c) size (graph_of_TM M) }.
    Proof.
      eexists.
      eapply dominatedWith_trans.
      { apply dominatedWith_solve. rewrite Encode_nat_hasSize. reflexivity. }
      ring_simplify. apply dominatedWith_add_r.
      { apply dominatedWith_solve. apply Encode_graph_ge_number_of_states. }
      { apply Encode_graph_hasSize_ge1. }
    Qed.

    Lemma Univ_Step_steps_Lookup_nice :
      { c | forall (q : states M) (tp : tape sigM), Univ_Step_steps_Lookup q tp <=(c) size (graph_of_TM M) }.
    Proof.
      eexists. unfold Univ_Step_steps_Lookup. intros. eapply dominatedWith_trans. unshelve eapply (proj2_sig (Lookup_steps_nice' _ _)).
      - intros (s,(f,i)). setoid_rewrite Encode_pair_hasSize. cbn. setoid_rewrite Encode_bool_hasSize. omega. constructor. (* this is odd *)
      - setoid_rewrite Encode_pair_hasSize; cbn [Encode_pair_size]. setoid_rewrite Encode_Finite_hasSize. ring_simplify. domWith_approx.
        + eapply dominatedWith_trans.
          * apply dominatedWith_solve. apply Encode_state_hasSize.
          * apply (proj2_sig number_of_states_nice).
        + apply dominatedWith_refl. constructor.
    Qed.

    Lemma Univ_Step_steps_Translate_nice :
      { c | forall (q : states M), Univ_Step_steps_Translate q <=(c) size number_of_states }.
    Proof.
      eexists. unfold Univ_Step_steps_Translate. intros.
      eapply dominatedWith_trans. apply (proj2_sig (Translate_steps_nice _)).
      rewrite Encode_pair_hasSize. cbn. rewrite Encode_bool_hasSize. ring_simplify. domWith_approx.
      - apply dominatedWith_solve. apply size_state_index_le.
      - instantiate (1 := 2). hnf. enough (1 <= size number_of_states) by omega. apply Encode_nat_hasSize_ge1.
    Qed.

    Lemma Univ_Step_steps_IsFinal_nice :
      { c | forall (q : states M) (tp : tape sigM),
          Univ_Step_steps_IsFinal q tp
          <=(c)
             if halt q
             then 1
             else size (graph_of_TM M) }.
    Proof.
      eexists. intros. unfold Univ_Step_steps_IsFinal. domWith_match. domWith_approx. destruct trans as (q',acts) eqn:E. ring_simplify. apply dominatedWith_add_r. domWith_approx.
      - eapply dominatedWith_trans. apply (proj2_sig ReadCurrent'_steps_nice). apply dominatedWith_solve. apply Encode_graph_hasSize_ge1.
      - eapply dominatedWith_trans. apply (proj2_sig Univ_Step_steps_ConstrPair_nice). apply dominatedWith_solve. apply Encode_graph_hasSize_ge1.
      - eapply dominatedWith_trans. apply (proj2_sig Univ_Step_steps_ResetSymbol_nice). apply dominatedWith_solve. apply Encode_graph_hasSize_ge1.
      - eapply dominatedWith_trans. apply (proj2_sig Univ_Step_steps_Lookup_nice). apply dominatedWith_solve. omega.
      - eapply dominatedWith_trans. apply (proj2_sig Univ_Step_steps_CasePair_nice). apply dominatedWith_solve. apply Encode_graph_hasSize_ge1.
      - eapply dominatedWith_trans. apply (proj2_sig DoAction'_steps_nice). apply dominatedWith_solve. apply Encode_graph_hasSize_ge1.
      - eapply dominatedWith_trans. apply (proj2_sig Univ_Step_steps_Translate_nice). apply (proj2_sig number_of_states_nice).
      - apply Encode_graph_hasSize_ge1.
    Qed.

    Lemma Univ_Step_steps_nice :
      { c | forall (q : states M) (tp : tape sigM),
          Univ_Step_steps q tp
          <=(c)
             if halt q
             then 1
             else size (graph_of_TM M) }.
    Proof.
      eexists. intros. unfold Univ_Step_steps. ring_simplify. apply dominatedWith_add_r; [ domWith_approx | ].
      - eapply dominatedWith_trans. apply (proj2_sig IsFinal_steps_nice). apply dominatedWith_solve. destruct halt; [omega | apply Encode_graph_hasSize_ge1].
      - eapply dominatedWith_trans. apply (proj2_sig Univ_Step_steps_IsFinal_nice). apply dominatedWith_solve. destruct halt; omega.
      - destruct halt; [omega | apply Encode_graph_hasSize_ge1].
    Qed.

    Local Arguments Univ_Step_steps : simpl never.

    Lemma Univ_steps_nice :
      { c | forall (q : states M) (tp : tape sigM) (k : nat), Univ_steps q tp k <=(c) size k * size (graph_of_TM M) }.
    Proof.
      pose_nice Univ_Step_steps_nice Hc_Step c_Step.
      exists (c_Step + 1). intros. induction k as [ | k' IH] in q,tp|-*; cbn [Univ_steps] in *.
      - hnf. rewrite Hc_Step. destruct halt.
        + rewrite Encode_nat_hasSize. ring_simplify. enough (1 <= size (graph_of_TM M)) by nia. apply Encode_graph_hasSize_ge1.
        + rewrite Encode_nat_hasSize. ring_simplify. enough (1 <= size (graph_of_TM M)) by nia. apply Encode_graph_hasSize_ge1.
      - specialize (Hc_Step q tp). hnf. destruct halt eqn:E.
        + rewrite Hc_Step. ring_simplify. enough (1 <= size (1 + k') /\ 1 <= size (graph_of_TM M)) by nia. split. apply Encode_nat_hasSize_ge1. apply Encode_graph_hasSize_ge1.
        + destruct (step (mk_mconfig q [|tp|])) as (q',tp') eqn:E'. specialize (IH q' tp'[@Fin0]); hnf in IH. rewrite IH. rewrite Hc_Step. clear_all.
          ring_simplify. rewrite !Encode_nat_hasSize. ring_simplify. enough (1 <= size (graph_of_TM M)) by nia. apply Encode_graph_hasSize_ge1.
    Qed.


  End Univ_nice.

End Univ_nice.

Print Assumptions Univ_nice.Univ_steps_nice.
