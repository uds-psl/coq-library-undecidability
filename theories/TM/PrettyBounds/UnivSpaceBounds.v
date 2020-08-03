(** * Space Analysis for Univ *)

From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import BaseCodeSpace.

From Undecidability Require Import CaseList CasePair.


From Undecidability Require Import Univ.LookupAssociativeListTM.


Lemma max_list_rec_map_monotone' (X : Type) (s0 s1 : nat) (xs : list X) (f0 f1 : X -> nat) :
  (forall x : X, x el xs -> f0 x <= f1 x) ->
  s0 <= s1 ->
  max_list_rec s0 (map f0 xs) <= max_list_rec s1 (map f1 xs).
Proof.
  intros. apply max_list_rec_monotone'.
  - apply Forall2_map, Forall_Forall2, Forall_forall. assumption.
  - assumption.
Qed.

(* [flip] doesn't work here. We could flip it in the definition of [max_list_rec], but this would look a bit weird. *)
Instance max_list_rec_proper (xs : list nat) : Proper (le ==> le) (Basics.flip max_list_rec xs).
Proof. hnf. intros. cbv [Basics.flip]. now apply max_list_rec_monotone. Qed.
  



Section Lookup_size_nice.
  Variable (sigX sigY : finType).
  Variable (X : eqType) (Y : Type) (cX : codable sigX X) (cY : codable sigY Y).

  Lemma CaseList_size1_CasePair_size0_Reset_size_nice (x' : X) (y : Y) (s : nat) :
    ((CaseList_size1 (x', y) >> CasePair_size0 x') >> Reset_size y) s = Init.Nat.max s (size (x', y) + 1). (* plus one, because tape was initally empty *)
  Proof.
    cbn.
    rewrite Reset_size_nice. (* = *)
    rewrite CasePair_size0_nice. (* = *)
    now rewrite CaseList_size1_nice'. (* = *)
  Qed.


  (** We only consider the [cons] case. Note that inequality is the worst case *)
  Lemma Lookup_Step_size_nice_eq (xs : list (X*Y)) (x : X) (p : X * Y) :
    let (x', y) := p in
    x = x' ->
    (forall (s0 : nat), Lookup_Step_size (p :: xs) x @>Fin0 s0           = s0 + size (p :: xs) + 1) /\
    (forall (s1 : nat), Lookup_Step_size (p :: xs) x @>Fin1 s1 + size y  = max (s1 + size x) (size y)) /\
    (forall (s2 : nat), Lookup_Step_size (p :: xs) x @>Fin2 s2           = max s2 (size (x', y) + 1)) /\
    (forall (s3 : nat), Lookup_Step_size (p :: xs) x @>Fin3 s3           = max s3 (size x + 1)).
  Proof.
    destruct p as [x' y]. unfold Lookup_Step_size; cbn [Vector.nth].
    intros Hdec. decide (x=x') as [<-|Hdec']; try tauto.
    {
      repeat split; intros; cbn.
      - now setoid_rewrite CaseList_size0_Reset_nice.
      - now rewrite MoveValue_size_y_nice.
      - now setoid_rewrite CaseList_size1_CasePair_size0_Reset_size_nice. (* [MoveValue_size_x] is the same as [Reset_size] *)
      - now setoid_rewrite CasePair_size1_Reset_nice.
    }
  Qed.

  (** We use two lemmas here because this makes rewriting easier *)
  Lemma Lookup_Step_size_nice_neq (xs : list (X*Y)) (x : X) (p : X * Y) :
    let (x', y) := p in
    x <> x' ->
    (forall (s0 : nat), Lookup_Step_size (p :: xs) x @>Fin0 s0 + size xs = s0 + size ((x', y) :: xs)) /\
    (forall (s1 : nat), Lookup_Step_size (p :: xs) x @>Fin1 s1           = s1) /\ (* id *)
    (forall (s2 : nat), Lookup_Step_size (p :: xs) x @>Fin2 s2           = max s2 (size (x', y) + 1)) /\
    (forall (s3 : nat), Lookup_Step_size (p :: xs) x @>Fin3 s3           = max s3 (size x' + 1)).
  Proof.
    destruct p as [x' y]. unfold Lookup_Step_size; cbn [Vector.nth].
    intros Hdec. decide (x=x') as [<-|Hdec']; try tauto.
    {
      repeat split; intros; cbn.
      - now rewrite CaseList_size0_nice.
      - now setoid_rewrite CaseList_size1_CasePair_size0_Reset_size_nice.
      - now setoid_rewrite CasePair_size1_Reset_nice.
    }
  Qed.

  (** Don't touch the definition any more; we have bounds now! *)
  Local Arguments Lookup_Step_size : simpl never.


  (** The elements in the list that have been seen by [lookup], including the element that was found *)
  Fixpoint lookup_hd (x : X) (xs : list (X*Y)) : list (X*Y) :=
    match xs with
    | nil => nil
    | (x', y) :: xs' => if Dec(x = x') then [(x',y)] else (x', y) :: lookup_hd x xs'
    end.

  Lemma lookup_hd_incl (x : X) (xs : list (X*Y)) :
    lookup_hd x xs <<= xs.
  Proof.
    revert x. induction xs as [ | (x',y) xs' IH]; intros; cbn in *.
    - intuition.
    - decide (x=x') as [<-|Hdec]; intuition.
  Qed.


  (** We are not really interested in the case that [lookup] fails *)
  Lemma Lookup_Loop_size_nice (xs : list (X*Y)) (x : X) (y_res : Y) :
    lookup x xs = Some y_res ->
    (forall (s0 : nat), Lookup_Loop_size xs x @>Fin0 s0              = s0 + size xs + 1) /\ (* The full list discarded *)
    (forall (s1 : nat), Lookup_Loop_size xs x @>Fin1 s1 + size y_res = max (s1 + size x) (size y_res)) /\ (* [x] is replaced with [y_res] only once *)
    (forall (s2 : nat), Lookup_Loop_size xs x @>Fin2 s2              = max_list_rec s2 (map (fun p => size p + 1) (lookup_hd x xs))) /\
    (forall (s3 : nat), Lookup_Loop_size xs x @>Fin3 s3              = max_list_rec s3 (map (fun p => size (fst p) + 1) (lookup_hd x xs))).
  Proof.
    revert x y_res. induction xs as [ | [x' y] xs IH]; intros; cbn in *.
    - congruence.
    - decide (x = x') as [<- | Hdec].
      { (* [x=x'] *) inv H.
        repeat split; cbn; intros.
        - projk_rewrite (Lookup_Step_size_nice_eq xs x (x, y_res) eq_refl) 0. nia.
        - projk_rewrite (Lookup_Step_size_nice_eq xs x (x, y_res) eq_refl) 1. reflexivity.
        - projk_rewrite (Lookup_Step_size_nice_eq xs x (x, y_res) eq_refl) 2. nia.
        - projk_rewrite (Lookup_Step_size_nice_eq xs x (x, y_res) eq_refl) 3. nia.
      }
      { (* [x<>x'] *) specialize IH with (1 := H) as (IH0&IH1&IH2&IH3).
        repeat split; cbn; intros.
        - rewrite IH0. projk_rewrite (Lookup_Step_size_nice_neq xs x (x', y) Hdec). nia.
        - rewrite IH1. now projk_rewrite (Lookup_Step_size_nice_neq xs x (x', y) Hdec).
        - rewrite IH2. projk_rewrite (Lookup_Step_size_nice_neq xs x (x', y) Hdec). f_equal. nia.
        - rewrite IH3. projk_rewrite (Lookup_Step_size_nice_neq xs x (x', y) Hdec). f_equal. nia.
      }
  Qed.


  Lemma Lookup_size_nice (xs : list (X*Y)) (x : X) (y_res : Y) :
    lookup x xs = Some y_res ->
    (forall (s0 : nat), Lookup_size xs x @>Fin0 s0              = s0) /\ (* [id] *)
    (forall (s1 : nat), Lookup_size xs x @>Fin1 s1 + size y_res = max (s1 + size x) (size y_res)) /\ (* [Fin1] *) (* output tape *)
    (forall (s2 : nat), Lookup_size xs x @>Fin2 s2              = max_list_rec s2 (map (fun p => size p + 1) (lookup_hd x xs))) /\ (* [Fin2] *)
    (forall (s3 : nat), Lookup_size xs x @>Fin3 s3              = max_list_rec s3 (map (fun p => size (fst p) + 1) (lookup_hd x xs))) /\ (* [Fin3] *)
    (forall (s4 : nat), Lookup_size xs x @>Fin4 s4              = max s4 (size xs + 1)). (* Copy >> [Fin0] *)
  Proof.
    intros. unfold Lookup_size; cbn. rewrite !vector_tl_nth. repeat split; intros.
    - now projk_rewrite (Lookup_Loop_size_nice H) 1.
    - now projk_rewrite (Lookup_Loop_size_nice H) 2.
    - now projk_rewrite (Lookup_Loop_size_nice H) 3.
    - projk_rewrite (Lookup_Loop_size_nice H) 0. now rewrite CopyValue_size_nice'.
  Qed.

End Lookup_size_nice.

Local Arguments Lookup_size : simpl never.


From Undecidability Require Import Univ.StepTM.
From Undecidability Require Import UnivBounds. (* We may need some lemmas from here *)
Import Univ_nice.


Section Univ_nice.

  (** The alphabet of the simulated machine *)
  Variable (sigM : finType).
  (** The simulated machine *)
  Variable (M : TM sigM 1).


  Lemma SetFinal_size_nice :
    (forall (final : bool) (q : nat) (s0 : nat), SetFinal_size @>Fin0 s0 + size (final, q) = max (s0 + size q) (size q + 1)) /\
    (forall                      (s1 : nat), SetFinal_size @>Fin1 s1                   = max s1 2).
  Proof.
    repeat split; intros; cbn.
    - transitivity (Constr_pair_size final s0 + size (final, q)).
      + reflexivity.
      + setoid_rewrite Constr_pair_size_nice. rewrite Encode_pair_hasSize; cbn. rewrite Encode_bool_hasSize; cbn. nia.
    - unfold ResetEmpty1_size. cbn. unfold WriteValue_size. rewrite Encode_bool_hasSize; cbn. ring_simplify. nia.
  Qed.

  Local Arguments SetFinal_size : simpl never.

  Lemma IsFinal_size_nice :
    forall (s : nat), IsFinal_size s = max s 2.
  Proof.
    intros. unfold IsFinal_size. cbn.
    projk_rewrite SetFinal_size_nice 1.
    enough (CasePair_size1 true s + size true + 1 = max s 2) as H by (rewrite Encode_bool_hasSize in H; nia).
    rewrite CasePair_size1_nice'. rewrite Encode_bool_hasSize; cbn. nia.
  Qed.

  Local Arguments IsFinal_size_nice : simpl never.

  
  (** Lemmas about [graph_of_fun] and [graph_of_TM] in particular *)
  
  Lemma graph_of_TM_In (Q Q' : state M) (s s' : option sigM) (q q' : nat) (b b' : bool) (m : move) (tp : tape sigM) :
    In (s, (b, q), (s', m, (b', q'))) (graph_of_TM M) ->
    index Q = q ->
    index Q' = q' ->
    current tp = s ->
    trans (Q, [|current tp|]) = (Q', [|(s', m)|]).
  Proof.
    unfold graph_of_TM.
    intros (?&?& ([? ?]&->) % graph_of_fun_In') % in_map_iff <- <- <-.
    cbn in H. inv H. apply injective_index in H3 as ->.
    destruct trans as [q' acts]. destruct acts[@Fin0] eqn:E. cbn in *. inv H4. apply injective_index in H3 as ->.
    destruct_vector. cbn in *. congruence.
  Qed.


  Lemma graph_of_TM_In' (s s' : option sigM) (q q' : nat) (b b' : bool) (m : move) :
    In (s, (b, q), (s', m, (b', q'))) (graph_of_TM M) ->
    exists (Q Q' : state M),
      index Q = q /\
      index Q' = q' /\
      trans (Q, [|s|]) = (Q', [|(s', m)|]).
  Proof.
    unfold graph_of_TM.
    intros (? & ? & ((x&y)&->) % graph_of_fun_In') % in_map_iff.
    cbn in *. inv H. unfold trans_map_keys, trans_map_values in *.
    destruct trans as [Q' acts] eqn:E.
    destruct_vector; rename h into act. destruct act as [act_w act_m]. cbn in *.
    inv H4.
    do 2 eexists; repeat split; eauto.
  Qed.

  Lemma graph_of_fun_not_empty (X : finType) (Y : Type) (f : X -> Y) :
    X -> graph_of_fun f <> nil.
  Proof.
    intros def.
    unfold graph_of_fun.
    intros H % map_eq_nil.
    eapply enum_not_nil with (X := X); eauto.
  Qed.

  Lemma graph_of_TM_not_nil : graph_of_TM M <> nil.
  Proof.
    unfold graph_of_TM.
    intros H % map_eq_nil.
    apply (graph_of_fun_not_empty (f := graph_function (M:=M))) in H; eauto.
    cbn. split. now constructor. apply start.
  Qed.

  
  (** We should have enough lemmas about [graph_of_TM] now *)
  Local Arguments graph_of_TM : simpl never.


  (** Non-standard encodings *)

  Local Existing Instance Encode_optSigM.
  Local Existing Instance Encode_action.
  Local Existing Instance Encode_graph.


  (** Lemmas about sizes of special encodings *)

  Local Lemma Encode_action_hasSize (act : option sigM * move) :
    size act = 1.
  Proof. apply Encode_Finite_hasSize. Qed.

  Local Lemma Encode_state_hasSize (q : state M) (halt : bool) :
    size (halt, index q) = index q + 2.
  Proof. do 1 (rewrite Encode_pair_hasSize; cbn). rewrite Encode_nat_hasSize. setoid_rewrite Encode_bool_hasSize. nia. Qed.

  (** x-values in [graph_of_TM] *)
  Local Lemma Encode_graph_x_hasSize (s : option sigM) (q : state M) (halt : bool) :
    size (s, (halt, index q)) = index q + 3.
  Proof. do 2 (rewrite Encode_pair_hasSize; cbn). rewrite Encode_bool_hasSize. rewrite Encode_nat_hasSize. setoid_rewrite Encode_Finite_hasSize. nia. Qed.

  (** x-values in [graph_of_TM] *)
  Local Lemma Encode_graph_y_hasSize (act : option sigM * move) (q' : state M) (halt' : bool) :
    size (act, (halt', index q')) = index q' + 3.
  Proof. do 2 (rewrite Encode_pair_hasSize; cbn). rewrite Encode_bool_hasSize. rewrite Encode_nat_hasSize. setoid_rewrite Encode_Finite_hasSize. nia. Qed.
    

  Lemma size_char_eq (c1 c2 : option sigM) :
    size c1 = size c2. (* = 1 *)
  Proof. now setoid_rewrite Encode_Finite_hasSize. Qed.

  
  (** First the aux tape (s3) for [IsFinal], then for [ReadCurrent]: [ReadCurrent] doesn't require more space than [IsFinal] (at most 2). *)
  Lemma IsFinal_Readcurrent_size_nice (s : nat) (c : option sigM) :
    (IsFinal_size >> ReadCurrent_size) s + size c + 1 = max s 2.
  Proof. cbn. rewrite IsFinal_size_nice. unfold ReadCurrent_size. setoid_rewrite Encode_Finite_hasSize. cbn. nia. Qed.


  (* Constr_pair_size (current tp) >> (Lookup_size (graph_of_TM M) (current tp, (halt q, index q)) @> Fin1) >> (CasePair_size0 act) *)
  Definition Univ_Step_size_bound2 (q q' : state M) (s2 : nat) :=
    (max (s2 + index q + 2) (max (index q) (index q') + 3)).

  Definition Univ_Step_size_bound3 (tp : tape sigM) (act : option sigM * move) (q : state M) (s3 : nat) :=
    max (max_list_rec (Init.Nat.max s3 2)
                      (map (fun p : option sigM * (bool * nat) * (option sigM * move * (bool * nat)) => size p + 1) (lookup_hd (current tp, (false, index q)) (graph_of_TM M))))
        (size act + 1).
  
  Definition Univ_Step_size_bound4 (tp : tape sigM) (q : state M) (s4 : nat) :=
    max_list_rec s4 (map (fun p : option sigM * (bool * nat) * (option sigM * move * (bool * nat)) => size (fst p) + 1) (lookup_hd (current tp, (false, index q)) (graph_of_TM M))).

  Definition Univ_Step_size_bound5 (s5 : nat) :=
    max s5 (size (graph_of_TM M) + 1).


  Lemma state_index_lt (q : state M) :
    index q < number_of_states M.
  Proof. apply index_le. Qed.

  Lemma state_index_le (q : state M) :
    index q <= number_of_states M.
  Proof. apply Nat.lt_le_incl. apply state_index_lt. Qed.

  (*
  Lemma state_index_le (q : state M) :
    index q <= number_of_states M.
  Proof. apply Nat.lt_le_incl. apply state_index_lt. Qed.
  *)

  Lemma size_state_lt (q : state M) (halt : bool) :
    size (halt, index q) < number_of_states M + 2.
  Proof.
    rewrite Encode_pair_hasSize; cbn. rewrite Encode_bool_hasSize. rewrite Encode_nat_hasSize.
    pose proof state_index_lt q. nia.
  Qed.

  Lemma size_state_le (q : state M) (halt : bool) :
    size (halt, index q) <= number_of_states M + 2.
  Proof. apply Nat.lt_le_incl. apply size_state_lt. Qed.


  Lemma Univ_Step_size_bound2_lt (q q' : state M) (s2 : nat) :
    Univ_Step_size_bound2 q q' s2 < max (s2 + number_of_states M + 2) (number_of_states M + 3).
  Proof.
    pose proof state_index_lt q. pose proof state_index_lt q'.
    unfold Univ_Step_size_bound2. nia.
  Qed.



  (** We only consider the case where [halt q = false]. No assertions about tape [0] (the object tape). *)
  Lemma Univ_Step_size_nice (tp : tape sigM) (q : state M) :
    let space := Univ_Step_size tp q in
    let (q', act) := trans (q, [|current tp|]) in
    let act := act[@Fin0] in
    let tp' := doAct tp act in
    halt q = false ->
    True /\
    (forall (s1 : nat), space @>Fin1 s1 = s1) /\
    (forall (s2 : nat), space @>Fin2 s2 + size (halt q', index q') = Univ_Step_size_bound2 q q' s2) /\
    (forall (s3 : nat), space @>Fin3 s3                            = Univ_Step_size_bound3 tp act q s3) /\
    (forall (s4 : nat), space @>Fin4 s4                            = Univ_Step_size_bound4 tp q s4) /\
    (forall (s5 : nat), space @>Fin5 s5                            = Univ_Step_size_bound5 s5).
  Proof.
    cbn.
    unfold Univ_Step_size; cbn. rewrite !vector_tl_nth.
    pose proof lookup_graph tp q as LLookup.
    destruct trans as [q' act] eqn:E.
    intros HHalt. rewrite HHalt in *.
    destruct_vector; rename h into act.
    pose proof (Lookup_size_nice _ _ LLookup) as (HL0&HL1&HL2&HL3&HL4).
    repeat split; intros; cbn in *; cbv [id].
    - rewrite CasePair_size0_nice. rewrite HL1. rewrite Constr_pair_size_nice. unfold Univ_Step_size_bound2.
      rewrite !Encode_graph_x_hasSize. rewrite Encode_graph_y_hasSize. rewrite Encode_state_hasSize. nia.
    - unfold DoAction_size. rewrite Reset_size_nice. rewrite CasePair_size1_nice'. rewrite HL2.
      rewrite Reset_size_nice. now setoid_rewrite IsFinal_Readcurrent_size_nice.
    - now rewrite HL3.
    - now rewrite HL4.
  Qed.


  Local Arguments Univ_Step_size : simpl never.


  (** For the Loop, we first write the exact bounds as fixpoints, we can simplify afterwards *)

  (** Bound for tape 2 *)

  Example Univ_Step_tape2_twice (tp : tape sigM) (q : state M) (s2 : nat) :
    halt q = false ->
    let (q', a) := trans (q, [|current tp|]) in
    let tp' := doAct tp a[@Fin0] in
    let (q'', a') := trans (q', [|current tp'|]) in
    halt q' = false ->
    Univ_Step_size tp' q' @> Fin2 (Univ_Step_size tp q @>Fin2 s2) + size (halt q'', index q'') =
    max (s2 + index q + 2) (max (index q) (max (index q') (index q'')) + 3).
  Proof.
    intros Hhalt.
    pose proof (Univ_Step_size_nice tp q). cbn in *.
    destruct (trans (q, _)) as (q', a) eqn:Et1. cbn.
    pose proof (Univ_Step_size_nice (doAct tp a[@Fin0]) q'). cbn in *.
    destruct (trans (q', _)) as (q'', a') eqn:Et2. cbn in *.
    intros Hhalt'.
    specialize (H Hhalt) as (_&_&HC&_). specialize (H0 Hhalt') as (_&_&HC'&_).
    rewrite HC'.
    unfold Univ_Step_size_bound2.
    replace ((Univ_Step_size tp q)[@Fin2] s2 + index q' + 2) with (Univ_Step_size tp q @>Fin2 s2 + size (halt q', index q')).
    2:{ rewrite Encode_state_hasSize. nia. }
    rewrite HC.
    unfold Univ_Step_size_bound2.
    nia.
  Qed.

  Example Univ_Step_tape2_trice (tp : tape sigM) (q : state M) (s2 : nat) :
    halt q = false ->
    let (q', a) := trans (q, [|current tp|]) in
    let tp' := doAct tp a[@Fin0] in
    let (q'', a') := trans (q', [|current tp'|]) in
    let tp'' := doAct tp' a'[@Fin0] in
    let (q''', a') := trans (q'', [|current tp''|]) in
    halt q' = false ->
    halt q'' = false ->
    Univ_Step_size tp'' q'' @>Fin2 (Univ_Step_size tp' q' @> Fin2 (Univ_Step_size tp q @>Fin2 s2)) + size (halt q''', index q''') =
    max (s2 + index q + 2) (max (index q) (max (index q') (max (index q'') (index q'''))) + 3).
  Proof.
    intros Hhalt.
    pose proof (Univ_Step_size_nice tp q). cbn in *.
    destruct (trans (q, _)) as (q', a) eqn:Et1. cbn.
    pose proof (Univ_Step_size_nice (doAct tp a[@Fin0]) q'). cbn in *.
    destruct (trans (q', _)) as (q'', a') eqn:Et2. cbn in *.
    pose proof (Univ_Step_size_nice (doAct (doAct tp a[@Fin0]) a'[@Fin0]) q''). cbn in *.
    destruct (trans (q'', _)) as (q''', a'') eqn:Et3. cbn in *.
    intros Hhalt' Hhalt''.
    specialize (H Hhalt) as (_&_&HC&_). specialize (H0 Hhalt') as (_&_&HC'&_). specialize (H1 Hhalt'') as (_&_&HC''&_).
    rewrite HC''.
    unfold Univ_Step_size_bound2.
    replace ((Univ_Step_size (doAct tp a[@Fin0]) q')[@Fin2] ((Univ_Step_size tp q)[@Fin2] s2) + index q'' + 2) with (((Univ_Step_size (doAct tp a[@Fin0]) q')[@Fin2] ((Univ_Step_size tp q)[@Fin2] s2) + size (halt q'', index q''))).
    2:{ rewrite Encode_state_hasSize. nia. }
    rewrite HC'.
    unfold Univ_Step_size_bound2.
    replace ((Univ_Step_size tp q)[@Fin2] s2 + index q' + 2) with (Univ_Step_size tp q @>Fin2 s2 + size (halt q', index q')).
    2:{ rewrite Encode_state_hasSize. nia. }
    rewrite HC.
    unfold Univ_Step_size_bound2.
    nia.
  Qed.

  (** We could continue this here; but let's rather write this series as fixpoint instead. *)

  (** The series looks like max (s2 + index q0 + 2) (max* [index q0, index q1, ..., index qk] + 3).  *)

  (*
Fixpoint Univ_size_bound2_fix 
*)

  
  (** Why not write a function [execution] that yields a list of configurations? We can then simply apply [max_list_rec] on this list to get the exact bound *)
  Fixpoint execution (q : state M) (tp : tape sigM) (k : nat) : list (state M * tape sigM) :=
    match k with
    | 0 => [(q, tp)]
    | S k' => if halt q then [(q, tp)]
             else let (q', act) := trans (q, [|current tp|]) in
                  (q, tp) :: execution q' (doAct tp act[@Fin0]) k'
    end.

  Definition Univ_size_bound2 (q : state M) (tp : tape sigM) (k : nat) (s2 : nat) :=
    max_list_rec (s2 + index q + 2) (map (fun '(q', tp') => index q' + 3) (execution q tp k)).



  (** Bound for tape 3 *)


  (** This is a better definition for tape 3, because we have two parts: one part that can be upper-bounded, and one that only depends on [s3] *)
  Lemma Univ_Step_size_bound3_better tp q act s3 :
    Univ_Step_size_bound3 tp act q s3 =
    max (max_list_rec (size act + 1)
                      (map (fun p : option sigM * (bool * nat) * (option sigM * move * (bool * nat)) => size p + 1) (lookup_hd (current tp, (false, index q)) (graph_of_TM M))))
        (Init.Nat.max s3 2).
  Proof.
    unfold Univ_Step_size_bound3. (* This definition followed directly from the semantics *)
    rewrite <- !max_list_rec_max''.
    f_equal. nia.
  Qed.


  (** We use a global upper bound for tape 4, because this is should be much easier here. (The upper bound never changes, and this is an internal tape.) *)
  Definition Univ_size_bound3 (s3 : nat) :=
    max_list_rec (max s3 2) (map (fun p : option sigM * (bool * nat) * (option sigM * move * (bool * nat)) => size p + 1) (graph_of_TM M)).

  
  Lemma graph_of_TM_In'' (s s' : option sigM) (b b' : bool) (qi qi' : nat) (q q' : state M) (m : move) :
    trans (q, [|s|]) = (q', [|(s', m)|]) ->
    qi = index q ->
    b = halt q ->
    qi' = index q' ->
    b' = halt q' ->
    In ((s, (b, qi)), (s', m, (b', qi'))) (graph_of_TM M).
  Proof.
    intros. subst. cbn in *.
    unfold graph_of_TM.
    eapply in_map_iff.
    eexists (_, _, (_, _, _)).
    cbv [map_pair]. cbn -[graph_of_fun]. split.
    - f_equal.
    - replace (s', m, q') with (graph_function (s, q)).
      2:{ unfold graph_function. now rewrite H. }
      apply graph_of_fun_In.
  Qed.

  Local Lemma helper_lemma_without_name3 (o w : option sigM) (b b' : bool) (x x' : state M) (m : move) (s3 : nat) :
    trans (x, [|o|]) = (x', [|(w, m)|]) ->
    size (o, (b, index x), (w, m, (b', index x'))) + 1 <= Univ_size_bound3 s3.
  Proof.
    intros.
    apply max_list_rec_ge_el.
    apply in_map_iff.
    eexists ((o, (halt x, index x)), ((w, m), (halt x', index x'))); cbn. split.
    - repeat (rewrite Encode_pair_hasSize; cbn). f_equal.
    - destruct_vector. eapply graph_of_TM_In''; eauto.
  Qed.

  
  (* This can be greatly simplified... *)
  Local Lemma helper_lemma_without_name3' (act : option sigM * move) (s3 : nat) :
    Init.Nat.max (Init.Nat.max (Init.Nat.max s3 2) (size act + 1)) 2 <=
    max_list_rec (Init.Nat.max s3 2) (map (fun p : option sigM * (bool * nat) * (option sigM * move * (bool * nat)) => size p + 1) (graph_of_TM M)).
  Proof.
    rewrite Encode_action_hasSize.
    transitivity (max s3 2); [nia| ].
    apply max_list_rec_ge.
  Qed.



  (** Bound for tape 4 *)

  (* We use a global upper bound for tape 4, because this is should be much easier here. (The upper bound never changes, and this is an internal tape.) *)
  Definition Univ_size_bound4 (s4 : nat) :=
    max_list_rec s4 (map (fun (p : option sigM * (bool * nat) * (option sigM * move * (bool * nat))) => size (fst p) + 1) (graph_of_TM M)).


  (** This lemma is needed in the induction step for tape 4 *)
  Local Lemma helper_lemma_without_name4 (o : option sigM) (b : bool) (x : state M) s4 :
    size (o, (b, index x)) + 1 <= max_list_rec s4 (map (fun p : option sigM * (bool * nat) * (option sigM * move * (bool * nat)) => size (fst p) + 1) (graph_of_TM M)).
  Proof.
    apply max_list_rec_ge_el.
    apply in_map_iff.
    destruct (trans (x, [|o|])) as [q' a] eqn:Et.
    eexists ((o, (halt x, index x)), (a[@Fin0], (halt q', index q'))); cbn. split.
    - auto.
    - destruct_vector. rename h into a. destruct a as [w m]. cbn in *.
      eapply graph_of_TM_In''; eauto.
  Qed.


  (** Bound for tape 5 is the same as in the step, i.e. the size of the lookup table *)


  Lemma Univ_size_nice' (k : nat) (tp : tape sigM) (q : state M) (tp_final : tape sigM) (q_final : state M) :
    let space := Univ_size tp q k in
    loopM (mk_mconfig q [|tp|]) k = Some (mk_mconfig q_final [|tp_final|]) ->
    True /\
    (forall (s1 : nat), space @>Fin1 s1 = s1) /\ (* This is still [id] *)
    (forall (s2 : nat), space @>Fin2 s2 + size (halt q_final, index q_final) <= Univ_size_bound2 q tp k s2) /\
    (forall (s3 : nat), space @>Fin3 s3 <= Univ_size_bound3 s3) /\
    (forall (s4 : nat), space @>Fin4 s4 <= Univ_size_bound4 s4) /\
    (forall (s5 : nat), space @>Fin5 s5 <= Univ_Step_size_bound5 s5).
  Proof.
    cbn. revert tp q tp_final q_final. induction k as [ | k' IH]; intros; cbn in *.
    {
      unfold haltConf in H. cbn in *. destruct (halt q) eqn:Eh; inv H. repeat split; intros.
      - unfold Univ_Step_size; cbn. rewrite Eh. cbn. auto.
      - unfold Univ_Step_size; cbn. rewrite Eh. cbn.
        cbv [id]. rewrite Encode_state_hasSize. nia.
      - unfold Univ_Step_size; cbn. rewrite Eh. cbn. rewrite IsFinal_size_nice. unfold Univ_size_bound3. apply max_list_rec_ge.
      - unfold Univ_Step_size; cbn. rewrite Eh. cbn. cbv [id]. unfold Univ_size_bound4. apply max_list_rec_ge.
      - unfold Univ_Step_size; cbn. rewrite Eh. cbn. auto. cbv [id]. unfold Univ_Step_size_bound5. nia.
    }
    {
      unfold haltConf in *. cbn in *. destruct (halt q) eqn:Eh.
      { (* [halt q = true /\ q = q_final]: the boring case *) inv H.
        repeat split; intros.
        - unfold Univ_Step_size; cbn. rewrite Eh. cbn. auto.
        - unfold Univ_Step_size; cbn. rewrite Eh. cbn. auto.
          cbv [id]. rewrite Encode_state_hasSize. nia.
        - unfold Univ_Step_size; cbn. rewrite Eh. cbn. rewrite IsFinal_size_nice. unfold Univ_size_bound3. apply max_list_rec_ge.
        - unfold Univ_Step_size; cbn. rewrite Eh. cbn. cbv [id]. unfold Univ_size_bound4. apply max_list_rec_ge.
        - unfold Univ_Step_size; cbn. rewrite Eh. cbn. auto. cbv [id]. unfold Univ_Step_size_bound5. nia.
      }
      { (* [halt q = false]: The interesting case *)
        unfold step; cbn.
        unfold step in H.
        pose proof @Univ_Step_size_nice tp q as HS. cbn in HS.
        destruct trans as [q' act] eqn:Etrans. destruct_vector; rename h into act. cbn in *.
        specialize IH with (1 := H) as (_&IH1&IH2&IH3&IH4&IH5).
        specialize HS with (1 := Eh) as (_&HS1&HS2&HS3&HS4&HS5).
        repeat split; intros.
        - rewrite IH1. now rewrite HS1. (* This was the easy part *)
        - rewrite IH2.
          destruct k' as [ | k'']; cbn in *.
          + replace ((Univ_Step_size tp q)[@Fin2] s2 + index q' + 2) with (Univ_Step_size tp q @>Fin2 s2 + size (halt q', index q')).
            2:{ rewrite Encode_state_hasSize. nia. }
            rewrite HS2. unfold Univ_Step_size_bound2. nia.
          + destruct (halt q') eqn:Eh'.
            * replace ((Univ_Step_size tp q)[@Fin2] s2 + index q' + 2) with (Univ_Step_size tp q @>Fin2 s2 + size (halt q', index q')).
              2:{ rewrite Encode_state_hasSize. nia. }
              rewrite HS2. unfold Univ_Step_size_bound2. cbn. nia.
            * auto. destruct (trans (q', _)) as [q'' a''] eqn:Etrans'; cbn in *.
              replace ((Univ_Step_size tp q)[@Fin2] s2 + index q' + 2) with (Univ_Step_size tp q @>Fin2 s2 + size (halt q', index q')).
              2:{ rewrite Encode_state_hasSize. nia. }
              rewrite HS2. unfold Univ_Step_size_bound2. cbn.
              enough ((Init.Nat.max (index q' + 3) (Init.Nat.max (s2 + index q + 2) (Init.Nat.max (index q) (index q') + 3))) = (Init.Nat.max (index q' + 3) (Init.Nat.max (index q + 3) (s2 + index q + 2)))) as -> by auto. (* let's help [nia] a bit... *)
              nia. (* my favourit tactic *)
        - rewrite IH3. rewrite HS3.
          apply max_list_rec_lower_bound.
          + unfold Univ_size_bound3. unfold Univ_Step_size_bound3. rewrite <- !max_list_rec_max''.
            apply max_list_rec_lower_bound.
            * apply helper_lemma_without_name3'.
            * intros ? (((?&?&?)&(?&?)&?&?) &<-& (?&?&<-&<-&?) % lookup_hd_incl % graph_of_TM_In') % in_map_iff; cbn in *. now apply helper_lemma_without_name3.
          + intros ? (((?&?&?)&(?&?)&?&?) &<-& (?&?&<-&<-&?) % graph_of_TM_In') % in_map_iff; cbn in *. now apply helper_lemma_without_name3.
        - rewrite IH4. rewrite HS4. unfold Univ_size_bound4.
          apply max_list_rec_lower_bound.
          + apply max_list_rec_lower_bound.
            * apply max_list_rec_ge.
            * intros ? (((?&?&?)&(?&?)&?&?) &<-& (?&?&<-&<-&?) % lookup_hd_incl % graph_of_TM_In') % in_map_iff; cbn in *. apply helper_lemma_without_name4.
          + intros ? (((?&?&?)&(?&?)&?&?) &<-& (?&?&<-&<-&?) % graph_of_TM_In') % in_map_iff; cbn in *. apply helper_lemma_without_name4.
        - rewrite IH5. rewrite HS5. unfold Univ_Step_size_bound5. nia.
      }
    }
  Qed.


  (** Some simplifications: *)
  (** Tape 0 is the object tape, it needs no bound. *)
  (** Tape 1 is constant, it contains the graph *)
  (** Tapes 2-5 are bounded by a constant that depends only on [graph_of_TM M]. *)
  (** But we don't forget that tape 2 has the output state on it's tape *)
  Definition Univ_size_bound (s : nat) := max (size (graph_of_TM M) + 1) s.


  Lemma Encode_list_hasSize_ge2 (sigX X : Type) (cX : codable sigX X) (xs : list X) :
    xs <> nil ->
    2 <= Encode_list_size xs.
  Proof.
    destruct xs as [ | x xs].
    - now intros [].
    - intros _. cbn. rewrite <- Encode_list_hasSize_ge1. nia.
  Qed.

  Lemma Encode_graph_hasSize_ge2 : 2 <= size (graph_of_TM M).
  Proof. setoid_rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge2. apply graph_of_TM_not_nil. Qed.

  Lemma tam (a b : nat) : a < b -> a + 1 <= b. Proof. nia. Qed.

  Lemma tamtam (q : state M) :
    index q + 2 <= size (graph_of_TM M).
  Proof.
    setoid_rewrite Encode_list_hasSize.
    transitivity ((size (index q)) + 1). rewrite Encode_nat_hasSize. nia.
    apply tam.
    destruct (trans (q, [|None|])) as [q' a] eqn:E.
    destruct_vector. destruct h as [m w].
    erewrite <- BaseCode.Encode_list_hasSize_el; swap 1 2.
    - eapply graph_of_TM_In''; eauto.
    - repeat (setoid_rewrite Encode_pair_hasSize; cbn).
      setoid_rewrite Encode_Finite_hasSize. nia.
  Qed.
  
  Lemma Univ_size_nice (k : nat) (tp : tape sigM) (q : state M) (tp_final : tape sigM) (q_final : state M) :
    let space := Univ_size tp q k in
    loopM (mk_mconfig q [|tp|]) k = Some (mk_mconfig q_final [|tp_final|]) ->
    True /\
    (forall (s1 : nat), space @>Fin1 s1 = s1) /\ (* This is still [id] *)
    (forall (s2 : nat), space @>Fin2 s2 + size (halt q_final, index q_final) <= Univ_size_bound s2 + size (halt q, index q)) /\
    (forall (s3 : nat), space @>Fin3 s3 <= Univ_size_bound s3) /\
    (forall (s4 : nat), space @>Fin4 s4 <= Univ_size_bound s4) /\
    (forall (s5 : nat), space @>Fin5 s5 <= Univ_size_bound s5).
  Proof.
    cbn. intros H.
    pose proof (Univ_size_nice' H) as (_&H1&H2&H3&H4&H5).
    repeat split; intros.
    - now rewrite H1.
    - unfold Univ_size_bound, Univ_size_bound4.
      rewrite H2. unfold Univ_size_bound, Univ_size_bound2.
      apply max_list_rec_lower_bound.
      + rewrite Encode_state_hasSize. nia.
      + intros ? (?&<-&?)%in_map_iff; cbn.
        destruct x0. cbn in *. clear H0.
        apply le_plus_trans.
        rewrite <- Nat.le_max_l.
        enough (index e + 2 <= size (graph_of_TM M)) by nia.
        apply tamtam.
    - rewrite H3. unfold Univ_size_bound, Univ_size_bound3.
      apply max_list_rec_lower_bound.
      + enough (2 <= size (graph_of_TM M)) by nia. apply Encode_graph_hasSize_ge2.
      + intros ? (?&<-&?)%in_map_iff.
        setoid_rewrite Encode_list_hasSize.
        rewrite <- Nat.le_max_l.
        apply le_plus_trans. apply tam. now apply BaseCode.Encode_list_hasSize_el.
    - rewrite H4. unfold Univ_size_bound, Univ_size_bound4.
      apply max_list_rec_lower_bound.
      + enough (2 <= size (graph_of_TM M)) by nia. apply Encode_graph_hasSize_ge2.
      + intros ? (?&<-&?)%in_map_iff.
        setoid_rewrite Encode_list_hasSize.
        rewrite <- Nat.le_max_l.
        apply le_plus_trans. apply tam.
        rewrite <- BaseCode.Encode_list_hasSize_el; eauto.
        destruct x0. cbn. destruct p.
        repeat (setoid_rewrite Encode_pair_hasSize; cbn). setoid_rewrite <- Encode_pair_hasSize.
        hnf. ring_simplify.
        progress enough (size o + size p + 1 <= size p + size o + size p0) by auto. (* some magic *)
        enough (1 <= size p0) by nia.
        destruct p0. destruct p1. repeat (rewrite Encode_pair_hasSize; cbn). rewrite Encode_nat_hasSize. nia.
    - rewrite H5. unfold Univ_size_bound, Univ_Step_size_bound5. nia.
  Qed.

End Univ_nice.
