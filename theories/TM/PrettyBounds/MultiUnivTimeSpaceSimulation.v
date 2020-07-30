(** * Theorem: Univ can simulate multi-tape Turing machines with polynominal time and linear space overhead *)

From Undecidability Require Import TM.Code.ProgrammingTools.
From Undecidability Require Import TM.Univ.StepTM. (* [Univ] for single-tape Turing machines *)
From Undecidability Require Import TM.Single.EncodeTapes TM.Single.StepTM. (* Compiler for multi-tape Turing machines to single-tape Turing machines *)

From Undecidability Require Import PrettyBounds PrettyBounds.SizeBounds MaxList.
From Undecidability Require UnivBounds.
From Undecidability Require UnivSpaceBounds.
From Undecidability Require M2MBounds.
From Undecidability Require Import TM.Util.VectorPrelim.

Require Import Derive.


Local Arguments loopM {_ _} _ _ _.
Local Arguments halt {_ _} _ _.
Local Arguments step {_ _} _ _.

(*
Lemma vector_const_nil (X : Type) (x : X) :
  Vector.const x 0 = Vector.nil _.
Proof. reflexivity. Qed.

Lemma vector_const_cons (X : Type) (n : nat) (x : X) :
  Vector.const x (S n) = x ::: Vector.const x n.
Proof. cbn. reflexivity. Qed.
*)


Lemma max_list_rec_repeat (a : nat) (s : nat) (n : nat) :
  n <> 0 ->
  max_list_rec s (repeat a n) = max s a.
Proof.
  revert s.
  (* refine (@complete_induction (fun n => forall s, n <> 0 -> max_list_rec s (repeat a n) = Init.Nat.max s a) n _). clear n. intros [ | n] IH s. *)
  induction n as [ | n IH]; intros s.
  - cbn. now intros [].
  - intros _.
    destruct n.
    + cbn. nia.
    + change (repeat a (S (S n))) with (a :: repeat a (S n)). cbn [max_list_rec].
      rewrite IH by congruence. nia.
Qed.

Lemma max_list_map_repeat (X : Type) (f : X -> nat) (a : X) (n : nat) :
  n <> 0 ->
  max_list_map f (repeat a n) = f a.
Proof.
  intros H.
  unfold max_list_map.
  rewrite map_repeat.
  now apply max_list_rec_repeat.
Qed.


Lemma vector_const_to_list (X : Type) (a : X) (n : nat) :
  vector_to_list (Vector.const a n) = repeat a n.
Proof. induction n; intros; cbn in *; now f_equal. Qed.


(*
(** Create a bogus tape of some size *)
Section MakeBogusTape.

  Variable (sig : Type) (defSig : inhabitedC sig).

  Definition bogus_tape (k : nat) : tape sig :=
    match k with
    | 0 => niltape _
    | S k' => midtape nil default (repeat default k')
    end.

  Lemma bogus_tape_sizeOfTape (k : nat) :
    sizeOfTape (bogus_tape k) = k.
  Proof.
    destruct k as [ | k']; cbn.
    - reflexivity.
    - now rewrite repeat_length.
  Qed.

  Definition bogus_tapes {n : nat} (k : nat) : Vector.t (tape sig) n := Vector.const (bogus_tape k) n.

  Lemma bogus_tapes_sizeOfmTapes (n k : nat) :
    n <> 0 ->
    sizeOfmTapes (@bogus_tapes n k) = k.
  Proof.
    unfold bogus_tapes.
    intros.
    setoid_rewrite sizeOfmTapes_max_list_map.
    rewrite vector_const_to_list.
    rewrite max_list_map_repeat by assumption.
    apply bogus_tape_sizeOfTape.
  Qed.

End MakeBogusTape.

Arguments bogus_tape {sig defSig} k.
Arguments bogus_tape : simpl never.

*)



Definition terminates (sigM : finType) (n : nat) (M : mTM sigM n) (tp : tapes sigM n) (k : nat) (tp' : tapes sigM n) :=
  exists (q : states M), loopM _ (initc M tp) k = Some (mk_mconfig q tp').



(** I forgot to write this function... *)
Definition ToSingleTape_steps (sigM F : finType) (n : nat) (pM : pTM sigM F n) (T : tapes sigM n) (k : nat) : nat := Single.StepTM.Loop_steps (start (projT1 pM)) T k.



(** Apply a size-function to every tape *)
Definition apply_sizeFun {n:nat} (f : Vector.t (nat->nat) n) (s : Vector.t nat n) : Vector.t nat n := tabulate (fun i => f @> i s[@i]).




(** Create the initial tapes of [Univ], given a single-tape machine [M] and a tape [t]. *)
Section InitUniv.

  Variable (sigM sig : finType).
  Definition sigGraph := (sigList (sigPair (sigPair (option sigM) sigState) (sigPair (option sigM * move) sigState))).
  Variable (retr_sigGraph_sig : Retract sigGraph sig).
  Variable retr_sigTape_sig : Retract sigM sig.

  Derive makeUnivWorkingTape SuchThat (forall (T : tape sigM), containsWorkingTape retr_sigTape_sig (makeUnivWorkingTape T : tape sig^+) T) As makeUnivWorkingTape_correct.
  Proof.
    subst makeUnivWorkingTape. cbn. intros.
    instantiate (1 := fun T => _). cbn.
    hnf. reflexivity.
  Qed.

  Lemma containsWorkingTape_iff (tp : tape sig^+) (T : tape sigM) :
    containsWorkingTape _ tp T <-> tp = makeUnivWorkingTape T.
  Proof.
    split.
    - apply id.
    - intros ->. apply makeUnivWorkingTape_correct.
  Qed.

  Derive makeUnivGraphTape SuchThat (forall (M : mTM sigM 1), containsTrans_size retr_sigGraph_sig (makeUnivGraphTape M : tape sig^+) M 0) As makeUnivGraphTape_correct_size.
  Proof.
    subst makeUnivGraphTape. cbn. intros.
    instantiate (1 := fun M => _). cbn.
    unfold containsTrans. apply initValue_contains_size.
  Qed.

  Lemma makeUnivGraphTape_correct M : containsTrans _ (makeUnivGraphTape M) M.
  Proof. eapply containsTrans_size_containsTrans. apply makeUnivGraphTape_correct_size. Qed.

  Derive makeUnivStartStateTape SuchThat (forall (M : mTM sigM 1), containsState_size retr_sigGraph_sig (makeUnivStartStateTape M : tape sig^+) (start M) 0) As makeUnivStartStateTape_correct_size.
  Proof.
    subst makeUnivStartStateTape. cbn. intros.
    instantiate (1 := fun M => _). cbn.
    unfold containsState. apply initValue_contains_size.
  Qed.

  Lemma makeUnivStartStateTape_correct M : containsState _ (makeUnivStartStateTape M) (start M).
  Proof. eapply containsState_size_containsState. apply makeUnivStartStateTape_correct_size. Qed.


  Definition makeUnivTapes (M : mTM sigM 1) (t : tape sigM) : tapes sig^+ 6 :=
    [| makeUnivWorkingTape t; makeUnivGraphTape M; makeUnivStartStateTape M; initRight _; initRight _; initRight _ |].

  Lemma makeUnivTapes_correct_size (M : mTM sigM 1) (tp : tape sigM) :
    containsWorkingTape _ (makeUnivTapes M tp)[@Fin0] tp /\
    containsTrans_size _ (makeUnivTapes M tp)[@Fin1] M 0 /\
    containsState_size _ (makeUnivTapes M tp)[@Fin2] (start M) 0 /\
    (forall (i : Fin.t 3), isRight_size (makeUnivTapes M tp)[@FinR 3 i] 0).
  Proof.
    unfold makeUnivTapes. cbn. split; [ | split; [ | split ]].
    - apply makeUnivWorkingTape_correct.
    - apply makeUnivGraphTape_correct_size.
    - apply makeUnivStartStateTape_correct_size.
    - intros i; destruct_fin i; cbn; apply initRight_isRight_size.
  Qed.

  Lemma makeUnivTapes_correct (M : mTM sigM 1) (tp : tape sigM) :
    containsWorkingTape _ (makeUnivTapes M tp)[@Fin0] tp /\
    containsTrans _ (makeUnivTapes M tp)[@Fin1] M /\
    containsState _ (makeUnivTapes M tp)[@Fin2] (start M) /\
    (forall (i : Fin.t 3), isRight (makeUnivTapes M tp)[@FinR 3 i]).
  Proof.
    unfold makeUnivTapes. cbn. split; [ | split; [ | split ]].
    - apply makeUnivWorkingTape_correct.
    - apply makeUnivGraphTape_correct.
    - apply makeUnivStartStateTape_correct.
    - intros i; destruct_fin i; cbn; apply initRight_isRight.
  Qed.


End InitUniv.


Lemma vector_to_list_nil (X : Type) :
  vector_to_list [||] = @nil X.
Proof. reflexivity. Qed.

Lemma vector_to_list_cons (X : Type) (n : nat) (x : X) (xs : Vector.t X n) :
  vector_to_list (x ::: xs) = x :: vector_to_list xs.
Proof. reflexivity. Qed.


Definition vector_sum {X : Type} {n : nat} (f : X -> nat) : Vector.t X n -> nat := fun xs => Vector.fold_left plus 0 (Vector.map f xs).

Lemma vector_sum_shift (X : Type) (n : nat) (xs : Vector.t X n) (f : X -> nat) (a : nat) :
  Vector.fold_left plus a (Vector.map f xs) = vector_sum f xs + a.
Proof.
  revert a. induction xs as [ | x n xs IH]; intros; cbn in *.
  - reflexivity.
  - setoid_rewrite IH at 2. setoid_rewrite IH at 1. omega.
Qed.


(* Coq's standard library is sooo inconsistent... *)
Definition list_sum {X : Type} (f : X -> nat) : list X -> nat := fun xs => fold_left plus (map f xs) 0.

Lemma list_sum_shift (X : Type) (xs : list X) (f : X -> nat) (a : nat) :
  fold_left plus (map f xs) a = list_sum f xs + a.
Proof.
  revert a. induction xs as [ | x xs IH]; intros; cbn in *.
  - reflexivity.
  - setoid_rewrite IH at 2. setoid_rewrite IH at 1. omega.
Qed.

Lemma vector_to_list_sum (X : Type) (n : nat) (xs : Vector.t X n) (f : X -> nat) :
  list_sum f (vector_to_list xs) = vector_sum f xs.
Proof.
  induction xs as [ | x n xs IH]; intros; cbn in *.
  - reflexivity.
  - rewrite vector_sum_shift, list_sum_shift. f_equal. apply IH.
Qed.

Lemma vector_sum_monotone (X : Type) (n : nat) (xs : Vector.t X n) (f1 f2 : X -> nat) :
  (forall x, Vector.In x xs -> f1 x <= f2 x) ->
  vector_sum f1 xs <= vector_sum f2 xs.
Proof.
  intros H. induction xs as [ | x n xs IH]; intros; cbn in *.
  - reflexivity.
  - rewrite !vector_sum_shift. rewrite H by constructor. now rewrite IH by (intros; apply H; now constructor).
Qed.

Lemma vector_sum_monotone_plus (X : Type) (n : nat) (a : nat) (xs : Vector.t X n) (f1 f2 : X -> nat) :
  (forall x, Vector.In x xs -> f1 x <= f2 x + a) ->
  vector_sum f1 xs <= vector_sum f2 xs + a * n.
Proof.
  intros H. induction xs as [ | x n xs IH]; intros; cbn in *.
  - omega.
  - rewrite !vector_sum_shift. rewrite Nat.mul_succ_r.
    rewrite H by constructor. rewrite IH by (intros; apply H; now constructor). omega.
Qed.

Lemma vector_sum_monotone_plus' (X : Type) (n : nat) (a : nat) (xs : Vector.t X n) (f1 f2 : X -> nat) :
  (forall x, Vector.In x xs -> f1 x + a <= f2 x) ->
  vector_sum f1 xs + a * n <= vector_sum f2 xs.
Proof.
  intros H. induction xs as [ | x n xs IH]; intros; cbn in *.
  - omega.
  - rewrite !vector_sum_shift. rewrite Nat.mul_succ_r.
    rewrite <- H by constructor. rewrite <- IH by (intros; apply H; now constructor). omega.
Qed.


Section MakeSingleTape.

  Variable (sigM : finType) (n : nat). (* We need [finType] here, because [contains_tapes] is defined over [finType] (bug) *)

  Derive makeSingleTape SuchThat (forall (T : tapes sigM n), contains_tapes (makeSingleTape T : tape _) T) As makeSingleTape_correct.
  Proof.
    subst makeSingleTape.
    instantiate (1 := fun T => _). cbn.
    intros. hnf. reflexivity.
  Qed.

  Lemma contains_tapes_injective (T : tapes sigM n) tp1 tp2 :
    contains_tapes tp1 T -> contains_tapes tp2 T -> tp1 = tp2.
  Proof. unfold contains_tapes. now intros -> ->. Qed.

  Lemma contains_tapes_iff (T : tapes sigM n) tp :
    contains_tapes tp T <-> tp = makeSingleTape T.
  Proof. split; intros ->; auto. apply makeSingleTape_correct. Qed.


  (** Size of [makeSingleTape] *)

  Definition Encode_tape_size (tp : tape sigM) : nat :=
    match tp with
    | niltape _ => 1
    | _ => sizeOfTape tp + 2
    end.

  Lemma Encode_tape_hasSize : forall (tp : tape sigM), size tp = Encode_tape_size tp.
  Proof. intros. unfold size. cbn. destruct tp; repeat progress (cbn; simpl_list); omega. Qed.

  Lemma Encode_tape_hasSize_le (tp : tape sigM) :
    Encode_tape_size tp <= sizeOfTape tp + 2.
  Proof. destruct tp; cbn -[sizeOfTape]; omega. Qed.


  Lemma Encode_tapes_hasSize :
    forall (T : tapes sigM n), size T = vector_sum (fun t => Encode_tape_size t + 1) T + 1.
  Proof.
    intros T.
    unfold size. cbn. unfold encode_tapes. cbn.
    setoid_rewrite Encode_list_hasSize with (cX := Encode_tape sigM).
    induction T as [ | t n T IH]; cbn; intros.
    - omega.
    - rewrite Encode_tape_hasSize. rewrite vector_sum_shift. rewrite IH. omega.
  Qed.

  Lemma makeSingleTape_sizeOfTape (T : tapes sigM n) :
    sizeOfTape (makeSingleTape T) <= vector_sum (fun tp => sizeOfTape tp + 2) T + n + 3.
  Proof.
    unfold tapes in *. unfold makeSingleTape. cbn. simpl_list. cbn.
    setoid_rewrite Encode_tapes_hasSize. ring_simplify.
    apply add_le_mono; auto.
    transitivity (vector_sum (fun tp : tape (eqType_X (type sigM)) => sizeOfTape tp + 2) T + (1 * n)); try nia.
    apply vector_sum_monotone_plus.
    intros t _. now rewrite Encode_tape_hasSize_le.
  Qed.

  (** Exact version *)
  Lemma makeSingleTape_sizeOfTape' (T : tapes sigM n) :
    sizeOfTape (makeSingleTape T) = vector_sum (fun tp => Encode_tape_size tp + 1) T + 3.
  Proof.
    unfold tapes in *. unfold makeSingleTape. cbn. simpl_list. cbn.
    setoid_rewrite Encode_tapes_hasSize. now ring_simplify.
  Qed.

  Lemma isRight_size_hasSize (tp : tape sigM) (s : nat) :
    isRight_size tp s ->
    Encode_tape_size tp <= s + 3.
  Proof. intros (x&ls&->&Hs). cbn. simpl_list; cbn. ring_simplify. now rewrite Hs. Qed.

End MakeSingleTape.


Lemma makeSingleTape_size' (sigM : finType) (n : nat) (T : tapes sigM n) :
  Encode_tape_size (makeSingleTape T) = vector_sum (fun tp => Encode_tape_size tp + 1) T + 5.
Proof.
  unfold makeSingleTape. repeat (cbn; simpl_list).
  change (| encode_tapes T |) with (size T).
  setoid_rewrite Encode_tapes_hasSize.
  now ring_simplify.
Qed.

Lemma makeSingleTape_size (sigM : finType) (n : nat) (T : tapes sigM n) :
  size (makeSingleTape T) = vector_sum (fun tp => Encode_tape_size tp + 1) T + 5.
Proof. setoid_rewrite Encode_tape_hasSize. apply makeSingleTape_size'. Qed.


(*
Definition sigTM (sigM : finType) (n : nat) (M : mTM sigM n) : finType := sigM.
Arguments sigTM {sigM n} M.
*)


Lemma vector_1_eta (X : Type) (v : Vector.t X 1) :
  exists x, v = [| x |].
Proof. destruct_vector. eauto. Qed.


Lemma graph_of_fun_ext (A : finType) (B : Type) (f1 f2 : A -> B) :
  (forall (a : A), f1 a = f2 a) ->
  graph_of_fun f1 = graph_of_fun f2.
Proof.
  intros.
  unfold graph_of_fun.
  apply List.map_ext.
  intros. f_equal. apply H.
Qed.


Local Arguments liftState {n sig F1 F2 pM} (l q).


Section StateWhile_irrelevant.
  Variable sig : finType.

  Variable F1 F2 : finType.
  Variable pM : F1 -> pTM sig (F1 + F2) 1.
  Hypothesis (defF : inhabitedC F2).

  Lemma StateWhile_graph_irrelevant (l1 l2 : F1) :
    graph_of_TM (projT1 (StateWhile pM l1)) = graph_of_TM (projT1 (StateWhile pM l2)).
  Proof. unfold graph_of_TM. reflexivity. Qed.

End StateWhile_irrelevant.


Section StateWhile_irrelevant'.
  Variable sig : finType.
  Variable n : nat.

  Variable F1 F2 : finType.
  Variable pM : F1 -> pTM sig (F1 + F2) n.
  Hypothesis (defF : inhabitedC F2).

  Lemma StateWhile_halt_irrelevant (l1 l2 : F1) q :
    halt (projT1 (StateWhile pM l1)) (liftState l1 q) = halt (projT1 (StateWhile pM l2)) (liftState l1 q).
  Proof. reflexivity. Qed.

  Lemma StateWhile_halt_irrelevant' (l1 l2 : F1) (q : StateWhile_states pM) :
    halt (projT1 (StateWhile pM l1)) q = halt (projT1 (StateWhile pM l2)) q.
  Proof. reflexivity. Qed.

  Lemma StateWhile_index_irrelevant (l1 l2 : F1) q :
    index (liftState l1 q : states (projT1 (StateWhile pM l1))) =
    index (liftState l1 q : states (projT1 (StateWhile pM l2))).
  Proof. reflexivity. Qed.

  Lemma StateWhile_liftStart_halt (l1 : F1) (l2 : F2) (q : states (projT1 (pM l1))) :
    projT2 (pM l1) q = inr l2 ->
    halt (projT1 (StateWhile pM l1)) (liftState l1 q) = halt _ q.
  Proof. intros H. unfold halt at 1, StateWhile; cbn. unfold StateWhile_halt; cbn. rewrite H. now rewrite andb_true_r. Qed.

End StateWhile_irrelevant'.




(** We need an injection from states of [M] to states of [M'] *)
Section M2M_Retract.

  Variable (sigM F : finType) (n : nat).
  Variable (pM : pTM sigM F n).
  Notation M := (projT1 pM).
  Notation pM' := (ToSingleTape pM).
  Notation M' := (projT1 pM').

  Definition ToSingleTape_Loop_inj (q q' : states (projT1 pM)) : states (projT1 (Loop q')).
  Proof. apply StateWhile.liftState with (l := q). apply start. Defined.

  Definition ToSingleTape_inj (q : states (projT1 pM)) : states (projT1 pM').
  Proof. apply ToSingleTape_Loop_inj. apply q. Defined.

  Lemma ToSingleTape_Loop_graph (q q' : states (projT1 pM)) :
    graph_of_TM (projT1 (Loop q)) = graph_of_TM (projT1 (Loop q')).
  Proof. apply StateWhile_graph_irrelevant. Qed.


  Lemma ToSingleTape_Loop_halt (q1 q2 : states (projT1 pM)) q :
    halt (projT1 (Loop q1)) (ToSingleTape_Loop_inj q q1) = halt (projT1 (Loop q2)) (ToSingleTape_Loop_inj q q2).
  Proof.
    unfold Loop.
    unfold ToSingleTape_Loop_inj.
    erewrite <- StateWhile_halt_irrelevant.
    erewrite StateWhile_halt_irrelevant.
    reflexivity.
  Qed.
  (* Wow, that was tricky to convince Coq that we can apply the lemma [StateWhile_halt_irrelevant]... *)

  Lemma ToSingleTape_Loop_index (q1 q2 q : states (projT1 pM)) :
    index (ToSingleTape_Loop_inj q q1) = index (ToSingleTape_Loop_inj q q2).
  Proof.
    unfold ToSingleTape_Loop_inj.
    setoid_rewrite <- StateWhile_index_irrelevant.
    setoid_rewrite -> StateWhile_index_irrelevant.
    reflexivity.
    Unshelve. auto.
  Qed.
  (* I am glad that (almost) the same trick worked here *)


End M2M_Retract.


Section MoreDominationLemmas.
  
  Lemma dominatedWith_add' (c1 c2 : nat) (A B C D : nat) :
    A <=(c1) C ->
    B <=(c2) D ->
    A + B <=(c1 + c2) C + D.
  Proof. unfold dominatedWith. nia. Qed.

  Lemma dominatedWith_S''' (a b c : nat) :
    S a <=(c) b ->
    a <=(S c) b.
  Proof. unfold dominatedWith. nia. Qed.

  Lemma dominatedWith_mult (c1 c2 : nat) (A B C D : nat) :
    A <=(c1) C ->
    B <=(c2) D ->
    A * B <=(c1 * c2) C * D.
  Proof. unfold dominatedWith. nia. Qed.

  Corollary dominatedWith_quad (c1 : nat) (A C : nat) :
    A <=(c1) C ->
    A * A <=(c1 * c1) C * C.
  Proof. intros. now apply dominatedWith_mult. Qed.

  Corollary dominatedWith_mult3 (c1 c2 c3 : nat) (A B C D E F : nat) :
    A <=(c1) D ->
    B <=(c2) E ->
    C <=(c3) F ->
    A * B * C <=(c1 * c2 * c3) D * E * F.
  Proof.
    intros. apply dominatedWith_mult.
    - now apply dominatedWith_mult.
    - assumption.
  Qed.

  Corollary dominatedWith_cube (c : nat) (A D : nat) :
    A <=(c) D ->
    A * A * A <=(c * c * c) D * D * D.
  Proof. intros. now apply dominatedWith_mult3. Qed.

End MoreDominationLemmas.


Local Existing Instance Encode_graph.

(** Single-tape and instantiated version of [Univ], [U]. At this point, the input of [U] is just an arbitrary single-tape machine [M]. *)
Section U.

  Variable (sigM : finType). (** The alphabet of the simulated single-tape machine *)
  Variable (F : finType). (** The label-type of the simulated single-tape machine *)

  Hypothesis (inhSigM : inhabitedC sigM). (** This is only a technical assumption. *)

  (** Instantiate [Univ] with its alphabet and retractions. *)
  Definition sigUniv' := FinType(EqType(sigList (sigPair (sigPair (option sigM) sigState) (sigPair (option (sigM) * move) sigState)))).
  Definition sigUniv : finType :=  sigUniv' ^+.
  Definition retr_sigSimGraph_sigUniv : Retract (sigList (sigPair (sigPair (option sigM) sigState) (sigPair (option (sigM) * move) sigState))) sigUniv' :=
    Retract_id _.
  Existing Instance retr_sigSimGraph_sigUniv.
  Definition retr_sigSimTape_sigUniv : Retract sigM sigUniv' := ltac:(eauto).
  Existing Instance retr_sigSimTape_sigUniv.
  Definition Univ : pTM sigUniv unit 6 := @Univ sigM sigUniv' retr_sigSimGraph_sigUniv retr_sigSimTape_sigUniv.

  (*
  Check Univ : pTM sigUniv unit 6.
  Check Univ : pTM sigUniv'^+ unit 6.
*)

  (** The single-tape version of [Univ] for alphabet [sigM] *)
  Definition U := ToSingleTape Univ.
  Definition sigU := ltac:(lazymatch type of U with pTM ?sigU _ _ => exact sigU end).
(*  Check U : pTM sigU unit 1. *)


  (*
  (** The simulated multi-tape machine over alphabet [sigM] *)
  Variable (pM : pTM sigM F 1).
  Notation M := (projT1 pM).
   *)


  (** Encode [pM] and the initial tape [T] to a tape of [U]. *)
  Definition initTapes_U (M : mTM sigM 1) (T : tape sigM) : tape sigU :=
    let tp := T in (* The tapes compressed into a single-tape *)
    let T_univ := makeUnivTapes _ _ M tp in
    makeSingleTape T_univ.

  (** [contains_conf_U] is a predicate for [U] that says that the tape [t] "contains" the transition function for [M] and the simulated tapes [T : tapes sigM n]. *)
  Definition contains_conf_Univ (M : mTM sigM 1) (T_univ : tapes sigUniv 6) (q : states M) (T : tape sigM) : Prop :=
    containsWorkingTape _ T_univ[@Fin0] T /\
    containsTrans _ T_univ[@Fin1] M /\
    containsState _ T_univ[@Fin2] q /\
    (forall (i : Fin.t 3), isRight T_univ[@FinR 3 i]).

  (** Variant with size. Note that [s_Univ[@Fin0]] is irrelevant. *)
  Definition contains_conf_Univ_size (M : mTM sigM 1) (T_univ : tapes sigUniv 6) (q : states M) (T : tape sigM) (s_Univ : Vector.t nat 6) : Prop :=
    containsWorkingTape _ T_univ[@Fin0] T /\
    containsTrans_size _ T_univ[@Fin1] M s_Univ[@Fin1] /\
    containsState_size _ T_univ[@Fin2] q s_Univ[@Fin2] /\
    (forall (i : Fin.t 3), isRight_size T_univ[@FinR 3 i] s_Univ[@FinR 3 i]).

  Lemma contains_conf_Univ_size_contains_conf_Univ (M : mTM sigM 1) (T_univ : tapes sigUniv 6) (q : states M) (T : tape sigM) (s_Univ : Vector.t nat 6) :
    contains_conf_Univ_size T_univ q T s_Univ ->
    contains_conf_Univ      T_univ q T.
  Proof.
    intros (H0&H1&H2&H3). repeat split.
    - apply H0.
    - eapply containsTrans_size_containsTrans; eauto.
    - eapply containsState_size_containsState; eauto.
    - intros. eapply isRight_size_isRight. apply H3.
  Qed.

  Definition contains_conf_U' (M : mTM sigM 1) (t : tape sigU) (T_univ : tapes sigUniv 6) (q : states M) (T : tape sigM) : Prop :=
    contains_tapes t T_univ /\ contains_conf_Univ T_univ q T.

  Definition contains_conf_U'_size (M : mTM sigM 1) (t : tape sigU) (T_univ : tapes sigUniv 6) (q : states M) (T : tape sigM) (s_Univ : Vector.t nat 6) : Prop :=
    contains_tapes t T_univ /\ contains_conf_Univ_size T_univ q T s_Univ.

  Definition contains_conf_U (M : mTM sigM 1) (t : tape sigU) (q : states M) (T : tape sigM) : Prop :=
    exists (T_univ : tapes sigUniv 6), contains_conf_U' t T_univ q T.

  Definition contains_conf_U_size (M : mTM sigM 1) (t : tape sigU) (q : states M) (T : tape sigM) (s_Univ : Vector.t nat 6) : Prop :=
    exists (T_univ : tapes sigUniv 6), contains_conf_U'_size t T_univ q T s_Univ.


  Lemma initTapes_U_correct (M : mTM sigM 1) (T : tape sigM) :
    contains_conf_U (initTapes_U M T) (start M) T.
  Proof.
    unfold contains_conf_U, initTapes_U. cbn.
    eexists. split.
    - apply makeSingleTape_correct.
    - apply makeUnivTapes_correct.
  Qed.

  Lemma initTapes_U_correct_size (M : mTM sigM 1) (T : tape sigM) :
    contains_conf_U_size (initTapes_U M T) (start M) T (Vector.const 0 _).
  Proof.
    unfold contains_conf_U, initTapes_U. cbn.
    eexists. split.
    - apply makeSingleTape_correct.
    - repeat split.
      + cbn. apply makeUnivGraphTape_correct_size.
      + cbn. apply makeUnivStartStateTape_correct_size.
      + intros i. cbn. destruct_fin i; cbn; apply initRight_isRight_size.
  Qed.


  (** Build correctness and termination relations for [U] *)

  Definition U_steps (M : mTM sigM 1) (T_Univ : tapes sigUniv 6) (q_M : states M) (T : tape sigM) (k_M : nat) :=
    Loop_steps (start (projT1 Univ)) T_Univ (Univ_steps q_M T k_M).

  Definition U_T : tRel sigU 1 :=
    fun tp k =>
      exists (M : mTM sigM 1) (T_Univ : tapes sigUniv 6) (T : tape sigM) (q_M : states M) (c_M : mconfig sigM (states M) 1) (k_M : nat),
        contains_conf_U' tp[@Fin0] T_Univ q_M T /\
        loopM _ (mk_mconfig q_M [|T|]) k_M = Some c_M /\
        U_steps T_Univ q_M T k_M <= k.

  Lemma U_terminatesIn : projT1 U ↓ U_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold U. apply ToSingleTape_Terminates. }
    {
      intros tp k H. hnf in H. destruct H as (M&T_Univ&T&q_M&c_M&k_M&HCont&M_halt&Hk).
      set (pM := (M; fun _ => tt) : pTM sigM (FinType(EqType unit)) 1).
      hnf in HCont. destruct HCont as (HCont_Univ&HCont1&HCont2&HCont3&HCont4).
      destruct c_M as (M_finalState&M_finalTapes). pose proof vector_1_eta M_finalTapes as (M_finalTape&->).

      pose proof @Univ_Terminates sigM sigUniv' retr_sigSimGraph_sigUniv retr_sigSimTape_sigUniv as Univ_term. hnf in Univ_term.
      evar (ktamtam : nat).
      specialize Univ_term with (tin := T_Univ) (k := ktamtam).
      spec_assert Univ_term as (Univ_finalConf&Univ_halt).
      { hnf. subst ktamtam.
        exists M.
        do 5 eexists. repeat split.
        - apply HCont1. (* working tape *)
        - unfold containsTrans in HCont2|-*. (* transition function *)
          replace (graph_of_TM (projT1 (Loop (q_M : states (projT1 pM))))) with (graph_of_TM (projT1 (ToSingleTape pM))); [ apply HCont2 | ].
          apply ToSingleTape_Loop_graph.
        - (* state [q_M] *)
          clear_except HCont3.
          unfold containsState in HCont3|-*.
          unfold ToSingleTape, ToSingleTape_inj in HCont3.
          apply HCont3.
        - apply HCont4. (* internal tapes *)
        - apply M_halt.
        - reflexivity. (* instantiate [ktamtam] *)
      }

      hnf. exists T_Univ. do 2 eexists. repeat split.
      - apply Univ_halt.
      - apply HCont_Univ.
      - rewrite <- Hk. subst ktamtam. reflexivity.
    }
  Qed.


  (** First, we write a running time function that still depends on the original input tape [T : tape sigM]. [k] is the number of steps that [M] needs on input [T] *)
  Definition fp (M : mTM sigM 1) (T : tape sigM) (k : nat) : nat :=
    let k_Univ := Univ_steps (start M) T k in (* steps that [Univ] needs *)
    let T_Univ := makeUnivTapes _ _ M T in (* Tapes for [Univ] *)
    ToSingleTape_steps Univ T_Univ k_Univ. (* Steps of [U] *)


  (*
  Hypthesis (inhSigM : inhabitedC sigM).
  (** Because the asymtopic behaviour of [fp] only depends on the size of the tapes, we will just insert bogus tapes with the corresponding tapes size. *)
  Definition f (M : mTM sigM 1) : nat * nat -> nat := fun '(k, s) => fp M (bogus_tape s) k.
*)
(*
  Check (projT1 U) : mTM sigU 1.
  Check forall (tp tp' : tape sigU), terminates (projT1 U) [|tp|] 42 [|tp'|].
*)
  (** [fp] is literally only another definition for [U_steps] *)
  Lemma fp_eq : forall M (T : tape sigM) k, fp M T k = U_steps (makeUnivTapes _ _ M T) (start M) T k.
  Proof. intros. reflexivity. Qed.


  (** Not the best approximation, but it's a beginning *)
  Lemma fp_nice1 M :
    { c : nat | forall (T : tape sigM) k,
        fp M T k
        <=(c)
           let x := (size (vector_to_list (makeUnivTapes retr_sigSimGraph_sigUniv retr_sigSimTape_sigUniv M T)) + 6 * Univ_steps (start M) T k) in
           x * x * Univ_steps (start M) T k
    }.
  Proof.
    unfold fp.
    eexists. intros.
    eapply dominatedWith_trans.
    - apply (proj2_sig (@M2MBounds.Loop_steps_nice)).
    - apply dominatedWith_solve. reflexivity.
  Qed.


  (** Apply bounds for [Univ_steps] *)
  Lemma fp_nice2 M :
    { c : nat | forall (T : tape sigM) k,
        fp M T k
        <=(c)
           let x := (size (vector_to_list (makeUnivTapes retr_sigSimGraph_sigUniv retr_sigSimTape_sigUniv M T)) + size k * size (graph_of_TM M)) in
           x * x * (size k * size (graph_of_TM M) * size (Cardinality.Cardinality (states M)))
    }.
  Proof.
    eexists. intros. eapply dominatedWith_trans. apply (proj2_sig (fp_nice1 M)). apply dominatedWith_mult.
    - apply dominatedWith_quad. domWith_approx.
      eapply dominatedWith_trans.
      apply (proj2_sig (UnivBounds.Univ_nice.Univ_steps_nice)).
      domWith_approx.
      apply dominatedWith_solve. enough (1 <= size (graph_of_TM M)) by nia. apply UnivBounds.Univ_nice.Encode_graph_hasSize_ge1.
    - apply (proj2_sig (UnivBounds.Univ_nice.Univ_steps_nice)).
  Qed.

  (** Throw away all constants that depend on [M] *)
  Lemma fp_nice3 M :
    { c : nat | forall (T : tape sigM) k,
        fp M T k
        <=(c)
           let x := (size (vector_to_list (makeUnivTapes retr_sigSimGraph_sigUniv retr_sigSimTape_sigUniv M T)) + size k) in
           x * x * size k
    }.
  Proof.
    eexists. intros. eapply dominatedWith_trans. apply (proj2_sig (fp_nice2 M)). apply dominatedWith_mult.
    - apply dominatedWith_quad. domWith_approx.
    - domWith_approx.
  Qed.

  Lemma makeUnivWorkingTape_size (T : tape sigM) :
    size (makeUnivWorkingTape retr_sigSimTape_sigUniv T) = size T.
  Proof.
    setoid_rewrite Encode_tape_hasSize. unfold makeUnivWorkingTape. cbn.
    destruct T; cbn -[sizeOfTape]; auto.
    all: repeat progress (cbn; simpl_list); auto.
  Qed.

  Lemma makeUnivWorkingTape_size' (T : tape sigM) :
    Encode_tape_size (makeUnivWorkingTape retr_sigSimTape_sigUniv T) = size T.
  Proof. rewrite <- Encode_tape_hasSize. apply makeUnivWorkingTape_size. Qed.

  Lemma tape_size_nice :
    { c | forall (T : tape sigM), size T <=(c) sizeOfTape T + 1 }.
  Proof.
    eexists. intros.
    setoid_rewrite Encode_tape_hasSize. unfold Encode_tape_size. domWith_match; cbn; domWith_approx.
    apply dominatedWith_S'; domWith_approx. omega.
  Qed.

  Lemma makeUnivTapes_size_nice M :
    { c | forall (T : tape sigM), size (makeUnivTapes retr_sigSimGraph_sigUniv retr_sigSimTape_sigUniv M T) <=(c) sizeOfTape T + 1 }.
  Proof.
    eexists. intros.
    unfold makeUnivTapes. cbn.
    setoid_rewrite Encode_tapes_hasSize. cbn -[sizeOfTape].
    domWith_approx.
    eapply dominatedWith_trans. apply dominatedWith_solve. apply Nat.eq_le_incl.
    apply makeUnivWorkingTape_size'. apply (proj2_sig tape_size_nice).
  Qed.


  (** Simplify [size (vector_to_list ...)] *)
  Lemma fp_nice4 M :
    { c : nat | forall (T : tape sigM) k,
        fp M T k
        <=(c)
           let x := sizeOfTape T + size k in
           x * x * size k
    }.
  Proof.
    eexists. intros. eapply dominatedWith_trans. apply (proj2_sig (fp_nice3 M)). apply dominatedWith_mult.
    - apply dominatedWith_quad. domWith_approx.
      eapply dominatedWith_trans.
      + apply (proj2_sig (makeUnivTapes_size_nice M)).
      + domWith_approx. apply dominatedWith_solve. rewrite Encode_nat_hasSize. omega.
    - domWith_approx.
  Qed.

  (** Let's get rid of [size] and [let] and write it in one line *)
  Lemma fp_nice M :
    { c : nat | forall (T : tape sigM) k, fp M T k <=(c) (sizeOfTape T + k + 1) * (sizeOfTape T + k + 1) * (k + 1) }.
  Proof.
    eexists. intros. eapply dominatedWith_trans. apply (proj2_sig (fp_nice4 M)). apply dominatedWith_mult.
    - apply dominatedWith_quad. domWith_approx. setoid_rewrite Encode_nat_hasSize. domWith_approx.
    - setoid_rewrite Encode_nat_hasSize. domWith_approx.
  Qed.


  (** Correctness *)

  (* TODO: Enrich relation with a size function *)
  Definition U_Rel : pRel sigU unit 1 :=
    fun tin '(_, tout) =>
      forall (pM : pTM sigM F 1) (T : tape sigM) (q_M : states (projT1 pM)) (s_Univ : Vector.t nat 6),
        contains_conf_U_size tin[@Fin0] q_M T s_Univ ->
        exists (T' : tape sigM) (qout_M : states (projT1 pM)) (k_M : nat),
          loopM _ (mk_mconfig q_M [|T|]) k_M = Some (mk_mconfig qout_M [|T'|]) /\
          contains_conf_U_size tout[@Fin0] qout_M T' (apply_sizeFun (Univ_size T q_M k_M) s_Univ).

  Lemma U_Realises : U ⊨ U_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold U. apply ToSingleTape_Realise. }
    {
      intros tin ([], tout) HU. hnf in HU. hnf. intros pM T q_M s_Univ (T_Univ&H_U&(H_Conf1&HConf2&HConf3&HConf4)).
      cbn in HU. specialize HU with (1 := H_U) as (Univ_finalConf&k_Univ&Univ_term&Univ_resultCont&_).
      pose proof Univ_Realise Univ_term as Univ_correct. hnf in Univ_correct.
      specialize Univ_correct with (M := projT1 pM) (tp := T) (q := q_M).

      modpon Univ_correct. (* This needs a bit help, because there are sizes involved *)
      { instantiate (1 := [|_;_;_|]). intros i; specialize (HConf4 i); destruct_fin i; cbn in *; isRight_mono. }

      cbn in Univ_correct. destruct Univ_correct as (k_M&oconf_M&M_term&Univ_oconfCont1&Univ_oconfCont2&Univ_oconfCont3&Univ_oconfCont4).
      destruct oconf_M as [qout_M Ts']. pose proof vector_1_eta Ts' as (T'&->).

      exists T', qout_M, k_M. split.
      - apply M_term.
      - hnf. exists (ctapes Univ_finalConf). hnf. split. apply Univ_resultCont. repeat split. (* This needs a bit help again *)
        { apply Univ_oconfCont1. }
        { unfold containsTrans, containsTrans_size in *. contains_ext. }
        { unfold containsState, containsState_size in *. contains_ext. }
        { intros i; specialize (Univ_oconfCont4 i); destruct_fin i; cbn in *; isRight_mono. }
    }
  Qed.


  (** We only do space-analysis for [Univ] now, because the size of the [sigU] tapes is directly determined by the tapes of [Univ] *)
  (* )Check UnivSpaceBounds.Univ_size_nice'. *)


  (* TODO: Maybe simplify this space bound a bit: every tape of [Univ], except the object tape, is bounded by a constant (that depends on M). *)

End U.


Lemma loopM_halt (sigM : finType) (n : nat) (M : mTM sigM n) (iconf oconf : mconfig sigM (states M) n) (k : nat) :
  loopM M iconf k = Some oconf ->
  halt M (cstate oconf) = true.
Proof.
  destruct iconf, oconf. cbn in *.
  unfold loopM, haltConf in *.
  intros H % loop_fulfills. cbn in *. auto.
Qed.

Lemma loopM_halt' (sigM : finType) (n : nat) (M : mTM sigM n) (iconf : mconfig sigM (states M) n) ostate otapes (k : nat) :
  loopM M iconf k = Some (mk_mconfig ostate otapes) ->
  halt M ostate = true.
Proof. apply loopM_halt. Qed.


Section Sum_bounded_by_max.

  Lemma list_sum_le_upperBound_times_length (X : Type) (f : X -> nat) (xs : list X) (y : X) :
    (forall x, In x xs -> f x <= f y) ->
    list_sum f xs <= f y * length xs.
  Proof.
    induction xs as [ | x xs IH]; intros; cbn in *.
    - omega.
    - rewrite list_sum_shift. rewrite H by auto. rewrite IH by auto. nia.
  Qed.

  Lemma list_sum_le_max_times_length (X : Type) (f : X -> nat) (xs : list X) :
    list_sum f xs <= max_list_map f xs * length xs.
  Proof.
    enough (xs <> nil -> list_sum f xs <= max_list_map f xs * length xs).
    { destruct xs. reflexivity. apply H. congruence. }
    intros Hnil.
    pose proof (max_list_map_In f Hnil) as (x&H&?).
    rewrite <- H.
    apply list_sum_le_upperBound_times_length with (xs := xs).
    intros. rewrite H. now apply max_list_map_ge.
  Qed.

End Sum_bounded_by_max.




Section MakeSingleTape_Bounded_by_sizeOfmTapes.
  Variable (sig : finType) (n : nat).

  (** We've already proven that [sizeOfTape (makeSingleTape T)] is the sum of the tape sizes (plus some constant) *)
  (* )Check makeSingleTape_sizeOfTape. *)

  Lemma tam (T : tapes sig n) :
    max_list_map (fun t : tape sig => Encode_tape_size t + 1) (vector_to_list T) <= sizeOfmTapes T + 3.
  Proof.
    apply max_list_map_lower_bound.
    intros.
    rewrite Encode_tape_hasSize_le.
    ring_simplify.
    apply add_le_mono; auto.
    rewrite sizeOfmTapes_max_list_map.
    now apply max_list_map_ge.
  Qed.

  Lemma Encode_tapes_hasSize_le_sizeOfmTapes (T : tapes sig n) :
    size T <= sizeOfmTapes T * n + n * 3 + 2.
  Proof.
    cbn.
    rewrite Encode_tapes_hasSize.
    setoid_rewrite <- vector_to_list_sum.
    rewrite list_sum_le_max_times_length.
    rewrite vector_to_list_length.
    apply add_le_mono; auto.
    rewrite tam.
    ring_simplify.
    nia.
  Qed.

  Lemma tamtam (T : tapes sig n) :
    max_list_map (fun tp : tape sig => sizeOfTape tp + 2) (vector_to_list T) <= sizeOfmTapes T + 2.
  Proof.
    apply max_list_map_lower_bound.
    intros t ? (*% vector_to_list_In*).
    apply add_le_mono; auto.
    rewrite sizeOfmTapes_max_list_map.
    now apply max_list_map_ge.
  Qed.

  Lemma makeSingleTape_sizeOfmTapes (T : tapes sig n) :
    sizeOfTape (makeSingleTape T) <= sizeOfmTapes T * n + n * 3 + 3.
  Proof.
    rewrite makeSingleTape_sizeOfTape.
    rewrite <- vector_to_list_sum.
    rewrite list_sum_le_max_times_length.
    rewrite vector_to_list_length.
    apply add_le_mono; auto.
    rewrite tamtam.
    ring_simplify. nia.
  Qed.

End MakeSingleTape_Bounded_by_sizeOfmTapes.

(* TODO *)




(** Now, we consider [U] again, but we use [ToSingleTape] as the "encoding" for a multi-tape machine [M]. *)
Section UnivMultiTimeSpaceTheorem.

  Variable (sigM : finType). (** The alphabet of the simulated multi-tape machine *)
  Variable (n : nat). (** The number of tapes of the simulated machine *)
  Hypothesis (n_ge1 : 1 <= n). (** Another technical assumption *)

  (** The alphabet for Multi-to-Mono compiled machine *)
  Definition sigM' := (FinType(EqType(boundary + sigList (sigTape sigM)))).

  (** Instantiate [Univ] and [U] with the alphabet for [M' := ToSingleTape M]. *)
  Notation MUniv := (Univ sigM').
  Notation sigMUniv := (sigUniv sigM').

  Notation sigMU := (sigU sigM').
  Definition MU : pTM sigMU unit 1 := U sigM'.


  (** The simulated multi-tape machine over alphabet [sigM] *)
  Variable (M : mTM sigM n).
  (** We use the states of [M] as labels for [M]. When [M'] terminated, we know exactly in which state [M] terminated. *)
  Definition pM : pTM sigM (states M) n := (M; id).

  Notation pM' := (ToSingleTape pM).
  Notation M' := (projT1 pM').
  (* )Check M' : mTM sigM' 1. *)

  Notation "'castState' q" := (q : (states (projT1 pM))) (at level 1).

  (** Encode [ToSingleTape M] and the initial tapes of [t] to a tape of [U]. *)
  Definition initTapes_MU (T : tapes sigM n) : tape sigMU :=
    initTapes_U (projT1 (ToSingleTape pM)) (makeSingleTape T).

  Definition contains_conf_MU' (t : tape sigMU) (T_univ : tapes sigMUniv 6) (q_M' : states M') (T : tapes sigM n) : Prop :=
    contains_tapes t T_univ /\ contains_conf_Univ T_univ q_M' (makeSingleTape T).

  Definition contains_conf_MU'_size (t : tape sigMU) (T_univ : tapes sigMUniv 6) (q_M' : states M') (T : tapes sigM n) (s_Univ : Vector.t nat 6) : Prop :=
    contains_tapes t T_univ /\ contains_conf_Univ_size T_univ q_M' (makeSingleTape T) s_Univ.

  Definition contains_conf_MU (t : tape sigMU) (q_M' : states M') (T : tapes sigM n) : Prop :=
    exists (T_univ : tapes (sigUniv sigM') 6), contains_conf_MU' t T_univ q_M' T.

  Definition contains_conf_MU_size (t : tape sigMU) (q_M' : states M') (T : tapes sigM n) (s_Univ : Vector.t nat 6) : Prop :=
    exists (T_univ : tapes (sigUniv sigM') 6), contains_conf_MU'_size t T_univ q_M' T s_Univ.


  Lemma contains_conf_MU'_size_contains_conf_MU' t T_univ q_M' T s_Univ :
    contains_conf_MU'_size t T_univ q_M' T s_Univ ->
    contains_conf_MU'      t T_univ q_M' T.
  Proof.
    intros (H0&H1). split.
    - apply H0.
    - eapply contains_conf_Univ_size_contains_conf_Univ. apply H1.
  Qed.

  Lemma contains_conf_MU_size_contains_conf_MU t q_M' T s_Univ :
    contains_conf_MU_size t q_M' T s_Univ ->
    contains_conf_MU      t q_M' T.
  Proof. intros (T_univ&H). exists T_univ. eapply contains_conf_MU'_size_contains_conf_MU'. apply H. Qed.


  Lemma initTapes_MU_correct (T : tapes sigM n)  :
    contains_conf_MU (initTapes_MU T) (start M') T.
  Proof. apply initTapes_U_correct. Qed.

  Lemma initTapes_MU_correct_size (T : tapes sigM n)  :
    contains_conf_MU_size (initTapes_MU T) (start M') T (Vector.const 0 6).
  Proof. apply initTapes_U_correct_size. Qed.




  (** Build correctness and termination relations for [U] *)

  Definition MU_steps (T_Univ : tapes sigMUniv 6) (T : tapes sigM n) (k_M : nat) :=
    U_steps T_Univ (start M') (makeSingleTape T) (Loop_steps (castState (start M)) T k_M).


  Definition MU_T : tRel sigMU 1 :=
    fun tp k =>
      exists (T_Univ : tapes sigMUniv 6) (T : tapes sigM n) (c_M : mconfig sigM (states M) n) (k_M : nat),
        contains_conf_MU' tp[@Fin0] T_Univ (start M') T /\
        loopM _ (initc M  T) k_M = Some c_M /\
        MU_steps T_Univ T k_M <= k.

  Lemma MU_terminatesIn : projT1 MU ↓ MU_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold MU. apply U_terminatesIn. }
    {
      intros tp k H. hnf in H. destruct H as (T_Univ&T&c_M&k_M&HCont&M_halt&Hk).
      hnf in HCont. destruct HCont as (HCont_Univ&HCont1&HCont2&HCont3&HCont4).
      destruct c_M as (M_finalState&M_finalTapes).

      pose proof Loop_Terminates (pM := pM) (q := start M) as M'_term. hnf in M'_term. unfold ToSingleTape_T, Loop_T in M'_term; hnf in M'_term.
      specialize (M'_term ([|makeSingleTape T|]) (Loop_steps (castState (start M)) T k_M)).
      spec_assert M'_term as (M'_finalConf&M'_halt).
      { do 3 eexists. repeat split; eauto. }
      destruct M'_finalConf as (M'_finalState&M'_finalTapes). pose proof vector_1_eta M'_finalTapes as (M'_finalTape&->).

      (* change (eqType_X (type (states (projT1 (Loop q_M))))) with (StateWhile_states (Step (pM:=pM))) in *. *)
      hnf.
      exists (projT1 (Loop (castState (start M)))).
      exists T_Univ.
      exists (makeSingleTape T).
      eexists. eexists (mk_mconfig _ [|_|]). eexists.
      repeat split.
      - auto.
      - auto.
      - auto. (* transition function *)
      - clear_except HCont3. (* state *)
        unfold containsState in HCont3|-*.
        unfold ToSingleTape, ToSingleTape_inj in HCont3.
        auto.
      - auto.
      - clear_except M'_halt. (* Loop *)
        unfold ToSingleTape.
        eauto.
      - rewrite <- Hk.
        unfold MU_steps, ToSingleTape_inj.
        reflexivity.
    }
  Qed.


  (* Instance sigM'_inhabited : inhabitedC sigM'. Proof. repeat econstructor. Qed. *)

  Definition Mfp : tapes sigM n -> nat -> nat := fun T k => fp M' (makeSingleTape T) (ToSingleTape_steps pM T k).
  (* Definition Mf : nat*nat->nat := fun '(k,s) => Mfp (bogus_tapes _ s) k. *)

  Lemma Mfp_eq : forall (T : tapes sigM n) k,
      Mfp T k =
      MU_steps (makeUnivTapes (retr_sigSimGraph_sigUniv _) (retr_sigSimTape_sigUniv _) M' (makeSingleTape T)) T k.
  Proof. reflexivity. Qed.


  (** Instance of [fp_nice] *)
  Lemma Mfp_nice0 :
    {c : nat | forall (T : tape sigM') (k : nat), fp M' T k <=(c) (sizeOfTape T + k + 1) * (sizeOfTape T + k + 1) * (k + 1)}.
  Proof. exact (fp_nice M'). Qed.

  (** This is still a direct corollary from [fp_nice] *)
  Lemma Mfp_nice1 :
    {c : nat | forall (T : tapes sigM n) (k : nat),
        let T' := makeSingleTape T in
        let k' := ToSingleTape_steps pM T k in
        Mfp T k <=(c) (sizeOfTape T' + k' + 1) * (sizeOfTape T' + k' + 1) * (k' + 1)}.
  Proof. eexists. intros. apply (proj2_sig (Mfp_nice0)). Qed.

  (** Simplify [ToSingleTape_steps] *)
  Lemma Mfp_nice2 :
    {c : nat | forall (T : tapes sigM n) (k : nat),
        let T' := makeSingleTape T in
        let k' := (size (vector_to_list T) + n * k) * (size (vector_to_list T) + n * k) * k in
        Mfp T k <=(c) (sizeOfTape T' + k' + 1) * (sizeOfTape T' + k' + 1) * (k' + 1)}.
  Proof.
    eexists. intros. eapply dominatedWith_trans. apply (proj2_sig Mfp_nice1).
    apply dominatedWith_mult3.
    - domWith_approx.
      + subst T'. apply dominatedWith_solve. nia.
      + eapply dominatedWith_trans.
        apply (proj2_sig (M2MBounds.Loop_steps_nice)).
        apply dominatedWith_solve.
        subst T' k'. nia.
    - domWith_approx.
      + subst T'. apply dominatedWith_solve. nia.
      + eapply dominatedWith_trans.
        apply (proj2_sig (M2MBounds.Loop_steps_nice)).
        apply dominatedWith_solve.
        subst T' k'. nia.
    - apply dominatedWith_add_r; [ | nia].
      eapply dominatedWith_trans.
      apply (proj2_sig M2MBounds.Loop_steps_nice).
      apply dominatedWith_solve. subst k'. nia.
  Qed.

  (** Simplify [sizeOfTape (makeSingleTape T)] *)

  (* )Check makeSingleTape_sizeOfmTapes. *)

  Lemma Mfp_nice3 :
    {c : nat | forall (T : tapes sigM n) (k : nat),
        let k' := (size (vector_to_list T) + n * k) * (size (vector_to_list T) + n * k) * k in
        Mfp T k <=(c) (sizeOfmTapes T + k' + 1) * (sizeOfmTapes T + k' + 1) * (k' + 1)}.
  Proof.
    eexists. intros. eapply dominatedWith_trans. apply (proj2_sig Mfp_nice2).
    apply dominatedWith_mult3.
    - subst k'. domWith_approx. setoid_rewrite makeSingleTape_sizeOfmTapes. domWith_approx.
    - subst k'. domWith_approx. setoid_rewrite makeSingleTape_sizeOfmTapes. domWith_approx.
    - subst k'. domWith_approx.
  Qed.


  (** Simplify [size (vector_to_list T)] and also remove [n] *)

  Lemma Mfp_nice :
    {c : nat | forall (T : tapes sigM n) (k : nat),
        let k' := (sizeOfmTapes T + k + 1) * (sizeOfmTapes T + k + 1) * k in
        Mfp T k <=(c) (sizeOfmTapes T + k' + 1) * (sizeOfmTapes T + k' + 1) * (k' + 1)}.
  Proof.
    eexists. intros. eapply dominatedWith_trans. apply (proj2_sig Mfp_nice3).
    apply dominatedWith_mult3.
    - subst k'. apply dominatedWith_add'. 2: apply dominatedWith_refl; constructor. apply dominatedWith_add'. 1: apply dominatedWith_refl; constructor. apply dominatedWith_mult3.
      + domWith_approx. change (size (vector_to_list T)) with (size T). setoid_rewrite Encode_tapes_hasSize_le_sizeOfmTapes. domWith_approx.
      + domWith_approx. change (size (vector_to_list T)) with (size T). setoid_rewrite Encode_tapes_hasSize_le_sizeOfmTapes. domWith_approx.
      + domWith_approx.
    - subst k'. apply dominatedWith_add'. 2: apply dominatedWith_refl; constructor. apply dominatedWith_add'. 1: apply dominatedWith_refl; constructor. apply dominatedWith_mult3.
      + domWith_approx. change (size (vector_to_list T)) with (size T). setoid_rewrite Encode_tapes_hasSize_le_sizeOfmTapes. domWith_approx.
      + domWith_approx. change (size (vector_to_list T)) with (size T). setoid_rewrite Encode_tapes_hasSize_le_sizeOfmTapes. domWith_approx.
      + domWith_approx.
    - subst k'. apply dominatedWith_add'. 2: apply dominatedWith_refl; constructor. apply dominatedWith_mult3.
      + domWith_approx. change (size (vector_to_list T)) with (size T). setoid_rewrite Encode_tapes_hasSize_le_sizeOfmTapes. domWith_approx.
      + domWith_approx. change (size (vector_to_list T)) with (size T). setoid_rewrite Encode_tapes_hasSize_le_sizeOfmTapes. domWith_approx.
      + domWith_approx.
  Qed.


  (*
  (** Finally, consider [Mf] and replace [sizeOfmTapes T] with [s] *)
  Lemma Mf_nice :
    {c : nat | forall k s,
        let k' := (s + k + 1) * (s + k + 1) * k in
        Mf (k, s) <=(c) (s + k' + 1) * (s + k' + 1) * (k' + 1)}.
  Proof.
    eexists. intros. cbn. eapply dominatedWith_trans. apply (proj2_sig Mfp_nice).
    apply dominatedWith_mult3.
    - subst k'. apply dominatedWith_add'. 2: apply dominatedWith_refl; constructor. apply dominatedWith_add'.
      + setoid_rewrite bogus_tapes_sizeOfmTapes. apply dominatedWith_solve. nia. nia.
      + setoid_rewrite bogus_tapes_sizeOfmTapes. apply dominatedWith_solve. nia. nia. nia.
    - subst k'. apply dominatedWith_add'. 2: apply dominatedWith_refl; constructor. apply dominatedWith_add'.
      + setoid_rewrite bogus_tapes_sizeOfmTapes. apply dominatedWith_solve. nia. nia.
      + setoid_rewrite bogus_tapes_sizeOfmTapes. apply dominatedWith_solve. nia. nia. nia.
    - subst k'. apply dominatedWith_add'. 2: apply dominatedWith_refl; constructor. apply dominatedWith_mult3.
      + domWith_approx. setoid_rewrite bogus_tapes_sizeOfmTapes. apply dominatedWith_solve. nia. nia.
      + domWith_approx. setoid_rewrite bogus_tapes_sizeOfmTapes. apply dominatedWith_solve. nia. nia.
      + domWith_approx.
  Qed.
   *)

  (** Extract the nice polynominal *)
  Definition Mf : nat*nat->nat :=
    fun '(k, s) =>
      let c := proj1_sig Mfp_nice in
      let k' := (s + k + 1) * (s + k + 1) * k in
      c * ((s + k' + 1) * (s + k' + 1) * (k' + 1)).

  (** We need this final bound in the End Theorem *)
  Lemma Mf_bounded :
    forall T k, Mfp T k <= Mf (k, sizeOfmTapes T).
  Proof.
    intros T k. unfold Mf.
    set (s := sizeOfmTapes T).
    set (c := proj1_sig Mfp_nice).
    set (k' := (s + k + 1) * (s + k + 1) * k).
    apply (proj2_sig Mfp_nice).
  Qed.


  (** Correctness *)

  Definition MU_size (T : tapes sigM n) (k_M' : nat) : Vector.t (nat->nat) 6 := Univ_size (makeSingleTape T) (start M') k_M'.

  Definition MU_Rel : pRel sigMU unit 1 :=
    fun tin '(_, tout) =>
      forall (T : tapes sigM n) (s_Univ : Vector.t nat 6),
        contains_conf_MU_size tin[@Fin0] (start M') T s_Univ ->
        exists (T' : tapes sigM n) (qout_M : states M) (qout_M' : states M') (k_M k_M' : nat),
          loopM _ (initc M T) k_M = Some (mk_mconfig qout_M T') /\
          loopM _ (initc M' [|makeSingleTape T|]) k_M' = Some (mk_mconfig qout_M' [|makeSingleTape T'|]) /\
          contains_conf_MU_size tout[@Fin0] qout_M' T' (apply_sizeFun (MU_size T k_M') s_Univ) /\
          projT2 pM' qout_M' = qout_M. (** We can show that the final state of [M'] corresponds to the final state of [M]. However, [qout_M' <> ToSingleTape_inj qout_M]. *)

  Lemma MU_Realises : MU ⊨ MU_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold MU. apply U_Realises. }
    {
      intros tin ([], tout) HU. hnf in HU. hnf. intros T s_Univ HUniv.
      unfold contains_conf_U_size at 1, contains_conf_U'_size at 1 in HU.
      destruct HUniv as (T_Univ&H_contUnic&HCont1&HCont2&HCont3&HCont4).

      specialize HU with (pM := pM') (T := makeSingleTape T) (q_M := start _) (s_Univ := s_Univ).
      spec_assert HU as (M'_finalTapes&M'_finalState&U_k&M'_halt&M'_finalContains).
      {
        eexists; split; eauto.
        hnf. repeat split; auto.
      }

      pose proof Loop_Realise (pM := pM) (q := start _) as M'_real. hnf in M'_real. unfold ToSingleTape_T, Loop_T in M'_real; hnf in M'_real.
      evar (M'_outc' : mconfig (sigList (sigTape (eqType_X (type sigM)))) ^+ (states M') 1).
      specialize (M'_real ([|makeSingleTape T|]) U_k M'_outc').
      spec_assert M'_real.
      {
        subst M'_outc'. instantiate (1 := mk_mconfig _ _).
        eauto.
      }
      subst M'_outc'.
      hnf in M'_real. cbn in M'_real.
      specialize M'_real with (T0 := T).
      spec_assert M'_real as (M_finalConf&M_k&M_halts&M_finalContained&tam) by apply makeSingleTape_correct.
      destruct M_finalConf as (M_finalState&M_finalTapes). cbn in M'_finalContains. cbn in tam.

      destruct M'_finalContains as (T_Univ_final&?). destruct H. destruct H0. destruct H1. destruct H2. cbn in H, H0, H1, H2.
      eexists. eexists. eexists. eexists. eexists. split; [ | split; [ | split ]].
      - eauto.
      - unfold initc. cbn. setoid_rewrite M'_halt. f_equal. f_equal.
        apply (proj1 (@contains_tapes_iff _ _ _ _)) in M_finalContained. subst. reflexivity.
      - hnf. eexists. hnf. split. eauto. hnf. repeat split.
        + unfold contains_tapes in M_finalContained. subst. unfold containsWorkingTape. unfold containsWorkingTape in H0. cbn. rewrite H0. cbn. auto.
        + eauto.
        + unfold containsState in H2|-*. eauto.
        + eauto.
      - eauto.
    }
  Qed.


  (** Complement lemma to [tape_size_nice] *)
  Lemma tape_sizeOfTape_nice (sig : finType) :
    { c : nat | forall (T : tape sig), sizeOfTape T <=(c) size T }.
  Proof.
    eexists. intros.
    eapply dominatedWith_trans with (y := Encode_tape_size T).
    - unfold Encode_tape_size. destruct T; cbn.
      all: repeat (cbn; simpl_list).
      all: apply dominatedWith_solve; omega.
    - apply dominatedWith_solve. apply Nat.eq_le_incl. symmetry. apply Encode_tape_hasSize.
  Qed.
    

  Lemma makeUnivWorkingTape_sizeOfTape_nice :
    { c | forall (T : tapes sigM n), sizeOfTape (makeUnivWorkingTape (retr_sigSimTape_sigUniv sigM') (makeSingleTape T)) <=(c) sizeOfmTapes T + 1 }.
  Proof.
    eexists. intros. eapply dominatedWith_trans. apply (proj2_sig (@tape_sizeOfTape_nice _)).
    eapply dominatedWith_trans. 
    rewrite makeUnivWorkingTape_size.
    apply (proj2_sig (@tape_size_nice _)).
    domWith_approx.
    eapply dominatedWith_trans. 
    - setoid_rewrite makeSingleTape_sizeOfmTapes.
      domWith_approx. instantiate (1 := sizeOfmTapes T + 1). all: domWith_approx.
    - domWith_approx.
  Qed.


(*  Print UnivSpaceBounds.Univ_size_bound. *)
    

  (** We need to bound the size of the [sigMU] tape *)


  Lemma containsTrans_size_hasSize tp s :
    containsTrans_size (retr_sigSimGraph_sigUniv sigM') tp M' s ->
    Encode_tape_size tp <= s + size (graph_of_TM M') + 4.
  Proof.
    intros (ls&->&Hs). repeat (cbn -[graph_of_TM encode]; simpl_list).
    eenough ((| ls |) + S ((| encode (graph_of_TM M') |) + 1) + 2 <= _) as H. (* magic *)
    { cbn -[graph_of_TM] in H|-*. rewrite map_length. apply H. }
    change (| encode (graph_of_TM M') |) with (size (graph_of_TM M')).
    ring_simplify. now rewrite Hs.
  Qed.

  Lemma containsState_size_hasSize tp s (q : states M') :
    containsState_size (retr_sigSimGraph_sigUniv sigM') tp q s ->
    Encode_tape_size tp <= index q + s + 6.
  Proof.
    intros (ls&->&Hs). repeat (cbn -[graph_of_TM encode]; simpl_list).
    progress eenough ((| ls |) + S ((| encode (halt M' q, index q) |) + 1) + 2 <= _) as H. (* magic *)
    { cbn -[graph_of_TM] in H|-*. rewrite map_length. apply H. }
    change (| encode (halt M' q, index q) |) with (size (halt M' q, index q)).
    rewrite UnivSpaceBounds.Encode_state_hasSize. ring_simplify. rewrite Hs. nia.
  Qed.


  (** The exact size of the [sigMU] tape, given the configuration and the rest sizes of [Univ] *)
  Definition contains_conf_MU_size_exact_size (T : tapes sigM n) (T_univ : tapes (sigUniv sigM') 6) (q : states M') (s_Univ : Vector.t nat 6) :=
    let s0 := s_Univ[@Fin0] in let s1 := s_Univ[@Fin1] in let s2 := s_Univ[@Fin2] in
    let s3 := s_Univ[@Fin3] in let s4 := s_Univ[@Fin4] in let s5 := s_Univ[@Fin5] in
    vector_sum (fun tp : tape (eqType_X (type sigM)) => Encode_tape_size tp + 1) T + s1 + size (graph_of_TM M') + index q + s2 + s3 + s4 + s5 + 33.

  Lemma contains_conf_MU_size_eq :
    forall (tp : tape sigMU) T_univ (q : states M') (T : tapes sigM n) (s_Univ : Vector.t nat 6),
      contains_conf_MU'_size tp T_univ q T s_Univ ->
      sizeOfTape tp <= contains_conf_MU_size_exact_size T T_univ q s_Univ.
  Proof.
    intros tp T_univ q T s_Univ. intros (H_univ&HT0&HT1&HT2&HT3).
    apply (proj1 (@contains_tapes_iff _ _ _ _)) in H_univ as ->.
    (* Destruct and name the tapes and size vector entries *)
    lock s_Univ. destruct_tapes. rename h into t0, h0 into t1, h1 into t2, h2 into t3, h3 into t4, h4 into t5. unlock s_Univ.
    destruct_vector. rename h into s0, h0 into s1, h1 into s2, h2 into s3, h3 into s4, h4 into s5.
    cbn -[sizeOfTape] in HT1,HT2,HT3,HT0|-*.
    apply (proj1 (@containsWorkingTape_iff _ _ _ _ _)) in HT0 as ->.
    setoid_rewrite makeSingleTape_sizeOfTape'. cbn -[makeUnivWorkingTape].
    setoid_rewrite makeUnivWorkingTape_size'.
    setoid_rewrite makeSingleTape_size.
    setoid_rewrite (containsTrans_size_hasSize HT1).
    setoid_rewrite (containsState_size_hasSize HT2).
    pose proof (HT3 Fin1) as HT4. pose proof (HT3 Fin2) as HT5. specialize (HT3 Fin0). cbn in HT3,HT4,HT5.
    rewrite (isRight_size_hasSize HT3).
    rewrite (isRight_size_hasSize HT4).
    rewrite (isRight_size_hasSize HT5).
    ring_simplify.
    unfold contains_conf_MU_size_exact_size.
    cbn [Vector.nth Vector.caseS]. reflexivity.
  Qed.

  Lemma contains_conf_MU_size0_nice :
    { c : nat | forall (tp : tape sigMU) (q : states M') (T : tapes sigM n),
        contains_conf_MU_size tp q T (Vector.const 0 6) ->
        sizeOfTape tp <=(c) sizeOfmTapes T + 1 }.
  Proof.
    eexists. intros tp q T. intros (T_Univ&Univ_contains).
    setoid_rewrite contains_conf_MU_size_eq; eauto.
    unfold contains_conf_MU_size_exact_size.
    domWith_approx.
    - apply dominatedWith_S'''. ring_simplify.
      replace (vector_sum (fun tp0 : tape (eqType_X (type sigM)) => Encode_tape_size tp0 + 1) T + 1) with (size T).
      2:{ apply Encode_tapes_hasSize. }
      rewrite Encode_tapes_hasSize_le_sizeOfmTapes. domWith_approx.
    - instantiate (1 := UnivBounds.Univ_nice.number_of_states M').
      hnf. ring_simplify.
      enough (index q <= UnivBounds.Univ_nice.number_of_states M') by nia.
      apply UnivSpaceBounds.state_index_le.
  Qed.

  (** This is our final constant for space usage *)
  Definition space_constant := proj1_sig contains_conf_MU_size0_nice.

  Lemma space_constant_correct :
    forall (tp : tape sigMU) (q : states M') (T : tapes sigM n),
        contains_conf_MU_size tp q T (Vector.const 0 6) ->
        sizeOfTape tp <= space_constant * (sizeOfmTapes T + 1).
  Proof. intros. exact (proj2_sig contains_conf_MU_size0_nice tp q T H). Qed.


  Lemma contains_conf_MU'_contains_conf_MU'_size tp T_univ q_M T :
    contains_conf_MU'      tp T_univ q_M T ->
    contains_conf_MU'_size tp T_univ q_M T [| |left T_univ[@Fin0]|; |left T_univ[@Fin1]|; |left T_univ[@Fin2]|; |tape_local_l T_univ[@Fin3]|; |tape_local_l T_univ[@Fin4]|; |tape_local_l T_univ[@Fin5]| |].
  Proof.
    intros (H0&H1&H2&H3&H4). repeat split; auto.
    - unfold containsTrans_size, containsTrans in *. simpl_vector. contains_ext.
    - unfold containsState_size, containsState in *. simpl_vector. contains_ext.
    - intros i; specialize (H4 i); destruct_fin i; simpl_vector; isRight_mono.
  Qed.


  (** If [MU] terminates, so does [M]. This follows directly from [MU_Realises]. *)
  Theorem EndTheorem1 :
    forall (T : tapes sigM n) (k_MU : nat) (tp tp' : tape sigMU),
      contains_conf_MU tp (start M') T ->
      terminates (projT1 MU) [|tp|] k_MU [|tp'|] ->
      exists (k_M : nat) (T' : tapes sigM n), terminates M T k_M T'.
  Proof.
    intros T k_MU tp tp'. intros HCont (MU_finalConf&HMU_Term).
    pose proof MU_Realises as MU_Real. hnf in MU_Real. specialize MU_Real with (1 := HMU_Term). cbn in MU_Real.
    destruct HCont as (T_Univ&HCont).
    evar (s_Univ : Vector.t nat 6).
    specialize MU_Real with (T := T) (s_Univ := s_Univ).
    spec_assert MU_Real as (T'&M_finalState&M'_finalState&k_M&M_halts&M_finalCont&M_finalStateCorresponds).
    {
      eexists. apply contains_conf_MU'_contains_conf_MU'_size. apply HCont.
    }
    unfold terminates. eauto.
  Qed.

  Theorem EndTheorem2 :
    forall (T T' : tapes sigM n) (k : nat),
      let tp := initTapes_MU T in
      terminates M T k T' ->
      (* contains_conf_MU tp (start M') T -> *)
      exists (tp' : tape sigMU) (M'_final : states M'),
        terminates (projT1 MU) [|tp|] (Mf (k, sizeOfmTapes T)) [|tp'|] /\
        contains_conf_MU tp' M'_final T' /\
        sizeOfTape tp <= space_constant * (sizeOfmTapes T + 1).
  Proof.
    intros T T' k.
    cbn zeta. set (tp := initTapes_MU T).
    intros (M_finalConf&M_halts).
    (* hnf in HCont. destruct HCont as (T_univ&HCont&HUnivContainsInitState). *)

    pose proof MU_terminatesIn as MU_Term. hnf in MU_Term.
    specialize MU_Term with
        (tin := [|tp|])
        (k := MU_steps (makeUnivTapes (retr_sigSimGraph_sigUniv _) (retr_sigSimTape_sigUniv _) M' (makeSingleTape T)) T k).
    spec_assert MU_Term as (MU_finalConf&MU_halts).
    { hnf. do 4 eexists. split; [ | split ]; eauto. (* don't [split] too much *)
      hnf. split. cbn.
      - apply makeSingleTape_correct.
      - apply makeUnivTapes_correct. }
    destruct MU_finalConf as (MU_finalState&MU_finalTapes). pose proof vector_1_eta MU_finalTapes as (MU_finalTape&->).

    pose proof MU_Realises as MU_Real. hnf in MU_Real.
    specialize MU_Real with (1 := MU_halts). hnf in MU_Real. cbn in MU_Real.
    specialize MU_Real with (T := T).

    specialize MU_Real with (s_Univ := Vector.const 0 6).
    spec_assert MU_Real as (T''&M_finalState&M'_finalState&k'&k_M'&M_halts'&M'_halts&M'_finalStatecontains&M'_finalStateCorrespond).
    { hnf. eexists.
      split.
      - apply makeSingleTape_correct.
      - split; [ | split; [ | split ] ].
        + apply makeUnivWorkingTape_correct.
        + apply makeUnivGraphTape_correct_size.
        + apply makeUnivStartStateTape_correct_size.
        + intros i; destruct_fin i; cbn; apply initRight_isRight_size.
    }
    (* We got another proof that [M] halts. But this is not a problem *)
    pose proof loop_injective M_halts M_halts'. symmetry in H. inv H.

    exists MU_finalTape. exists M'_finalState. split; [ | split].
    - hnf. exists MU_finalState. eapply loop_monotone. eauto.
      rewrite <- Mfp_eq. apply Mf_bounded.
    - eapply contains_conf_MU_size_contains_conf_MU; eauto.
    - eapply space_constant_correct; eauto. apply initTapes_MU_correct_size.
  Qed.


End UnivMultiTimeSpaceTheorem.

(*
Print Assumptions EndTheorem1.
Print Assumptions EndTheorem2.
*)
