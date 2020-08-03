(** * Bounds For M2M *)


From Undecidability Require Import TM.PrettyBounds.PrettyBounds.
From Undecidability Require Import TM.PrettyBounds.BaseCode.

From Undecidability Require Import TM.Single.StepTM.
From Undecidability Require Import TM.Single.EncodeTapes.
From Undecidability Require Import TM.Util.VectorPrelim.



(** Note that we do not need place bound, because the tape is globally specified *)



Local Arguments Encode_list_size {sigX X cX}.



Lemma dominatedWith_match_tape (sig : Type) (c0 c1 c2 c3 z : nat)
      (f0 : nat) (f1 : sig -> list sig -> nat)
      (f2 : sig -> list sig -> nat)
      (f3 : list sig -> sig -> list sig -> nat)
      (tp : tape sig) :
  (tp = niltape _ -> f0 <=(c0) z) ->
  (forall r rs, tp = leftof r rs -> f1 r rs <=(c1) z) ->
  (forall l ls, tp = rightof l ls -> f2 l ls <=(c2) z) ->
  (forall ls m rs, tp = midtape ls m rs -> f3 ls m rs <=(c3) z) ->
  match tp with
  | @niltape _ => f0
  | leftof r rs => f1 r rs
  | rightof l ls => f2 l ls
  | midtape ls m rs => f3 ls m rs
  end <=(max c0 (max c1 (max c2 c3) )) z.
Proof with reflexivity + apply Nat.mul_le_mono; eauto 4 using le_trans, Nat.le_max_r,Nat.le_max_l.
  intros H1 H2 H3 H4. unfold dominatedWith in *.
  destruct tp.
  - rewrite H1...
  - rewrite H2...
  - rewrite H3...
  - rewrite H4...
Qed.

Smpl Add 12
     match goal with
     | [ |- (match _ with @niltape _ => _ | _ => _ end) <=(_) _ ] =>
       let H := fresh in
       (eapply dominatedWith_match_tape; [ intros H | intros ? ? H | intros ? ? H | intros ? ? ? H]); try rewrite !H
     end : domWith_match.


Lemma dominatedWith_match_move (c0 c1 c2 z : nat)
      (f0 f1 f2 : nat) (m : move) :
  (m = Lmove -> f0 <=(c0) z) ->
  (m = Rmove -> f1 <=(c1) z) ->
  (m = Nmove -> f2 <=(c2) z) ->
  match m with
  | Lmove => f0
  | Rmove => f1
  | Nmove => f2
  end <=(max c0 (max c1 c2)) z.
Proof with reflexivity + apply Nat.mul_le_mono; eauto 4 using le_trans, Nat.le_max_r,Nat.le_max_l.
  intros H1 H2 H3. unfold dominatedWith in *.
  destruct m.
  - rewrite H1...
  - rewrite H2...
  - rewrite H3...
Qed.

Smpl Add 12
     match goal with
     | [ |- (match _ with Lmove => _ | _ => _ end) <=(_) _ ] =>
       let H := fresh in
       (eapply dominatedWith_match_move; [ intros H | intros H | intros H]); try rewrite !H
     end : domWith_match.


Local Arguments plus : simpl never. Local Arguments mult : simpl never.


Section ToSingleTape_bounds.

  Implicit Types (sig : finType) (F : finType).
  (*
  Variable n : nat.
  (* Hypothesis (nNeq0 : n <> 0). (* This really makes no sense for [0] tapes. *) *)
  Notation nMax := (finMax' n).
*)
  Local Arguments finMax' : simpl never.

  Notation sigSim := (FinType(EqType(boundary + sigList (sigTape sig)))).

  (* Implicit Types (T : tapes sig n).
  Notation "t ≃ T" := (contains_tapes t T) (at level 70, no associativity).
 *)

  Lemma GoToCurrent_steps'_nice :
    { c | forall sig (tp : tape sig), GoToCurrent_steps' tp <=(c) length (left tp) + 4 }.
  Proof. eexists. intros. unfold GoToCurrent_steps'. domWith_match; cbn in *; domWith_approx. Qed.

  Lemma GoToCurrent_steps_nice :
    { c | forall (sig : finType) (tp : tape sig), GoToCurrent_steps tp <=(c) length (left tp) + 1 }.
  Proof.
    eexists. intros. unfold GoToCurrent_steps.
    apply dominatedWith_add_r. 2: lia.
    eapply dominatedWith_trans.
    - apply (proj2_sig GoToCurrent_steps'_nice).
    - domWith_approx.
  Qed.

  Lemma GoToNext_steps'_nice :
    { c | forall sig (tp : tape sig), GoToNext_steps' tp <=(c) length (right tp) + 1 }.
  Proof. eexists. intros. unfold GoToNext_steps'. domWith_match; cbn in *; domWith_approx. Qed.

  Lemma GoToNext_steps_nice :
    { c | forall sig (tp : tape sig), GoToNext_steps tp <=(c) length (right tp) + 1 }.
  Proof.
    eexists. intros. unfold GoToNext_steps.
    apply dominatedWith_add_r. 2: lia.
    eapply dominatedWith_trans.
    - apply (proj2_sig GoToNext_steps'_nice).
    - domWith_approx.
  Qed.


  Definition tape_size {sig : Type} (tp : tape sig) := 1 + length (left tp) + length (right tp).

  Lemma tape_size_ge1 {sig : Type} (tp : tape sig) :
    1 <= tape_size tp.
  Proof. unfold tape_size. lia. Qed.

  (** [size tp] is the size w.r.t. the linear encoding (adding of extra symbols for left end, etc.) *)
  Definition Encode_tape_hasSize {sig : Type} (tp : tape sig) :
    size tp <= tape_size tp + 2.
  Proof.
    unfold size.
    destruct tp; cbn.
    all: simpl_list.
    all: cbn.
    all: unfold tape_size.
    all: cbn.
    all: simpl_list.
    all: try lia.
    all: cbn.
    all: try lia.
  Qed.

  Lemma ReadCurrentSymbols_Step_steps_cons_nice :
    { c | forall sig (tp : tape sig), ReadCurrentSymbols_Step_steps_cons tp <=(c) tape_size tp }.
  Proof.
    unfold tape_size.
    eexists. unfold ReadCurrentSymbols_Step_steps_cons. intros. domWith_approx.
    - eapply dominatedWith_trans. apply (proj2_sig GoToCurrent_steps_nice). domWith_approx.
    - eapply dominatedWith_trans. apply (proj2_sig GoToNext_steps_nice). domWith_approx.
  Qed.

  Fixpoint greatest_tape {sig : Type} (tps : list (tape sig)) : nat :=
    match tps with
    | nil => 0
    | tp :: tps' => max (tape_size tp) (greatest_tape tps')
    end.

  Fixpoint tape_size_sum {sig : Type} (tps : list (tape sig)) : nat :=
    match tps with
    | nil => 0
    | tp :: tps' => tape_size tp + tape_size_sum tps'
    end.
  
  Lemma ReadCurrentSymbols_Loop_steps_cons_nice :
    { c | forall (sig : finType) (tps2 : list (tape sig)) (tp : tape sig), ReadCurrentSymbols_Loop_steps_cons tps2 tp <=(c) tape_size_sum (tp :: tps2) + 1 }.
  Proof.
    pose_nice ReadCurrentSymbols_Step_steps_cons_nice Hc_step c_step.
    exists (c_step + 1). intros sig tps2. induction tps2 as [ | tp' tps2' IH]; intros.
    - specialize (Hc_step sig tp). cbn. hnf. rewrite Hc_step. hnf. cbn. nia.
    - specialize (Hc_step sig tp). cbn. hnf. rewrite Hc_step. hnf. cbn in *.
      specialize (IH tp'). hnf in IH. rewrite IH. clear. ring_simplify.
      enough (1 <= tape_size tp) by nia. apply tape_size_ge1.
  Qed.

  Lemma ReadCurrentSymbols_steps_nice :
    { c | forall (n : nat) sig (T : tapes sig n), ReadCurrentSymbols_steps T <=(c) tape_size_sum (vector_to_list T) + 1 }.
  Proof.
    eexists. intros. unfold ReadCurrentSymbols_steps.
    (* This is quite a hack! *)
    match goal with [ |- ?x <=(?c) ?y ] => enough (match n with 0 => x | S n' => x end <=(c) y) by (destruct n; auto) end.
    domWith_match; subst.
    - rewrite (destruct_vector_nil T). domWith_approx.
    - pose proof (destruct_vector_cons T) as (tp&T'&->). cbn. domWith_approx.
      eapply dominatedWith_trans.
      + apply (proj2_sig ReadCurrentSymbols_Loop_steps_cons_nice).
      + cbn. domWith_approx.
  Qed.


  Lemma Encode_tapes_hasSize {sig : Type} (tps : list (tape sig)) :
    size tps <= length tps * (3 + greatest_tape tps) + 1.
  Proof.
    rewrite Encode_list_hasSize.
    induction tps as [ | tp tps' IH]; cbn.
    - cbv. lia.
    - rewrite IH. rewrite Encode_tape_hasSize. nia.
  Qed.

  Lemma Encode_tapes_size_fold {sig : Type} (tps : list (tape sig)) :
    length (encode_list _ tps) = size tps.
  Proof. reflexivity. Qed.

  Lemma size_tapes_ge1 {sig : Type} (tps : list (tape sig)) :
    1 <= size tps.
  Proof. rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1. Qed.

  Lemma MoveToStart_steps_nice :
    { c | forall sig (tps : list (tape sig)), MoveToStart_steps tps <=(c) size tps }.
  Proof.
    eexists. intros. unfold MoveToStart_steps. rewrite Encode_tapes_size_fold. domWith_approx. apply dominatedWith_const. 
    enough (1 <= size tps) by nia. setoid_rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1.
  Qed.

  Lemma DoWrite_steps_nice' :
    { c | forall {sig : finType} (d : option move) (tps1 tps2 : list (tape sig)),
        DoWrite_steps d tps1 tps2
        <=(c)
           match d with
           | Some Lmove => size tps1
           | Some Rmove => size tps2
           | Some Nmove => 1
           | None => size tps1 + size tps2
           end }.
  Proof.
    eexists. intros. unfold DoWrite_steps.
    domWith_match; subst.
    domWith_match; subst.
    3: now domWith_approx.
    all: ring_simplify.
    all: rewrite Encode_tapes_size_fold.
    all: apply dominatedWith_add_r; [ | try now apply size_tapes_ge1].
    4:{ rewrite <- size_tapes_ge1. lia. }
    all: domWith_approx.
    1:{ rewrite Encode_tapes_size_fold. apply dominatedWith_solve. lia. }
  Qed.

  Lemma DoWrite_steps_nice :
    { c | forall sig (d : option move) (tps1 tps2 : list (tape sig)), DoWrite_steps d tps1 tps2 <=(c) size tps1 + size tps2 }.
  Proof.
    eexists. intros. eapply dominatedWith_trans. apply (proj2_sig DoWrite_steps_nice').
    destruct d as [ [ | | ] | ]; cbn; domWith_approx. hnf. ring_simplify. rewrite <- size_tapes_ge1. lia.
  Qed.
  
  Lemma DoAction_steps_nice' :
    { c | forall sig (d : option move) (a : option sig * move) (tps1 tps2 : list (tape sig)),
          DoAction_steps d a tps1 tps2
          <=(c)
             match (fst a) with
             | Some _ => size tps1 + size tps2
             | None => 1
             end }.
  Proof.
    eexists. intros sig d [w m] tps1 tps2. unfold DoAction_steps. cbn. domWith_match; subst.
    - ring_simplify. apply dominatedWith_add_r. domWith_approx.
      + eapply dominatedWith_trans. apply (proj2_sig DoWrite_steps_nice). domWith_approx.
      + apply dominatedWith_const. rewrite <- size_tapes_ge1. lia.
      + rewrite <- size_tapes_ge1. lia.
    - now apply dominatedWith_const.
  Qed.

  Lemma DoAction_steps_nice :
    { c | forall sig (d : option move) (a : option sig * move) (tps1 tps2 : list (tape sig)), DoAction_steps d a tps1 tps2 <=(c) size tps1 + size tps2 }.
  Proof.
    eexists. intros sig d [w m] tps1 tps2. eapply dominatedWith_trans. apply (proj2_sig DoAction_steps_nice'). cbn. domWith_match; subst.
    - domWith_approx.
    - apply dominatedWith_solve. rewrite <- size_tapes_ge1. lia.
  Qed.


  (* Semantical lemma *)
  Lemma tape_doAct_right_length {sig : Type} (tp : tape sig) (act : option sig * move) :
    length (right (doAct tp act)) <= 1 + length (right tp).
  Proof. destruct tp, act as [ [ | ] [ | | ] ]; cbn; simpl_tape; simpl_list; cbn; lia. Qed.

  Lemma size_tape_bounded : forall {sig : Type} (tp : tape sig), tape_size tp <= size tp.
  Proof.
    unfold tape_size, size.
    destruct tp.
    all: cbn.
    all: simpl_list; cbn; simpl_list; cbn.
    all: lia.
  Qed.

  Lemma doAct_size : forall {sig : Type} (tp : tape sig) act, size (doAct tp act) <= size tp + 2.
  Proof.
    intros. unfold size. cbn. unfold encode_tape.
    destruct tp, act as [ [ w | ] [ | | ] ]; cbn.
    all: simpl_list; cbn.
    all: try lia.
    - destruct l; cbn; repeat (simpl_list; cbn); lia.
    - destruct l0; cbn; repeat (simpl_list; cbn); lia.
    - destruct l; cbn; repeat (simpl_list; cbn); lia.
    - destruct l0; cbn; repeat (simpl_list; cbn); lia.
  Qed.
    
  Lemma doAct_size' : forall {sig : Type} (tps1 : list (tape sig)) tp tps2 act, (size (tps1 ++ doAct tp act :: tps2) <= size (tps1 ++ tp :: tps2) + 2).
  Proof.
    intros. rewrite !Encode_list_hasSize. rewrite !Encode_list_hasSize_app. cbn.
    enough (size (doAct tp act) <= size tp + 2) by nia.
    apply doAct_size.
  Qed.
  
  Lemma doAct_size'' : forall {sig : Type} (tp : tape sig) act, size tp <= size (doAct tp act).
  Proof.
    intros. unfold size. cbn. unfold encode_tape.
    destruct tp, act as [ [ w | ] [ | | ] ]; cbn.
    all: simpl_list; cbn.
    all: try lia.
    - destruct l; cbn; repeat (simpl_list; cbn); lia.
    - destruct l0; cbn; repeat (simpl_list; cbn); lia.
    - destruct l; cbn; repeat (simpl_list; cbn); lia.
    - destruct l0; cbn; repeat (simpl_list; cbn); lia.
  Qed.
    
  Lemma DoActions_Step_steps_cons_nice'' :
    { c | forall sig (n : nat) (acts : Vector.t (option sig * move) n) (i : Fin.t n) (tps1 tps2 : list (tape sig)) (tp : tape sig),
        DoActions_Step_steps_cons acts i tps1 tps2 tp <=(c) tape_size tp + size tps1 + size tps2 }.
  Proof.
    unfold tape_size.
    eexists. intros. unfold DoActions_Step_steps_cons. ring_simplify. apply dominatedWith_add_r. domWith_approx.
    - eapply dominatedWith_trans. apply (proj2_sig GoToCurrent_steps_nice). domWith_approx.
    - eapply dominatedWith_trans. apply (proj2_sig DoAction_steps_nice). domWith_approx.
    - eapply dominatedWith_trans. apply (proj2_sig GoToNext_steps_nice). domWith_approx.
      apply dominatedWith_solve. rewrite tape_doAct_right_length. lia.
    - rewrite <- size_tapes_ge1. lia.
  Qed.

  (** Replace [tape_size] with [size],  *)
  Lemma DoActions_Step_steps_cons_nice' :
    { c | forall sig (n : nat) (acts : Vector.t (option sig * move) n) (i : Fin.t n) (tps1 tps2 : list (tape sig)) (tp : tape sig),
        DoActions_Step_steps_cons acts i tps1 tps2 tp <=(c) size tp + size tps1 + size tps2 }.
  Proof.
    eexists. intros. eapply dominatedWith_trans. apply (proj2_sig DoActions_Step_steps_cons_nice''). domWith_approx.
    eapply dominatedWith_trans.
    - apply dominatedWith_solve. apply size_tape_bounded.
    - domWith_approx.
  Qed.

  (** ... and summarize the sizes in a list *)
  Lemma DoActions_Step_steps_cons_nice :
    { c | forall sig (n : nat) (acts : Vector.t (option sig * move) n) (i : Fin.t n) (tps1 tps2 : list (tape sig)) (tp : tape sig),
        DoActions_Step_steps_cons acts i tps1 tps2 tp <=(c) size (tps1 ++ tp :: tps2) }.
  Proof.
    eexists. intros. eapply dominatedWith_trans. apply (proj2_sig DoActions_Step_steps_cons_nice').
    apply dominatedWith_solve.
    rewrite !Encode_list_hasSize. rewrite !Encode_list_hasSize_app. cbn. lia.
  Qed.

  (* Optimize Heap. *)

  Lemma size_doActions {sig : Type} (n : nat) (acts : Vector.t (option sig * move) n) (tps : list (tape sig)) :
    size (map_vect_list (@doAct sig) acts tps) <= size tps + 2 * n.
  Proof.
    rewrite !Encode_list_hasSize.
    revert tps. induction acts as [ | act n acts IH]; intros.
    - destruct tps; cbn; lia.
    - destruct tps as [ | tp tps]; cbn in *; try lia.
      rewrite IH. rewrite doAct_size. lia.
  Qed.

  Lemma size_doActions' {sig : Type} (n : nat) (acts : Vector.t (option sig * move) n) (tps : list (tape sig)) :
    size tps <= size (map_vect_list (@doAct sig) acts tps).
  Proof.
    rewrite !Encode_list_hasSize.
    revert tps. induction acts as [ | act n acts IH]; intros.
    - destruct tps; cbn; lia.
    - destruct tps as [ | tp tps]; cbn in *; try lia.
      rewrite IH. rewrite <- doAct_size''. lia.
  Qed.


  (** First optimsation step for [DoActions_Loop_steps_cons]: structurally same function, but with terms replaced by bounded terms. *)
  Fixpoint DoActions_Loop_steps_cons_asym {sig : Type} (n : nat) (acts : Vector.t (option sig * move) n) (i : Fin.t n) (tps1 tps2 : list (tape sig)) (tp : tape sig) :=
    match tps2 with
    | nil => size (tps1 ++ tp :: tps2)
    | tp' :: tps2' =>
      match finSucc_opt i with
      | Some i' => size (tps1 ++ tp :: tps2) + DoActions_Loop_steps_cons_asym acts i' (tps1 ++ [doAct tp acts[@i]]) tps2' tp'
      | None => 0
      end
    end.

  (** Then bound every term with [size (tps1 ++ tp :: tps2)] *)
  Fixpoint DoActions_Loop_steps_cons_asym2 {sig : Type} (n : nat) (acts : Vector.t (option sig * move) n) (i : Fin.t n) (tps1 tps2 : list (tape sig)) (tp : tape sig) :=
    match tps2 with
    | nil => size (map_vect_list (@doAct sig) acts (tps1 ++ tp :: tps2))
    | tp' :: tps2' =>
      match finSucc_opt i with
      | Some i' => size (map_vect_list (@doAct sig) acts (tps1 ++ tp :: tps2)) + DoActions_Loop_steps_cons_asym2 acts i' (tps1 ++ [tp]) tps2' tp'
      | None => 0
      end
    end.


  Lemma DoActions_Loop_steps_cons_nice'' :
    { c | forall sig (n : nat) (acts : Vector.t (option sig * move) n) (i : Fin.t n) (tps1 tps2 : list (tape sig)) (tp : tape sig),
        DoActions_Loop_steps_cons acts i tps1 tps2 tp <=(c) DoActions_Loop_steps_cons_asym acts i tps1 tps2 tp }.
  Proof.
    pose_nice DoActions_Step_steps_cons_nice Hc_step c_step. exists (c_step + 1).
    intros. revert n acts i tps1 tp. induction tps2 as [ | tp' tps2 IH]; intros; cbn in *.
    - hnf. rewrite Hc_step. nia.
    - destruct finSucc_opt as [ i' | ]; [ | hnf; lia].
      specialize (IH n acts i' (tps1 ++ [doAct tp acts[@i]]) tp'). hnf in IH. rewrite IH. clear IH.
      hnf. rewrite Hc_step. ring_simplify.
      enough (1 <= size (tps1 ++ tp :: tp' :: tps2)) by nia. apply size_tapes_ge1.
  Qed.

  Instance sub_le_mono : Proper (le ==> ge ==> le) minus.
  Proof. repeat intro. nia. Qed.

  Lemma le_ge (n m : nat) : n <= m -> m >= n. Proof. nia. Qed.

  Lemma size_tape_ge1 {sig : Type} (tp : tape sig) :
    1 <= size tp.
  Proof. unfold size. destruct tp; cbn; lia. Qed.



  Fixpoint vector_drop (X : Type) (n : nat) (vs : Vector.t X n) (k : nat) {struct k} : Vector.t X (n-k).
  Proof.
    refine (match k with
            | 0 => Vector.cast vs _
            | S k' => match vs with
                     | [||] => Vector.cast [||] _
                     | _ ::: vs' => Vector.cast (vector_drop _ _ vs' k') _
                     end
            end); abstract lia.
  Defined.

  (* Generalisation of the lemma [map_vect_list_app] *)
  Lemma map_vect_list_app_drop (X Y : Type) (f : X -> Y -> X) (n : nat) (vs : Vector.t Y n) (xs ys : list X)
        (i : Fin.t n) :
    fin_to_nat i = length xs ->
    map_vect_list f vs (xs ++ ys) =
    map_vect_list f vs xs ++ map_vect_list f (vector_drop vs (length xs)) ys.
  Proof.
    revert n vs i. induction xs as [ | x xs' IH]; cbn; intros.
    - destruct vs. destruct_fin i. apply fin_is_0 in H as ->. cbn.
      f_equal. f_equal. now rewrite vector_cast_refl.
    - destruct vs as [ | v n vs]; cbn in *.
      + destruct_fin i.
      + f_equal.
        pose proof fin_destruct_S i as [ (i'&->) | -> ]; cbn in *.
        * rewrite fin_to_nat_S in *. erewrite IH; eauto.
          f_equal. f_equal. now rewrite vector_cast_refl.
        * lia.
  Qed.


  (** The easy part *)
  Lemma DoActions_Loop_steps_cons_asym2_bounded sig (n : nat) (acts : Vector.t (option sig * move) n) (i : Fin.t n) (tps1 tps2 : list (tape sig)) (tp : tape sig) :
    DoActions_Loop_steps_cons_asym2 acts i tps1 tps2 tp <= size (map_vect_list (@doAct sig) acts (tps1 ++ tp :: tps2)) * (1 + length tps2).
  Proof.
    revert tps1 tp n acts i. induction tps2 as [ | tp' tps2' IH]; intros; cbn in *.
    - nia.
    - destruct finSucc_opt as [ i' | ] eqn:E; [ | nia].
      rewrite IH. clear IH. simpl_list. cbn. nia.
  Qed.


  (** The harder part *)
  Lemma DoActions_Loop_steps_cons_asym_bounded'' sig (n : nat) (acts : Vector.t (option sig * move) n) (i : Fin.t n) (tps1 tps2 : list (tape sig)) (tp : tape sig) :
    length tps1 = fin_to_nat i ->
    length tps1 + (1 + length tps2) = n ->
    DoActions_Loop_steps_cons_asym acts i (map_vect_list (@doAct sig) acts tps1) tps2 tp <=
    DoActions_Loop_steps_cons_asym2 acts i tps1 tps2 tp.
  Proof.
    revert tps1 tp n acts i. induction tps2 as [ | tp' tps2' IH]; intros; cbn in *.
    - erewrite map_vect_list_app; eauto.
      rewrite !Encode_list_hasSize, !Encode_list_hasSize_app; cbn.
      enough (size tp <= size (doAct tp acts[@i])) by nia.
      apply doAct_size''.
    - destruct finSucc_opt as [ i' | ] eqn:E; [ | nia].
      erewrite map_vect_list_app_drop; eauto.
      rewrite !encodeList_size_app_eq.
      rewrite <- map_vect_list_app; eauto.
      erewrite IH. clear IH.
      2-3: apply finSucc_opt_Some' in E; simpl_list; cbn; lia.
      enough (size (tp :: tp' :: tps2') <= size (map_vect_list (doAct (sig:=eqType_X (type sig))) (vector_drop acts (| tps1 |)) (tp :: tp' :: tps2'))) by nia.
      apply size_doActions'.
  Qed.

  
  (** Remove the uggly [map_vect_list] from the above bound *)
  Lemma DoActions_Loop_steps_cons_asym_monotone sig (n : nat) (acts : Vector.t (option sig * move) n) (i : Fin.t n) (tps1a tps1b tps2 : list (tape sig)) (tp : tape sig) :
    size tps1a <= size tps1b ->
    DoActions_Loop_steps_cons_asym acts i tps1a tps2 tp <=
    DoActions_Loop_steps_cons_asym acts i tps1b tps2 tp.
  Proof.
    revert tps1a tps1b tp n acts i. induction tps2 as [ | tp' tps2' IH]; intros; cbn in *.
    - rewrite !Encode_list_hasSize, !Encode_list_hasSize_app. cbn. rewrite <- !Encode_list_hasSize. lia.
    - destruct finSucc_opt as [ i' | ] eqn:E; [ | nia].
      specialize (IH (tps1a ++ [doAct tp acts[@i]]) (tps1b ++ [doAct tp acts[@i]]) tp' _ acts i'). spec_assert IH.
      { rewrite !Encode_list_hasSize, !Encode_list_hasSize_app. cbn. rewrite <- !Encode_list_hasSize. lia. }
      rewrite IH.
      enough (size (tps1a ++ tp :: tp' :: tps2') <= size (tps1b ++ tp :: tp' :: tps2')) by nia.
      { rewrite !Encode_list_hasSize, !Encode_list_hasSize_app. cbn. rewrite <- !Encode_list_hasSize. lia. }
  Qed.

  Lemma DoActions_Loop_steps_cons_asym_bounded' sig (n : nat) (acts : Vector.t (option sig * move) n) (i : Fin.t n) (tps1 tps2 : list (tape sig)) (tp : tape sig) :
    length tps1 = fin_to_nat i ->
    length tps1 + (1 + length tps2) = n ->
    DoActions_Loop_steps_cons_asym acts i tps1 tps2 tp <=
    DoActions_Loop_steps_cons_asym2 acts i tps1 tps2 tp.
  Proof.
    intros. erewrite DoActions_Loop_steps_cons_asym_monotone.
    - now apply DoActions_Loop_steps_cons_asym_bounded''.
    - apply size_doActions'.
  Qed.

  
  (** Combine both bounds! *)
  Lemma DoActions_Loop_steps_cons_asym_bounded sig (n : nat) (acts : Vector.t (option sig * move) n) (i : Fin.t n) (tps1 tps2 : list (tape sig)) (tp : tape sig) :
    length tps1 = fin_to_nat i ->
    length tps1 + (1 + length tps2) = n ->
    DoActions_Loop_steps_cons_asym acts i tps1 tps2 tp <= size (map_vect_list (@doAct sig) acts (tps1 ++ tp :: tps2)) * (1 + length tps2).
  Proof.
    intros. etransitivity.
    - now apply DoActions_Loop_steps_cons_asym_bounded'.
    - apply DoActions_Loop_steps_cons_asym2_bounded.
  Qed.

    

  (** Finally, a better bound for [DoActions_Loop_steps_cons] *)
  Lemma DoActions_Loop_steps_cons_nice :
    { c | forall sig (n : nat) (acts : Vector.t (option sig * move) n) (i : Fin.t n) (tps1 tps2 : list (tape sig)) (tp : tape sig),
        length tps1 = fin_to_nat i ->
        length tps1 + (1 + length tps2) = n ->
        DoActions_Loop_steps_cons acts i tps1 tps2 tp <=(c) size (map_vect_list (@doAct sig) acts (tps1 ++ tp :: tps2)) * (1 + length tps2) }.
  Proof.
    eexists. intros. eapply dominatedWith_trans.
    - apply (proj2_sig DoActions_Loop_steps_cons_nice'').
    - apply dominatedWith_solve. now apply DoActions_Loop_steps_cons_asym_bounded.
  Qed.

        

  Lemma DoActions_steps_nice :
    { c | forall sig (n : nat) (acts : Vector.t (option sig * move) n) (tps : list (tape sig)),
        length tps = n ->
        DoActions_steps acts tps <=(c) size (map_vect_list (@doAct sig) acts tps) * (length tps) + 1 }.
  Proof.
    eexists. intros sig n acts tps Hlen. unfold DoActions_steps. repeat domWith_match; subst. 1,3: domWith_approx.
    ring_simplify. apply dominatedWith_add_r.
    2: { rewrite <- size_tapes_ge1. cbn. lia. }
    rename x0 into tp, xs into tps.
    eapply dominatedWith_trans. apply (proj2_sig DoActions_Loop_steps_cons_nice).
    - cbn. now apply finMin_opt_Some_val in H.
    - cbn. nia.
    - apply dominatedWith_solve. cbn [app length]. nia.
  Qed.

  Lemma Encode_list_hasSize_ge_length (sigX X : Type) (cX : codable sigX X) (xs : list X) :
    length xs <= Encode_list_size xs.
  Proof. induction xs as [ | x xs IH]; cbn in *; lia. Qed.
  
  Lemma tape_size_sum_le_size {sig : Type} (tps : list (tape sig)) :
    tape_size_sum tps <= size tps.
  Proof.
    rewrite Encode_list_hasSize.
    induction tps as [ | tp tps IH]; cbn in *.
    - lia.
    - rewrite IH. rewrite size_tape_bounded. lia.
  Qed.

  
  Lemma Step_steps_nice' :
    { c | forall sig (F : finType) (n : nat) (pM : pTM sig F n) (q : state (projT1 pM)) (T : tapes sig n),
        let (q', act) := trans (m := projT1 pM) (q, current_chars T) in
        Step_steps q T <=(c) size (vector_to_list (doAct_multi T act)) * size (vector_to_list (doAct_multi T act)) }.
  Proof.
    eexists. intros. unfold Step_steps. destruct trans as (q', act) eqn:E. ring_simplify. apply dominatedWith_add_r. domWith_approx.
    - eapply dominatedWith_trans. apply (proj2_sig ReadCurrentSymbols_steps_nice).
      apply dominatedWith_add_r.
      + apply dominatedWith_solve.
        enough (tape_size_sum (vector_to_list T) <= size (vector_to_list (doAct_multi T act))) by nia.
        unfold doAct_multi. rewrite <- map_vect_list_eq. rewrite <- size_doActions'. apply tape_size_sum_le_size.
      + enough (1 <= size (vector_to_list (doAct_multi T act))) by nia. apply size_tapes_ge1.
    - eapply dominatedWith_trans. apply (proj2_sig MoveToStart_steps_nice).
      apply dominatedWith_solve.
      enough (size (vector_to_list T) <= size (vector_to_list (doAct_multi T act))) by nia.
      unfold doAct_multi. rewrite <- map_vect_list_eq. apply size_doActions'.
    - eapply dominatedWith_trans. apply (proj2_sig DoActions_steps_nice).
      + apply vector_to_list_length.
      + apply dominatedWith_add_r. 2: now rewrite <- size_tapes_ge1.
        apply dominatedWith_solve. unfold doAct_multi. rewrite <- map_vect_list_eq.
        enough ((| vector_to_list T |) <= size (map_vect_list (doAct (sig:=eqType_X (type sig))) act (vector_to_list T))) by nia.
        rewrite vector_to_list_length.
        rewrite Encode_list_hasSize. rewrite <- Encode_list_hasSize_ge_length. now rewrite map_vect_list_length, vector_to_list_length.
    - eapply dominatedWith_trans. apply (proj2_sig MoveToStart_steps_nice). apply dominatedWith_solve. nia.
    - enough (1 <= size (vector_to_list (doAct_multi T act))) by nia. apply size_tapes_ge1.
  Qed.


  Lemma Step_steps_nice :
    { c | forall sig F (n : nat) (pM : pTM sig F n) (q : state (projT1 pM)) (T : tapes sig n),
        Step_steps q T <=(c) size (vector_to_list T) * size (vector_to_list T) }.
  Proof.
    eexists. intros.
    pose proof (proj2_sig Step_steps_nice' _ _ _ _ q T). destruct trans as [q' act] eqn:Etrans.
    eapply dominatedWith_trans. apply H.
    eapply dominatedWith_trans.
    - apply dominatedWith_solve. unfold doAct_multi. rewrite <- map_vect_list_eq. rewrite !size_doActions. reflexivity.
    - ring_simplify. domWith_approx.
      + rewrite (Nat.mul_comm 4), <- Nat.mul_comm, !Nat.mul_assoc. apply dominatedWith_mult_r.
        apply dominatedWith_solve. enough (n <= size (vector_to_list T)) by nia. now rewrite Encode_list_hasSize, <- Encode_list_hasSize_ge_length, vector_to_list_length.
      + rewrite (Nat.mul_comm 4), <- Nat.mul_comm, !Nat.mul_assoc. apply dominatedWith_mult_r.
        apply dominatedWith_solve. enough (n <= size (vector_to_list T)) by nia. now rewrite Encode_list_hasSize, <- Encode_list_hasSize_ge_length, vector_to_list_length.
  Qed.


  (** Same structure as [Loop_steps], but with bounded terms *)
  Fixpoint Loop_steps_asym {n : nat} sig {M : TM sig n} q (T : tapes sig n) (k : nat) {struct k} :=
    if halt q
    then 0
    else match k with
         | 0 => 0 (* can't happen *)
         | S k' =>
           let (q', acts) := trans (m := M) (q, current_chars T) in
           size (vector_to_list T) * size (vector_to_list T) + Loop_steps_asym q' (doAct_multi T acts) k'
         end.

  Lemma Loop_steps_asym_halt {n : nat} sig {M : TM sig n} (q : state M) (T : tapes sig n) (k : nat) :
    halt q = true ->
    Loop_steps_asym q T k = 0.
  Proof. now destruct k; cbn; intros ->. Qed.

  Lemma Loop_steps_asym_nice :
    { c | forall sig F (n : nat) (pM : pTM sig F n) (q : state (projT1 pM)) (T : tapes sig n) (k : nat),
          Loop_steps q T k <=(c) Loop_steps_asym q T k }.
  Proof.
    pose_nice Step_steps_nice Hc_step c_step. exists (c_step + 1).
    intros sig F n pM q T k. revert q T. induction k as [ | k' IH]; intros; cbn in *.
    - destruct halt; hnf; nia.
    - destruct halt eqn:Ehalt; [hnf; nia| ].
      destruct trans as [q' acts] eqn:Etrans.
      specialize IH with (q := q') (T := doAct_multi T acts); hnf in IH.
      rewrite Hc_step, IH. hnf. ring_simplify.
      enough (1 <= size (vector_to_list T) * size (vector_to_list T)) by nia.
      now rewrite <- size_tapes_ge1.
  Qed.

  
  Lemma size_doAct_multi {sig : Type} (n : nat) (T : tapes sig n) (act : Vector.t (option sig * move) n) :
    size (vector_to_list T) <= size (vector_to_list (doAct_multi T act)).
  Proof. unfold doAct_multi. rewrite <- map_vect_list_eq. apply size_doActions'. Qed.

  Lemma size_doAct_multi' {sig : Type} (n : nat) (T : tapes sig n) (act : Vector.t (option sig * move) n) :
    size (vector_to_list (doAct_multi T act)) <= size (vector_to_list T) + 2 * n.
  Proof. unfold doAct_multi. rewrite <- map_vect_list_eq. apply size_doActions. Qed.

  Lemma size_final_tapes {sig : finType} {n : nat} {M : TM sig n} (q : state M) (T : tapes sig n) (k : nat) (q_fin : state M) (T_fin : tapes sig n) :
    loopM (mk_mconfig q T) k = Some (mk_mconfig q_fin T_fin) ->
    size (vector_to_list T) <= size (vector_to_list T_fin).
  Proof.
    intros HLoop. revert q T q_fin T_fin HLoop. induction k as [ | k' IH]; intros; cbn in *.
    - unfold haltConf in HLoop. cbn in *. destruct (halt q); now inv HLoop.
    - unfold haltConf in HLoop. cbn in *. destruct (halt q).
      + inv HLoop. reflexivity.
      + destruct (trans (m := M) (q, current_chars T)) eqn:Etrans.
        unfold step in HLoop. cbn -[doAct_multi] in *. rewrite Etrans in HLoop.
        specialize IH with (1 := HLoop).
        rewrite <- IH. apply size_doAct_multi.
  Qed.        

  Lemma size_final_tapes' {sig : finType} {n : nat} {M : TM sig n} (q : state M) (T : tapes sig n) (k : nat) (q_fin : state M) (T_fin : tapes sig n) :
    loopM (mk_mconfig q T) k = Some (mk_mconfig q_fin T_fin) ->
    size (vector_to_list T_fin) <= size (vector_to_list T) + 2 * n * k.
  Proof.
    intros HLoop. revert q T q_fin T_fin HLoop. induction k as [ | k' IH]; intros; cbn in *.
    - unfold haltConf in HLoop. cbn in *. destruct (halt q); inv HLoop. nia.
    - unfold haltConf in HLoop. cbn in *. destruct (halt q).
      + inv HLoop. nia.
      + destruct (trans (m := M) (q, current_chars T)) eqn:Etrans.
        unfold step in HLoop. cbn -[doAct_multi] in *. rewrite Etrans in HLoop.
        specialize IH with (1 := HLoop).
        rewrite IH. rewrite size_doAct_multi'. ring_simplify. nia.
  Qed.        
  

  (** Bound every step term with the term for the tape after the execution *)
  Lemma Loop_steps_asym_bounded sig {n : nat} {M : TM sig n} (q : state M) (T : tapes sig n) (k : nat) (q_fin : state M) (T_fin : tapes sig n) :
    loopM (mk_mconfig q T) k = Some (mk_mconfig q_fin T_fin) ->
    Loop_steps_asym q T k <= size (vector_to_list T_fin) * size (vector_to_list T_fin) * k.
  Proof.
    intros HLoop. revert q T q_fin T_fin HLoop. induction k as [ | k' IH]; intros; cbn in *.
    - destruct halt; nia.
    - unfold haltConf in HLoop. cbn in *.
      destruct halt eqn:Eh; [nia| ].
      destruct trans as [q' acts] eqn:Etrans.
      specialize IH with (q := q') (T := doAct_multi T acts) (q_fin := q_fin) (T_fin := T_fin). rewrite IH. clear IH.
      2:{ rewrite <- HLoop. unfold step. cbn. now rewrite Etrans. }
      ring_simplify.
      enough (size (vector_to_list T) <= size (vector_to_list T_fin)) by nia.
      eapply size_final_tapes with (k := (S k')). setoid_rewrite loop_step; eauto. all: now rewrite <- HLoop. (* we need this for Coq<8.9 *)
  Qed.

  (** Bound for the loop w.r.t. the final tapes *)
  Lemma Loop_steps_nice_final :
    { c | forall sig F (n : nat) (pM : pTM sig F n) (q : state (projT1 pM)) (T : tapes sig n) (k : nat),
        forall (q_fin : state (projT1 pM)) (T_fin : tapes sig n),
          loopM (mk_mconfig q T) k = Some (mk_mconfig q_fin T_fin) ->
          Loop_steps q T k <=(c) size (vector_to_list T_fin) * size (vector_to_list T_fin) * k }.
  Proof.
    eexists. intros. eapply dominatedWith_trans. apply (proj2_sig Loop_steps_asym_nice).
    apply dominatedWith_solve. eapply Loop_steps_asym_bounded; eauto.
  Qed.


  (** Bound for the final tape size after k steps *)
  Lemma Loop_steps_asym_bounded' sig {n : nat} {M : TM sig n} (q : state M) (T : tapes sig n) (k : nat) (* (q_fin : state M) (T_fin : tapes sig n) *) :
    (* loopM (mk_mconfig q T) k = Some (mk_mconfig q_fin T_fin) -> *)
    Loop_steps_asym q T k <= (size (vector_to_list T) + 2 * n * k) * (size (vector_to_list T) + 2 * n * k) * k.
  Proof.
    revert q T. induction k as [ | k' IH]; intros; cbn in *.
    - destruct halt; nia.
    - destruct halt eqn:Eh. cbn. lia.
      destruct trans as (q', acts) eqn:Etrans.
      rewrite IH. rewrite size_doAct_multi'. lia.
  Qed.

  Lemma Loop_steps_nice :
    { c | forall sig F (n : nat) (pM : pTM sig F n) (q : state (projT1 pM)) (T : tapes sig n) (k : nat),
          Loop_steps q T k <=(c) (size (vector_to_list T) + n * k) * (size (vector_to_list T) + n * k) * k }.
  Proof.
    eexists. intros. eapply dominatedWith_trans. apply (proj2_sig Loop_steps_asym_nice).
    eapply dominatedWith_trans.
    - apply dominatedWith_solve. eapply Loop_steps_asym_bounded'; eauto.
    - ring_simplify. domWith_approx.
      + rewrite <- !Nat.mul_assoc. domWith_approx.
      + rewrite <- !Nat.mul_assoc. domWith_approx.
  Qed.

End ToSingleTape_bounds.


(* Print Assumptions Loop_steps_nice. *)
