From Undecidability Require Import TM.Code.ProgrammingTools.
Require Import PslBase.Bijection. (* [injective] *)


From Undecidability Require Import Basic.Duo.
From Undecidability Require Import Code.CaseFin Code.CaseList Code.CasePair.
From Undecidability Require Import Univ.LookupAssociativeListTM.


Local Arguments plus : simpl never.
Local Arguments mult : simpl never.


(** * Universal Turing Machine *)


Definition map_pair (X X' Y Y' : Type) (f : X -> X') (g : Y -> Y') : X*Y->X'*Y' :=
  fun '(x,y) => (f x, g y).


Section Graph.

  Variable (A : finType) (B : Type) (f : A -> B).

  Definition graph_of_fun : list (A*B) := map (fun x => (x, f x)) enum.

  Lemma graph_of_fun_functional x y1 y2 :
    In (x, y1) graph_of_fun -> In (x, y2) graph_of_fun -> y1 = y2.
  Proof. unfold graph_of_fun. intros (?&?H1&H2) % in_map_iff (?&H3&H4) % in_map_iff. congruence. Qed.

  Lemma graph_of_fun_In x :
    In (x, f x) graph_of_fun.
  Proof. unfold graph_of_fun. apply in_map_iff. exists x. split. reflexivity. apply count_in_equiv. rewrite enum_ok. omega. Qed.

  Lemma graph_of_fun_In' p :
    In p graph_of_fun ->
    exists x, p = (x, f x).
  Proof.
    destruct p as [a b].
    intros H. assert ((a, f a) el graph_of_fun) by apply graph_of_fun_In.
    pose proof graph_of_fun_functional H H0 as ->. eauto.
  Qed.

  Lemma lookup_In (X : eqType) (Y : Type) (lst : list (X*Y)) x y :
  (x, y) el lst ->
  exists y', lookup x lst = Some y'.
  Proof.
    induction lst as [ | p lst IH]; cbn in *.
    - auto.
    - intros [ -> | Hp].
      + decide (x=x); [ | tauto]. eauto.
      + specialize IH with (1 := Hp) as (y'&IH).
        destruct p as [a b]. cbn. decide (x=a) as [ <- | HDec]; eauto.
  Qed.


  Lemma lookup_In' (X : eqType) (Y : Type) (lst : list (X*Y)) x y :
    lookup x lst = Some y ->
    (x, y) el lst.
  Proof.
    induction lst as [ | [a b] lst IH]; cbn in *.
    - congruence.
    - decide (x=a) as [ <- | HDec].
      + intros H. inv H. eauto.
      + intros H. specialize IH with (1 := H). auto.
  Qed.
  
  Lemma graph_of_fun_lookup x :
    lookup x graph_of_fun = Some (f x).
  Proof.
    pose proof graph_of_fun_In x as H.
    apply lookup_In in H as (y'&H).
    enough (y' = f x) by congruence.
    apply lookup_In' in H. eapply graph_of_fun_functional in H; eauto.
    apply graph_of_fun_In.
  Qed.

End Graph.

(** map keys injectively and values arbitrarily *)
Lemma lookup_map (X X' : eqType) (Y Y' : Type) (lst : list (X*Y)) (f : X -> X') (g : Y -> Y') (x : X) (y : Y) :
  injective f ->
  lookup x lst = Some y ->
  lookup (f x) (map (map_pair f g) lst) = Some (g y).
Proof.
  intros HInj. revert x y. induction lst as [ | p lst IH]; intros x y HEq; cbn in *.
  - congruence.
  - destruct p as [a b]. cbn in *. decide (f x = f a) as [ HDec | HDec].
    + apply HInj in HDec as ->. decide (a=a) as [_|?]; [ | tauto]. congruence.
    + decide (x=a) as [ -> | _]; [congruence | ]. now apply IH.
Qed.


(** States are encoded as numbers *)

Notation sigState := (sigPair bool sigNat).

Lemma transition_graph_injective (sigM : finType) :
  injective
    (Encode_pair (Encode_Finite (finType_CS (option sigM)))
       (Encode_pair Encode_bool Encode_nat)).
Proof.
  apply Encode_pair_injective.
  - apply Encode_Finite_injective.
  - apply Encode_pair_injective.
    + apply Encode_bool_injective.
    + apply Encode_nat_injective.
Qed.


Lemma doAct_map (sig tau : Type) (t : tape sig) (f : sig -> tau) (a : option sig * move) :
  mapTape f (doAct t a) = doAct (mapTape f t) (map_opt f (fst a), snd a).
Proof.
  destruct a as [ [ w | ] [ | | ]]; destruct t; cbn; auto.
  - destruct l; cbn; auto.
  - destruct l0; cbn; auto.
  - destruct l; cbn; auto.
  - destruct l0; cbn; auto.
Qed.
  

Section Univ.

  (** Actually, we build a Universal Turing Machine for each alphabet [sigM] *)
  Variable (sigM : finType).

  Notation sigGraph := (sigList (sigPair (sigPair (option sigM) sigState) (sigPair (option sigM * move) sigState))).

  (** The alphabet of [Univ] *)
  Variable (sig : finType).
  Variable (retr_sigGraph_sig : Retract sigGraph sig).
  Variable (retr_sigTape_sig : Retract sigM sig).

  (** Encoding of the current state number *)
  Local Definition retr_sigCurrentStateNumber_sigGraph : Retract sigNat sigGraph :=
    Retract_sigList_X (Retract_sigPair_X _ (Retract_sigPair_Y _ (Retract_sigPair_Y _ _))).
  Local Definition retr_sigCurrentStateNumber_sig : Retract sigNat sig :=
    ComposeRetract retr_sigGraph_sig retr_sigCurrentStateNumber_sigGraph.

  (** Encoding of the current state (= halt bit + number) *)
  Local Definition retr_sigCurrentState_sigGraph : Retract sigState sigGraph :=
    Retract_sigList_X (Retract_sigPair_X _ (Retract_sigPair_Y _ (Retract_id _))).
  Local Definition retr_sigCurrentState_sig : Retract sigState sig := ComposeRetract retr_sigGraph_sig retr_sigCurrentState_sigGraph.

  (** Encoding of final bit of the current state *)
  Local Definition retr_sigCurrentStateFinal_sigGraph : Retract bool sigGraph :=
    Retract_sigList_X (Retract_sigPair_X _ (Retract_sigPair_Y _ (Retract_sigPair_X _ _))).
  Local Definition retr_sigCurrentStateFinal_sig : Retract bool sig := ComposeRetract retr_sigGraph_sig retr_sigCurrentStateFinal_sigGraph.

  (** Encoding of the next state *)
  Local Definition retr_sigNextState_sigGraph : Retract sigState sigGraph := Retract_sigList_X (Retract_sigPair_Y _ _).
  Local Definition retr_sigNextState_sig : Retract sigState sig := ComposeRetract retr_sigGraph_sig retr_sigNextState_sigGraph.

  (** Encoding the current symbol *)
  Local Definition retr_sigCurrentSymbol_sigGraph : Retract (option sigM) sigGraph := Retract_sigList_X (Retract_sigPair_X _ (Retract_sigPair_X _ _)).
  Local Definition retr_sigCurrentSymbol_sig: Retract (option sigM) sig := ComposeRetract retr_sigGraph_sig retr_sigCurrentSymbol_sigGraph.

  (** Encoding of actions *)
  Local Definition retr_act_sigGraph : Retract (option sigM * move) sigGraph := _.
  Local Definition retr_act_sig : Retract (option sigM * move) sig := ComposeRetract retr_sigGraph_sig retr_act_sigGraph.

  (** Encoding of the keys for [Lookup] ([option sig * Q]) *)
  Local Definition retr_key_sigGraph : Retract _ sigGraph := Retract_sigList_X (Retract_sigPair_X _ (Retract_id _)).
  Local Definition retr_key_sig : Retract _ sig := ComposeRetract retr_sigGraph_sig retr_key_sigGraph.

  (** Encoding of the value for [Lookup] ([option sig * Q]) *)
  Local Definition retr_value_sigGraph : Retract _ sigGraph := Retract_sigList_X (Retract_sigPair_Y _ (Retract_id _)).
  Local Definition retr_value_sig : Retract _ sig := ComposeRetract retr_sigGraph_sig retr_value_sigGraph.

  
  
  (** One tape is the working tape of the simulated machine. *)

  Definition containsWorkingTape (t : tape sig^+) (tp : tape sigM) :=
    t = mapTape (fun s => inr (Retr_f (Retract := retr_sigTape_sig) s)) tp.

  Lemma containsWorkingTape_current t tp :
    containsWorkingTape t tp ->
    current t = map_opt (fun s => inr (Retr_f s)) (current tp).
  Proof. intros ->. cbn. simpl_tape. auto. Qed.

  Lemma containsWorkingTape_doAct (a : option sigM * move) t tp :
    containsWorkingTape t tp ->
    containsWorkingTape (doAct t (map_opt (fun s => inr (Retr_f s)) (fst a), snd a)) (doAct tp a).
  Proof. intros ->. hnf. cbn. now rewrite doAct_map. Qed.

  (** Simply read a symbol from the working tape *)
  Definition ReadCurrent : pTM sig^+ (option sigM) 1 :=
    CaseChar (fun c => match c with
                    | Some (inr c') =>
                      match Retr_g (Retract := retr_sigTape_sig) c' with
                      | Some s => Some s
                      | None => None
                      end
                    | _ => None
                    end).

  Definition ReadCurrent_Rel : pRel sig^+ (option sigM) 1 :=
    fun tin '(yout, tout) => forall tp, containsWorkingTape tin[@Fin0] tp -> containsWorkingTape tout[@Fin0] tp /\ yout = current tp.

  Lemma ReadCurrent_Sem : ReadCurrent ⊨c(1) ReadCurrent_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold ReadCurrent. TM_Correct. }
    { reflexivity. }
    { intros tin (yout, tout) H. intros tp HContTp. TMSimp. split; auto. erewrite containsWorkingTape_current; eauto.
      destruct (current tp); cbn; auto. now retract_adjoint. }
  Qed.

  (** Read the current symbol and write it to another tape *)
  Definition ReadCurrent' : pTM sig^+ unit 2 :=
    Switch (ReadCurrent @ [|Fin0|])
           (fun c => WriteValue [Retr_f (Retract := retr_sigCurrentSymbol_sig) c] @ [|Fin1|]).

  Definition ReadCurrent_size := pred >> pred.


  Local Instance Encode_optSigM : codable (option sigM) (option sigM) := Encode_Finite _.
  

  Definition ReadCurrent'_Rel : pRel sig^+ unit 2 :=
    ignoreParam(
        fun tin tout =>
          forall (tp : tape sigM) (s : nat),
            containsWorkingTape tin[@Fin0] tp ->
            isRight_size tin[@Fin1] s ->
            containsWorkingTape tout[@Fin0] tp /\
            tout[@Fin1] ≃(retr_sigCurrentSymbol_sig; ReadCurrent_size s) current tp).

  Definition ReadCurrent'_steps := 7.

  Lemma ReadCurrent'_Sem : ReadCurrent' ⊨c(ReadCurrent'_steps) ReadCurrent'_Rel.
  Proof.
    unfold ReadCurrent'_steps. eapply RealiseIn_monotone.
    { unfold ReadCurrent'. apply Switch_RealiseIn. TM_Correct. apply ReadCurrent_Sem. intros c. TM_Correct.
      instantiate (1 := WriteValue_steps 1). apply WriteValue_Sem with (cX := Encode_map Encode_optSigM retr_sigCurrentSymbol_sig). }
    { cbn. reflexivity. }
    { intros tin ([], tout) H. cbn. intros tp s HCont HRight1. TMSimp. modpon H. modpon H0. subst. split; auto.
      contains_ext. unfold WriteValue_size, ReadCurrent_size. cbn. omega. }
  Qed.


  Definition DoAction : option sigM * move -> pTM sig^+ unit 1 :=
    fun '(m, w) => DoAct (map_opt (fun s => inr (Retr_f s)) m, w).

  Definition DoAction_Rel (a : option sigM * move) : pRel sig^+ unit 1 :=
    ignoreParam (fun tin tout => forall tp, containsWorkingTape tin[@Fin0] tp -> containsWorkingTape tout[@Fin0] (doAct tp a)).

  Lemma DoAction_Sem (a : option sigM * move) : DoAction a ⊨c(1) DoAction_Rel a.
  Proof.
    destruct a as [w m]. eapply RealiseIn_monotone.
    { unfold DoAction. TM_Correct. }
    { reflexivity. }
    { intros tin ([], tout) H. intros tp HCont. TMSimp. apply containsWorkingTape_doAct with (a := (w,m)) in HCont. auto. }
  Qed.


  (** Read an action and execute it *)

  Definition DoAction' : pTM sig^+ unit 2 :=
    Switch (CaseFin (FinType(EqType(option sigM * move))) ⇑ retr_act_sig @ [|Fin1|])
           (fun a => DoAction a @ [|Fin0|]).

  Local Instance Encode_action : codable (option sigM * move) (option sigM * move) := Encode_Finite _.

  Definition DoAction_size (a : option sigM * move) (s : nat) := (Reset_size a s).

  Definition DoAction'_Rel : pRel sig^+ unit 2 :=
    ignoreParam
      (fun tin tout => forall (tp : tape sigM) (a : option sigM * move) (s : nat),
           let size := DoAction_size a in
           containsWorkingTape tin[@Fin0] tp ->
           tin[@Fin1] ≃(retr_act_sig; s) a ->
           containsWorkingTape tout[@Fin0] (doAct tp a) /\
           isRight_size tout[@Fin1] (size s)).

  Definition DoAction'_steps := 7.

  Lemma DoAction'_Sem : DoAction' ⊨c(DoAction'_steps) DoAction'_Rel.
  Proof.
    unfold DoAction'_steps. eapply RealiseIn_monotone.
    { unfold DoAction'.
      apply Switch_RealiseIn. TM_Correct.
      intros a. TM_Correct. apply DoAction_Sem. }
    { cbn. reflexivity. }
    {
      intros tin ([], tout) H. cbn. intros tp [w m] s HCont HEncA. TMSimp.
      unfold DoAction_size in *.
      rename H into HCaseAct, H0 into HDoAct.
      modpon HCaseAct. inv HCaseAct0. modpon HDoAct. auto.
    }
  Qed.


  Definition SetFinal (final : bool) : pTM sig^+ unit 2 :=
    WriteValue [final] ⇑ retr_sigCurrentStateFinal_sig @ [|Fin1|];;
    Constr_pair (FinType(EqType bool)) (FinType(EqType sigNat)) ⇑ retr_sigCurrentState_sig  @ [|Fin1; Fin0|];;
    ResetEmpty1 _ @ [|Fin1|].

  Definition SetFinal_size : Vector.t (nat->nat) 2 :=
    [| Constr_pair_size true; WriteValue_size true >> ResetEmpty1_size |]. 

  Definition SetFinal_Rel (final : bool) : pRel sig^+ unit 2 :=
    ignoreParam
      (fun tin tout =>
         forall (q : nat) (s0 s1 : nat),
           tin[@Fin0] ≃(retr_sigCurrentStateNumber_sig; s0) q ->
           isRight_size tin[@Fin1] s1 ->
           tout[@Fin0] ≃(retr_sigCurrentState_sig; SetFinal_size@>Fin0 s0) (final, q) /\
           isRight_size tout[@Fin1] (SetFinal_size@>Fin1 s1)).

  Lemma SetFinal_Realise (final : bool) : SetFinal final ⊨ SetFinal_Rel final.
  Proof.
    eapply Realise_monotone.
    { unfold SetFinal.
      TM_Correct_step. TM_Correct_step. TM_Correct_step.
      eapply RealiseIn_Realise; apply WriteValue_Sem with (X := bool).
      TM_Correct.
      eapply RealiseIn_Realise; apply ResetEmpty1_Sem with (cX := Encode_map Encode_bool retr_sigCurrentStateFinal_sig). }
    {
      intros tin ([], tout) H. cbn. intros q s0 s1 HEncQ HRight. TMSimp. rename H into HWriteValue, H0 into HConstrPair, H1 into HReset.
      modpon HWriteValue. unfold tape_contains in HWriteValue. modpon HConstrPair. modpon HReset. auto.
    }
  Qed.

  Definition SetFinal_steps := 2 + WriteValue_steps 1 + Constr_pair_steps true + ResetEmpty1_steps.

  Definition SetFinal_T : tRel sig^+ 2 :=
    fun tin k => exists (q:nat), tin[@Fin0] ≃(retr_sigCurrentStateNumber_sig) q /\ isRight tin[@Fin1] /\ SetFinal_steps <= k.

  Lemma SetFinal_Terminates final : projT1 (SetFinal final) ↓ SetFinal_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold SetFinal. TM_Correct.
      - eapply RealiseIn_TerminatesIn. apply ResetEmpty1_Sem with (cX := Encode_map Encode_bool retr_sigCurrentStateFinal_sig). }
    {
      intros tin k (q&HEncQ&HRight&Hk). unfold SetFinal_steps in Hk.
      exists (WriteValue_steps 1), (1 + Constr_pair_steps true + ResetEmpty1_steps). repeat split; try omega.
      { hnf. cbn. reflexivity. }
      intros tmid [] (HWrite&HWriteInj); TMSimp. modpon HWrite.
      exists (Constr_pair_steps true), (ResetEmpty1_steps). repeat split; try omega. 2: reflexivity.
      { hnf. cbn. eexists. split. simpl_surject. contains_ext. reflexivity. }
    }
  Qed.

  

  Definition containsState (t : tape sig^+) (M : mTM sigM 1) (q : states M) :=
    t ≃(retr_sigCurrentState_sig) (halt q, index q).

  Definition containsState_size (t : tape sig^+) (M : mTM sigM 1) (q : states M) (s : nat) :=
    t ≃(retr_sigCurrentState_sig; s) (halt q, index q).

  Lemma containsState_size_containsState t M (q : states M) s :
    containsState_size t q s -> containsState t q.
  Proof. firstorder. Qed.

  Hint Resolve containsState_size_containsState : core.

  (*
  Definition IsFinal_size (M : mTM sigM 1) (q : states M) :=
    [| (*0*) CasePair_size0 _ (halt q) >> SetFinal_size@>Fin0; (*1*) CasePair_size1 _ (halt q) >> (S >> S) >> SetFinal_size@>Fin1|].
   *)

  Definition IsFinal_size := CasePair_size1 (default : bool) >> (S >> S) >> SetFinal_size@>Fin1.

  Definition IsFinal_Rel : pRel sig^+ bool 2 :=
    fun tin '(yout, tout) =>
      forall (M : mTM sigM 1) (q : states M) (s0 s1 : nat),
        let size := IsFinal_size in
        containsState_size tin[@Fin0] q s0 ->
        isRight_size tin[@Fin1] s1 ->
        containsState_size tout[@Fin0] q s0 /\
        isRight_size tout[@Fin1] (size s1) /\
        yout = halt q.

  Definition IsFinal : pTM sig^+ bool 2 :=
    CasePair (FinType(EqType bool)) (FinType(EqType sigNat)) ⇑ retr_sigCurrentState_sig @ [|Fin0; Fin1|];;
    If (CaseFin (FinType(EqType bool)) ⇑ retr_sigCurrentStateFinal_sig @ [|Fin1|])
       (Return (SetFinal true @ [|Fin0; Fin1|]) true)
       (Return (SetFinal false @ [|Fin0; Fin1|]) false).

  Lemma IsFinal_Realise : IsFinal ⊨ IsFinal_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold IsFinal. TM_Correct.
      - apply SetFinal_Realise.
      - apply SetFinal_Realise. }
    {
      intros tin (yout, tout) H. cbn. intros M q s0 s1 HEncQ HRight. TMSimp. rename H into HCase, H0 into HIf.
      unfold containsState_size in *.
      modpon HCase. cbn in *.
      destruct HIf; TMSimp.
      - modpon H. modpon H0. repeat split; auto. unfold containsState_size. contains_ext. congruence.
        unfold Constr_pair_size, CasePair_size0. cbn. omega.
      - modpon H. modpon H0. repeat split; auto. unfold containsState_size. contains_ext. congruence.
        unfold Constr_pair_size, CasePair_size0. cbn. omega.
    }
  Qed.

  Definition IsFinal_steps (final : bool) := 2 + CasePair_steps (final) + CaseFin_steps + SetFinal_steps.

  Definition IsFinal_T : tRel sig^+ 2 :=
    fun tin k => exists (M : mTM sigM 1) (q : states M), containsState tin[@Fin0] q /\ isRight tin[@Fin1] /\ IsFinal_steps (halt q) <= k.

  Lemma IsFinal_Terminates : projT1 IsFinal ↓ IsFinal_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold IsFinal. TM_Correct.
      - apply SetFinal_Terminates.
      - apply SetFinal_Terminates. }
    {
      intros tin k (M&q&HEncQ&HRight&Hk). unfold IsFinal_steps in Hk.
      exists (CasePair_steps (halt q)), (1 + CaseFin_steps + SetFinal_steps). repeat split; try omega.
      { hnf. cbn. eexists. split. simpl_surject. unfold containsState in HEncQ. eauto. cbn. reflexivity. }
      intros tmid [] (HCasePair&HCasePairInj); TMSimp. modpon HCasePair. cbn in *.
      { unfold containsState in *. cbn in *. simpl_surject. contains_ext. }
      exists (CaseFin_steps), (SetFinal_steps). repeat split; try omega.
      intros tmid0 ymid0 (HCaseFin&HCaseFinInj); TMSimp. modpon HCaseFin. subst.
      destruct (halt q).
      - hnf. cbn. eexists. repeat split. contains_ext. eauto. reflexivity.
      - hnf. cbn. eexists. repeat split. contains_ext. eauto. reflexivity.
    }
  Qed.
    

  (** Alternative form for the transition function (for efficiency) *)
  Definition graph_function (M : mTM sigM 1) : option sigM * states M -> ((option sigM * move) * states M) :=
    (fun '(s, q) =>
       let (q', acts) := trans (q, [|s|]) in
       let (w, m) := acts[@Fin0] in
       ((w, m), q')).

  Definition trans_map_keys (M : mTM sigM 1) :=
    fun (key : option sigM * (states M)) =>
      let (s,q) := key in
      (s, (halt q, index q)).

  Definition trans_map_values (M : mTM sigM 1) :=
    fun (value : (option sigM * move) * (states M)) =>
      let (act, q') := value in
      (act, (halt q', index q')).
        
  Definition graph_of_TM (M : mTM sigM 1) :
    list ((option sigM * (bool * nat)) * ((option sigM * move) * (bool * nat))) :=
    map (map_pair (trans_map_keys (M := M)) (trans_map_values (M := M)))
        (graph_of_fun (@graph_function M)).

  Local Instance Encode_graph : codable sigGraph (list ((option sigM * (bool * nat)) * ((option sigM * move) * (bool * nat)))) :=
    (Encode_list
       (Encode_pair (Encode_pair (Encode_Finite _) (Encode_pair Encode_bool Encode_nat))
                    (Encode_pair (Encode_Finite _) (Encode_pair Encode_bool Encode_nat)))).

  Lemma trans_map_keys_injective (M : mTM sigM 1) : injective (trans_map_keys (M:=M)).
  Proof. hnf. unfold trans_map_keys. intros (s1&q1) (s2&q2). intros H. inv H. f_equal. now apply injective_index in H3. Qed.

  Lemma lookup_graph (M : mTM sigM 1) (tp : tape sigM) (q : states M) :
    lookup (current tp, (halt q, index q)) (graph_of_TM M) =
    let (q', acts) := trans (q, [|current tp|]) in
    Some (acts[@Fin0], (halt q', index q')).
  Proof.
    destruct (trans (q, [|current tp|])) as [q' acts] eqn:E.
    unfold graph_of_TM.
    change (current tp, (halt q, index q)) with ((trans_map_keys (M:=M)) (current tp, q)).
    change (acts[@Fin0], (halt q', index q')) with ((trans_map_values (M:=M)) (acts[@Fin0], q')).
    apply lookup_map with (f := trans_map_keys (M:=M)) (g := trans_map_values (M:=M)).
    - apply trans_map_keys_injective.
    - replace (acts[@Fin0], q') with ((graph_function (M:=M)) (current tp, q)).
      + apply graph_of_fun_lookup.
      + cbn. rewrite E. now destruct (acts[@Fin0]).
  Qed.
  
  Definition containsTrans (t : tape sig^+) (M : mTM sigM 1) :=
    t ≃(retr_sigGraph_sig) (graph_of_TM M).

  Definition containsTrans_size (t : tape sig^+) (M : mTM sigM 1) (s : nat) :=
    t ≃(retr_sigGraph_sig; s) (graph_of_TM M).

  Lemma containsTrans_size_containsTrans t M s : containsTrans_size t M s -> containsTrans t M.
  Proof. intros H. unfold containsTrans, containsTrans_size in *. auto. Qed.
  Hint Resolve containsTrans_size_containsTrans : core.


  Local Arguments IsFinal_size : simpl never.
  Local Arguments ReadCurrent_size : simpl never.
  Local Arguments Lookup_size : simpl never.

  Definition Univ_Step_size (M : mTM sigM 1) (tp : tape sigM) (q : states M) : Vector.t (nat->nat) 6 :=
    (* Note that the size function for tape 0 is semantically irrelevant because there is no size associated to this (working) tape *)
    if halt q
    then [|IsFinal_size|]@>>[|Fin3|]
    else let (q', act) := trans (q, [|current tp|]) in
         ([|IsFinal_size|]@>>[|Fin3|]) >>>
         ([|ReadCurrent_size|]@>>[|Fin3|]) >>>
         ([|Constr_pair_size (current tp)|]@>>[|Fin2|]) >>>
         ([|Reset_size (current tp)|] @>> [|Fin3|]) >>>
         (Lookup_size (graph_of_TM M) (current tp, (halt q, index q)) @>> [|Fin1; Fin2; Fin3; Fin4; Fin5|]) >>>
         ([|CasePair_size0 act[@Fin0];
            CasePair_size1 act[@Fin0]|] @>> [|Fin2; Fin3|]) >>>
         ([|DoAction_size act[@Fin0]|] @>> [|Fin3|]).
  

  Definition Univ_Step_Rel : pRel sig^+ (option unit) 6 :=
    fun tin '(yout, tout) =>
      forall (M : mTM sigM 1) (tp : tape sigM) (q : states M) (s1 s2: nat) (sr : Vector.t nat 3),
        let size := Univ_Step_size tp q in
        containsWorkingTape tin[@Fin0] tp ->
        containsTrans_size tin[@Fin1] M s1 ->
        containsState_size tin[@Fin2] q s2 ->
        (forall (i : Fin.t 3), isRight_size tin[@FinR 3 i] sr[@i]) ->
        match yout, halt q with
        | Some tt, true =>
          containsWorkingTape tout[@Fin0] tp /\
          containsTrans_size tout[@Fin1] M (size@>Fin1 s1) /\
          containsState_size tout[@Fin2] q (size@>Fin2 s2) /\
          (forall (i : Fin.t 3), isRight_size tout[@FinR 3 i] (size@>(FinR 3 i) sr[@i]))
        | None, false =>
          let (q', tp') := step (mk_mconfig q [|tp|]) in
          containsWorkingTape tout[@Fin0] tp'[@Fin0] /\
          containsTrans_size tout[@Fin1] M (size@>Fin1 s1) /\
          containsState_size tout[@Fin2] q'(size@>Fin2 s2) /\
          (forall (i : Fin.t 3), isRight_size tout[@FinR 3 i] (size@>(FinR 3 i) sr[@i]))
        | _, _ => False
        end.

  Definition Univ_Step : pTM sig^+ (option unit) 6 :=
    If (IsFinal @ [|Fin2; Fin3|])
       (Return Nop (Some tt))
       (Return
          (ReadCurrent' @ [|Fin0; Fin3|];;
           Constr_pair (FinType(EqType (option sigM))) (FinType(EqType sigState)) ⇑ retr_key_sig @ [|Fin3; Fin2|];;
           Reset _ @ [|Fin3|];;
           Lookup _ _ ⇑ retr_sigGraph_sig @ [|Fin1; Fin2; Fin3; Fin4; Fin5|];;
           CasePair (FinType(EqType(option sigM * move))) (FinType(EqType(sigState))) ⇑ retr_value_sig @ [|Fin2; Fin3|];;
           DoAction' @ [|Fin0; Fin3|];;
           Translate retr_sigNextState_sig retr_sigCurrentState_sig @ [|Fin2|]) None).

  Lemma Univ_Step_Realise : Univ_Step ⊨ Univ_Step_Rel.
  Proof.
    eapply Realise_monotone.
    {
      (* Every [TM_Correct_step] step is good, except for [Constr_pair] and [CasePair], because it uses "non-standard" encodings, i.e. [Encode_Finite] *)
      unfold Univ_Step. TM_Correct_step. 2: TM_Correct. TM_Correct_step.
      apply IsFinal_Realise.
      TM_Correct_step. TM_Correct_step. TM_Correct_step.
      eapply RealiseIn_Realise; apply ReadCurrent'_Sem.
      TM_Correct_step. TM_Correct_step. TM_Correct_step.
      apply Constr_pair_Realise with (cX := Encode_Finite (FinType(EqType(option sigM)))) (cY := Encode_pair Encode_bool Encode_nat).
      TM_Correct_step. TM_Correct_step.
      apply Reset_Realise with (I := retr_sigCurrentSymbol_sig).
      TM_Correct_step. TM_Correct_step. TM_Correct_step.
      apply Lookup_Realise with (cX := (Encode_pair (Encode_Finite _) (Encode_pair Encode_bool Encode_nat)))
                                (cY := (Encode_pair (Encode_Finite _) (Encode_pair Encode_bool Encode_nat))).
      { apply transition_graph_injective. }
      TM_Correct_step. TM_Correct_step. TM_Correct_step.
      apply CasePair_Realise with (cX := Encode_Finite (FinType(EqType(option sigM*move)))) (cY := Encode_pair Encode_bool Encode_nat).
      TM_Correct_step. TM_Correct_step.
      eapply RealiseIn_Realise; apply DoAction'_Sem.
      TM_Correct_step.
      apply Translate_Realise with (X := (bool * nat)%type).
    }
    {
      intros tin (yout, tout) H. cbn. intros M tp q s1 s2 sr HEncTp HEncM HEncQ HRight.
      destruct H; TMSimp.
      { (* Halting state *)
        unfold Univ_Step_size. 
        modpon H. rewrite <- H1. repeat split; eauto.
        - intros i; destruct_fin i; TMSimp_goal; auto.
          all: cbn. all: apply HRight.
      }
      { (* Not a halting state *)
        rename H into HIsFinal, H0 into HReadCurrent, H1 into HConstrPair, H2 into HReset, H3 into HLookup,
        H4 into HCaseResult, H5 into HDoAction, H6 into HTranslate.
        unfold Univ_Step_size in *.
        modpon HIsFinal. rewrite <- HIsFinal1.
        modpon HReadCurrent.
        specialize (HConstrPair (current tp) (halt q, index q)).
        modpon HConstrPair.
        modpon HReset.
        specialize (HLookup (graph_of_TM M)).
        modpon HLookup.
        rewrite lookup_graph in HLookup. destruct (trans (q, [|current tp|])) as [q' acts] eqn:E. destruct ymid; auto; modpon HLookup.
        unfold Univ_Step_size in *.
        unfold step; cbn; unfold current_chars; cbn. rewrite E. simpl_vector. cbn.
        specialize (HCaseResult (acts[@Fin0], (halt q', index q'))). modpon HCaseResult. modpon HDoAction.
        modpon HTranslate. cbn in *.
        repeat split; eauto.
        - unfold containsState_size. contains_ext. rewrite !vector_tl_nth. unfold finType_CS.
          apply Nat.eq_le_incl. now repeat f_equal. (* use assumption about the step *)
        - intros i; destruct_fin i; cbn; TMSimp_goal; auto.
      }
    }
  Qed.

  Local Arguments Univ_Step_size : simpl never.


  Definition Univ_Step_steps_ConstrPair (tp : tape sigM) :=
    Constr_pair_steps (current tp).

  Definition Univ_Step_steps_ResetSymbol (tp : tape sigM) :=
    Reset_steps (current tp).

  Definition Univ_Step_steps_Lookup (M : mTM sigM 1) (q : states M) (tp : tape sigM) :=
    Lookup_steps (current tp, (halt q, index q)) (graph_of_TM M).

  Definition Univ_Step_steps_CasePair (a : option sigM * move) :=
    CasePair_steps a.

  Definition Univ_Step_steps_Translate (M : mTM sigM 1) (q' : states M) :=
    Translate_steps (halt q', index q').

  Definition Univ_Step_steps_IsFinal (M : mTM sigM 1) (q : states M) (tp : tape sigM) :=
    if halt q
    then 0
    else
      let (q', acts) := trans (q, [|current tp|]) in
      6 + ReadCurrent'_steps + Univ_Step_steps_ConstrPair tp + Univ_Step_steps_ResetSymbol tp +
      Univ_Step_steps_Lookup q tp + Univ_Step_steps_CasePair acts[@Fin0] + DoAction'_steps + Univ_Step_steps_Translate q'.

  Definition Univ_Step_steps (M : mTM sigM 1) (q : states M) (tp : tape sigM) : nat :=
    1 + IsFinal_steps (halt q) + Univ_Step_steps_IsFinal q tp.

  Definition Univ_Step_T : tRel sig^+ 6 :=
    fun tin k =>
      exists (M : mTM sigM 1) (tp : tape sigM) (q : states M),
        containsWorkingTape tin[@Fin0] tp /\
        containsTrans tin[@Fin1] M /\
        containsState tin[@Fin2] q /\
        (forall (i : Fin.t 3), isRight tin[@FinR 3 i]) /\
        Univ_Step_steps q tp <= k.
  
  Lemma Univ_Step_Terminates : projT1 Univ_Step ↓ Univ_Step_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Univ_Step.
      (* Every [TM_Correct_step] step is good, except for [Constr_pair] and [CasePair], because it uses "non-standard" encodings, i.e. [Encode_Finite] *)
      unfold Univ_Step. TM_Correct_step. 2: TM_Correct. TM_Correct_step.
      apply IsFinal_Realise. apply IsFinal_Terminates.
      TM_Correct_step. TM_Correct_step. TM_Correct_step.
      TM_Correct_step. TM_Correct_step. eapply RealiseIn_Realise; apply ReadCurrent'_Sem.
      TM_Correct_step. eapply RealiseIn_TerminatesIn; apply ReadCurrent'_Sem.
      TM_Correct_step. TM_Correct_step. TM_Correct_step.
      apply Constr_pair_Realise with (cX := Encode_Finite (FinType(EqType(option sigM)))) (cY := Encode_pair Encode_bool Encode_nat).
      TM_Correct_step. TM_Correct_step.
      apply Constr_pair_Terminates with (cX := Encode_Finite (FinType(EqType(option sigM)))).
      TM_Correct_step. TM_Correct_step.
      apply Reset_Realise with (I := retr_sigCurrentSymbol_sig).
      TM_Correct_step.
      apply Reset_Terminates with (I := retr_sigCurrentSymbol_sig).
      TM_Correct_step. TM_Correct_step. TM_Correct_step.
      apply Lookup_Realise with (cX := (Encode_pair (Encode_Finite _) (Encode_pair Encode_bool Encode_nat)))
                                (cY := (Encode_pair (Encode_Finite _) (Encode_pair Encode_bool Encode_nat))).
      { apply transition_graph_injective. }
      TM_Correct_step. TM_Correct_step.
      apply Lookup_Terminates with (cX := (Encode_pair (Encode_Finite _) (Encode_pair Encode_bool Encode_nat)))
                                (cY := (Encode_pair (Encode_Finite _) (Encode_pair Encode_bool Encode_nat))).
      { apply transition_graph_injective. }
      TM_Correct_step. TM_Correct_step. TM_Correct_step.
      apply CasePair_Realise with (cX := Encode_Finite (FinType(EqType(option sigM*move)))) (cY := Encode_pair Encode_bool Encode_nat).
      TM_Correct_step. TM_Correct_step.
      apply CasePair_Terminates with (cX := Encode_Finite (FinType(EqType(option sigM*move)))) (cY := Encode_pair Encode_bool Encode_nat).
      TM_Correct_step. TM_Correct_step.
      eapply RealiseIn_Realise; apply DoAction'_Sem.
      TM_Correct_step. eapply RealiseIn_TerminatesIn; apply DoAction'_Sem.
      TM_Correct_step.
      apply Translate_Terminates with (X := (bool * nat)%type).
    }
    {
      intros tin k. intros (M&tp&q&HEncTp&HEncM&HEncQ&HRight&Hk). unfold Univ_Step_steps in Hk.
      exists (IsFinal_steps (halt q)), (Univ_Step_steps_IsFinal q tp). repeat split; try omega.
      { hnf; cbn. do 3 eexists; repeat split; eauto. apply HRight. }
      intros tmid ymid (HIsFinal&HIsFinalInj); TMSimp. modpon HIsFinal; eauto.
      { unfold containsState, containsState_size in *. contains_ext. }
      { apply isRight_isRight_size; auto. }
      subst. unfold Univ_Step_steps_IsFinal. destruct (halt q).
      { (* halting state *) eauto. }
      { (* no halting state *)
        destruct (trans (q, [|current tp|])) as [q' acts] eqn:E.
        exists (ReadCurrent'_steps),
        (5 + Univ_Step_steps_ConstrPair tp + Univ_Step_steps_ResetSymbol tp +
         Univ_Step_steps_Lookup q tp + Univ_Step_steps_CasePair acts[@Fin0] + DoAction'_steps + Univ_Step_steps_Translate q'). repeat split; try omega.
        intros tmid0 [] (HReadCurrent&HReadCurrentInj); TMSimp. modpon HReadCurrent.
        exists (Univ_Step_steps_ConstrPair tp),
        (4 + Univ_Step_steps_ResetSymbol tp +
         Univ_Step_steps_Lookup q tp + Univ_Step_steps_CasePair acts[@Fin0] + DoAction'_steps + Univ_Step_steps_Translate q'). repeat split; try omega.
        { hnf; cbn. eexists; repeat split; eauto. simpl_surject. eauto. }
        intros tmid1 [] (HConstrPair&HConstrPairInj); TMSimp.
        specialize (HConstrPair (current tp) (halt q, index q)). modpon HConstrPair.
        exists (Univ_Step_steps_ResetSymbol tp), (3 + Univ_Step_steps_Lookup q tp + Univ_Step_steps_CasePair acts[@Fin0] + DoAction'_steps + Univ_Step_steps_Translate q'). repeat split; try omega.
        { eexists. repeat split; eauto. }
        intros tmid2 [] (HReset&HResetInj); TMSimp. modpon HReset.
        exists (Univ_Step_steps_Lookup q tp), (2 + Univ_Step_steps_CasePair acts[@Fin0] + DoAction'_steps + Univ_Step_steps_Translate q'). repeat split; try omega.
        { hnf; cbn. eexists. exists (current tp, (halt q, index q)). repeat split; simpl_surject; eauto. }
        intros tmid3 ymid3 (HLookup&HLookupInj); TMSimp. modpon HLookup.
        { simpl_surject. unfold containsTrans in *. contains_ext. }
        { simpl_surject. apply isRight_isRight_size; eauto. }
        { simpl_surject. apply isRight_isRight_size; eauto. }
        rewrite lookup_graph in HLookup. cbn in *. rewrite E in HLookup.
        destruct ymid3; auto. modpon HLookup.
        exists (Univ_Step_steps_CasePair acts[@Fin0]), (1 + DoAction'_steps + Univ_Step_steps_Translate q'). repeat split; try omega.
        { hnf; cbn. exists (acts[@Fin0], (halt q', index q')). repeat split; simpl_surject; eauto. }
        intros tmid4 [] (HCasePair&HCasePairInj); TMSimp. modpon HCasePair. cbn in *.
        exists (DoAction'_steps), (Univ_Step_steps_Translate q'). repeat split; try omega.
        intros tmid5  [] (HDoAction&HDoActionInj); TMSimp. modpon HDoAction.
        { hnf; cbn. exists (halt q', index q'). split; auto. }
      }
    }
  Qed.



  Definition Univ := While Univ_Step.


  Fixpoint Univ_size (M : mTM sigM 1) (tp : tape sigM) (q : states M) (k : nat) {struct k} : Vector.t (nat->nat) 6 :=
    match k with
    | 0 => Univ_Step_size tp q
    | S k' =>
      if halt q
      then Univ_Step_size tp q
      else let (q', tp') := step (mk_mconfig q [|tp|]) in
           Univ_Step_size tp q >>> Univ_size tp'[@Fin0] q' k'
    end.
  

  Definition Univ_Rel : pRel sig^+ unit 6 :=
    fun tin '(_, tout) =>
      forall (M : mTM sigM 1) (tp : tape sigM) (q : states M) (s1 s2 : nat) (sr : Vector.t nat 3),
        containsWorkingTape tin[@Fin0] tp ->
        containsTrans_size tin[@Fin1] M s1 ->
        containsState_size tin[@Fin2] q s2 ->
        (forall (i : Fin.t 3), isRight_size tin[@FinR 3 i] sr[@i]) ->
        exists k (oconf : mconfig sigM (states M) 1),
          let size := Univ_size tp q k in
          loopM (mk_mconfig q [|tp|]) k = Some oconf /\
          containsWorkingTape tout[@Fin0] (ctapes oconf)[@Fin0] /\
          containsTrans_size tout[@Fin1] M              (size@>Fin1 s1) /\
          containsState_size tout[@Fin2] (cstate oconf) (size@>Fin2 s2) /\
          (forall (i : Fin.t 3), isRight_size tout[@FinR 3 i] (size@>(FinR 3 i) sr[@i])).

  Lemma Univ_Realise : Univ ⊨ Univ_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Univ. TM_Correct. apply Univ_Step_Realise. }
    { apply WhileInduction; intros; cbn; intros M tp q s1 s2 sr HEncTp HEncM HEncQ HRight; cbn in *; destruct_unit.
      - modpon HLastStep. destruct (halt q) eqn:E; auto; modpon HLastStep.
        exists 0. eexists. cbn. unfold haltConf. cbn. rewrite E. repeat split; eauto.
      - modpon HStar. destruct (halt q) eqn:E; auto. destruct (step (mk_mconfig q [|tp|])) as [q' tp'] eqn:E2. modpon HStar.
        modpon HLastStep.
        { instantiate (1:=[|_;_;_|]). cbn. intros i. specialize(HStar2 i). destruct_fin i; cbn; auto. }
        destruct HLastStep as (k&oconf&HLastStep); modpon HLastStep.
        exists (S k). eexists. cbn. unfold haltConf. cbn. rewrite !E, !E2. repeat split; eauto.
        rewrite <- HLastStep. unfold loopM. f_equal. clear_all. destruct_tapes; auto.
        { intros i. specialize(HLastStep3 i). destruct_fin i; cbn; auto. }
    }
  Qed.


  Fixpoint Univ_steps (M : mTM sigM 1) (q : states M) (tp : tape sigM) (k : nat) : nat :=
    match k with
    | 0 => Univ_Step_steps q tp
    | S k' =>
      if halt q
      then Univ_Step_steps q tp
      else let (q', tp') := step (mk_mconfig q [|tp|]) in
           1 + Univ_Step_steps q tp + Univ_steps q' tp'[@Fin0] k'
    end.

  Definition Univ_T : tRel sig^+ 6 :=
    fun tin k =>
      exists (M : mTM sigM 1) (tp : tape sigM) (q : states M) (k' : nat) (q' : states M) (tp' : tape sigM),
        containsWorkingTape tin[@Fin0] tp /\
        containsTrans tin[@Fin1] M /\
        containsState tin[@Fin2] q /\
        (forall (i : Fin.t 3), isRight tin[@FinR 3 i]) /\
        loopM (mk_mconfig q [|tp|]) k' = Some (mk_mconfig q' [|tp'|]) /\
        Univ_steps q tp k' <= k.


  Lemma destruct_vector1 (X : Type) (v : Vector.t X 1) :
    exists x, v = [| x |].
  Proof. destruct_vector. eauto. Qed.
  
  Lemma Univ_Terminates : projT1 Univ ↓ Univ_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Univ. TM_Correct.
      - apply Univ_Step_Realise.
      - apply Univ_Step_Terminates. }
    { apply WhileCoInduction; intros. destruct HT as (M&tp&q&k'&q'&tp'&HEncTp&HEncM&HEncQ&HRight&HLoop&Hk).
      exists (Univ_Step_steps q tp). split. hnf; eauto 8.
      intros [ [] | ] tmid HStep; cbn in *.
      - modpon HStep.
        { unfold containsTrans, containsTrans_size in *. contains_ext. }
        { unfold containsState, containsState_size in *. contains_ext. }
        { instantiate (1 := [|_;_;_|]). intros i. specialize (HRight i). destruct_fin i; cbn; auto. }
        destruct (halt q) eqn:E; auto; modpon HStep. destruct k'; cbn in Hk; auto. rewrite E in Hk. auto.
      - modpon HStep.
        { unfold containsTrans, containsTrans_size in *. contains_ext. }
        { unfold containsState, containsState_size in *. contains_ext. }
        { instantiate (1 := [|_;_;_|]). intros i. specialize (HRight i). destruct_fin i; cbn; auto. }
        destruct (halt q) eqn:E; auto.
        unfold step, current_chars in HStep. cbn in *. destruct (trans (q, [|current tp|])) as [q'' acts] eqn:E'; modpon HStep. simpl_vector in HStep. cbn in *.
        pose proof destruct_vector1 acts as (act&->); cbn in *.
        destruct k' as [ | k']; cbn in *; unfold haltConf in *; cbn in *.
        + exfalso. rewrite E in HLoop. inv HLoop.
        + rewrite E in HLoop. unfold step, haltConf, current_chars in HLoop, Hk; cbn in *. rewrite E' in HLoop, Hk. rewrite E in Hk. simpl_vector in *. cbn in *.
          exists (Univ_steps q'' (doAct tp act) k'). split.
          * hnf. do 6 eexists; repeat split; eauto.
            intros i. specialize (HStep2 i). isRight_mono.
          * omega.
    }
  Qed.


End Univ.


Print Assumptions Univ_Realise.

