(** * Implementation of [ϕ] (aka SplitBody) *)

From Undecidability Require Import TM.Code.ProgrammingTools.
From Undecidability Require Import TM.LM.Semantics TM.LM.Alphabets.
From Undecidability Require Import TM.LM.CaseCom.
From Undecidability Require Import TM.Code.ListTM TM.Code.CaseList TM.Code.CaseNat.

Local Arguments plus : simpl never.
Local Arguments mult : simpl never.


(** The [JumpTarget] machine only operates on programs. Thus we define [JumpTarget] on the alphabet [sigPro^+]. *)

(** This is the only way we can encode [nat] on [sigPro]: as a variable token. *)
Definition retr_nat_prog : Retract sigNat sigPro := Retract_sigList_X _.


(** append a token to the token list *)
Definition App_Commands : pTM sigPro^+ (FinType(EqType unit)) 2 :=
  App' _ @ [|Fin0; Fin1|];;
  MoveValue _ @ [|Fin1; Fin0|].

Definition App_Commands_size (Q Q' : list Com) : Vector.t (nat->nat) 2 :=
  [| MoveValue_size_y (Q ++ Q') Q; App'_size Q >> MoveValue_size_x (Q ++ Q') |].

Definition App_Commands_Rel : pRel sigPro^+ (FinType(EqType unit)) 2 :=
  ignoreParam (
      fun tin tout =>
        forall (Q Q' : list Com) (s0 s1 : nat),
          tin[@Fin0] ≃(;s0) Q ->
          tin[@Fin1] ≃(;s1) Q' ->
          tout[@Fin0] ≃(;App_Commands_size Q Q' @>Fin0 s0) Q ++ Q' /\
          isRight_size tout[@Fin1] (App_Commands_size Q Q' @>Fin1 s1)
    ).

Lemma App_Commands_Realise : App_Commands ⊨ App_Commands_Rel.
Proof.
  eapply Realise_monotone.
  { unfold App_Commands. TM_Correct.
    - apply App'_Realise with (X := Com).
    - apply MoveValue_Realise with (X := Pro).
  }
  {
    intros tin ((), tout) H. intros Q Q' s0 s1 HEncQ HEncQ'.
    TMSimp. modpon H. modpon H0. auto.
  }
Qed.

Arguments App_Commands_size : simpl never.


Definition App_Commands_steps (Q Q': Pro) := 1 + App'_steps Q + MoveValue_steps (Q ++ Q') Q.

Definition App_Commands_T : tRel sigPro^+ 2 :=
  fun tin k => exists (Q Q' : list Com), tin[@Fin0] ≃ Q /\ tin[@Fin1] ≃ Q' /\ App_Commands_steps Q Q' <= k.

Lemma App_Commands_Terminates : projT1 App_Commands ↓ App_Commands_T.
Proof.
  eapply TerminatesIn_monotone.
  { unfold App_Commands. TM_Correct.
    - apply App'_Realise with (X := Com).
    - apply App'_Terminates with (X := Com).
    - apply MoveValue_Terminates with (X := Pro) (Y := Pro).
  }
  {
    intros tin k (Q&Q'&HEncQ&HEncQ'&Hk).
    exists (App'_steps Q), (MoveValue_steps (Q++Q') Q); cbn; repeat split; try omega.
    hnf; cbn. eauto. now rewrite Hk.
    intros tmid () (HApp&HInjApp); TMSimp. modpon HApp.
    exists (Q++Q'), Q. repeat split; eauto.
  }
Qed.


(** append a token to the token list *)
Definition App_ACom (t : ACom) : pTM sigPro^+ unit 2 :=
  WriteValue (encode [ACom2Com t]) @ [|Fin1|];;
  App_Commands.

Definition App_ACom_size (t : ACom) (Q : list Com) : Vector.t (nat->nat) 2 :=
  [| id; WriteValue_size [ACom2Com t] |] >>> App_Commands_size Q [ACom2Com t].

Definition App_ACom_Rel (t : ACom) : pRel sigPro^+ unit 2 :=
  ignoreParam (
      fun tin tout =>
        forall (Q : list Com) (s0 s1:nat),
          tin[@Fin0] ≃(;s0) Q ->
          isRight_size tin[@Fin1] s1 ->
          tout[@Fin0] ≃(;App_ACom_size t Q @>Fin0 s0) Q ++ [ACom2Com t] /\
          isRight_size tout[@Fin1] (App_ACom_size t Q @>Fin1 s1)
    ).

Lemma App_ACom_Realise t : App_ACom t ⊨ App_ACom_Rel t.
Proof.
  eapply Realise_monotone.
  { unfold App_ACom. TM_Correct.
    - apply App_Commands_Realise.
  }
  {
    intros tin ((), tout) H. intros Q s0 s1 HENcQ HRight1.
    TMSimp. cbn in H. specialize H with (x := [ACom2Com t]) (1 := eq_refl). modpon H. modpon H0. auto.
  }
Qed.

Arguments App_ACom_size : simpl never.


Definition App_ACom_steps (Q: Pro) (t: ACom) := 1 + WriteValue_steps (size _ [ACom2Com t]) + App_Commands_steps Q [ACom2Com t].

Definition App_ACom_T (t: ACom) : tRel sigPro^+ 2 :=
  fun tin k => exists (Q: list Com), tin[@Fin0] ≃ Q /\ isRight tin[@Fin1] /\ App_ACom_steps Q t <= k.

Lemma App_ACom_Terminates (t: ACom) : projT1 (App_ACom t) ↓ App_ACom_T t.
Proof.
  eapply TerminatesIn_monotone.
  { unfold App_ACom. TM_Correct.
    - apply App_Commands_Terminates.
  }
  {
    intros tin k. intros (Q&HEncQ&HRight&Hk).
    exists (WriteValue_steps (size _ [ACom2Com t])), (App_Commands_steps Q [ACom2Com t]). cbn; repeat split; try omega.
    now rewrite Hk.
    intros tmid () (HWrite&HInjWrite); hnf; cbn; TMSimp.
    cbn in HWrite. specialize HWrite with (x := [ACom2Com t]) (1 := eq_refl).
    modpon HWrite. eauto.
  }
Qed.



(** Add a singleton list of tokes to [Q] *)
Definition App_Com : pTM sigPro^+ (FinType(EqType unit)) 3 :=
  Constr_nil _ @ [|Fin2|];;
  Constr_cons _@ [|Fin2; Fin1|];;
  App_Commands @ [|Fin0; Fin2|];;
  Reset _ @ [|Fin1|].

Definition App_Com_size (Q : list Com) (t : Com) : Vector.t (nat->nat) 3 :=
  [| App_Commands_size Q [t] @>Fin0; Reset_size t; pred >> Constr_cons_size t >> App_Commands_size Q [t] @>Fin1 |].

Definition App_Com_Rel : pRel sigPro^+ (FinType(EqType unit)) 3 :=
  ignoreParam (
      fun tin tout =>
        forall (Q : list Com) (t : Com) (s0 s1 s2 : nat),
          tin[@Fin0] ≃(;s0) Q ->
          tin[@Fin1] ≃(;s1) t ->
          isRight_size tin[@Fin2] s2 ->
          tout[@Fin0] ≃(;App_Com_size Q t @>Fin0 s0) Q ++ [t] /\
          isRight_size tout[@Fin1] (App_Com_size Q t @>Fin1 s1) /\
          isRight_size tout[@Fin2] (App_Com_size Q t @>Fin2 s2)
    ).


Lemma App_Com_Realise : App_Com ⊨ App_Com_Rel.
Proof.
  eapply Realise_monotone.
  { unfold App_Com. TM_Correct.
    - apply App_Commands_Realise.
    - apply Reset_Realise with (X := Com).
  }
  { intros tin ((), tout) H. cbn. intros Q t s0 s1 s2 HEncQ HEncT HRight.
    unfold sigPro, sigCom in *. TMSimp.
    rename H into HNil, H0 into HCons, H1 into HApp, H2 into HReset.
    modpon HNil. modpon HCons. modpon HApp. modpon HReset. repeat split; auto.
  }
Qed.

Arguments App_Com_size : simpl never.

Definition App_Com_steps (Q: Pro) (t:Com) :=
  3 + Constr_nil_steps + Constr_cons_steps t + App_Commands_steps Q [t] + Reset_steps t.

Definition App_Com_T : tRel sigPro^+ 3 :=
  fun tin k => exists (Q: list Com) (t: Com), tin[@Fin0] ≃ Q /\ tin[@Fin1] ≃ t /\ isRight tin[@Fin2] /\ App_Com_steps Q t <= k.

Lemma App_Com_Terminates : projT1 App_Com ↓ App_Com_T.
Proof.
  eapply TerminatesIn_monotone.
  { unfold App_Com. TM_Correct.
    - apply App_Commands_Realise.
    - apply App_Commands_Terminates.
    - apply Reset_Terminates with (X := Com).
  }
  {
    intros tin k (Q&t&HEncQ&HEncT&HRight&Hk). unfold App_Com_steps in Hk.
    exists (Constr_nil_steps), (1 + Constr_cons_steps t + 1 + App_Commands_steps Q [t] + Reset_steps t). cbn. repeat split; try omega.
    intros tmid () (HNil&HInjNil); TMSimp. modpon HNil.
    exists (Constr_cons_steps t), (1 + App_Commands_steps Q [t] + Reset_steps t). cbn. repeat split; try omega.
    eauto.
    unfold sigPro in *. intros tmid0 () (HCons&HInjCons); TMSimp. modpon HCons.
    exists (App_Commands_steps Q [t]), (Reset_steps t). cbn. repeat split; try omega.
    hnf; cbn. do 2 eexists; repeat split; eauto.
    intros tmid1 _ (HApp&HInjApp); TMSimp. modpon HApp.
    eexists. split; eauto.
  }
Qed.



Definition JumpTarget_Step : pTM sigPro^+ (option bool) 5 :=
  If (CaseList sigCom_fin @ [|Fin0; Fin3|])
     (Switch (ChangeAlphabet CaseCom _ @ [|Fin3|])
             (fun t : option ACom =>
                match t with
                | Some retAT =>
                  If (CaseNat ⇑ retr_nat_prog @ [|Fin2|])
                     (Return (App_ACom retAT @ [|Fin1; Fin4|]) None) (* continue *)
                     (Return (ResetEmpty1 _ @ [|Fin2|]) (Some true)) (* return true *)
                | Some lamAT =>
                  Return (Constr_S ⇑ retr_nat_prog @ [|Fin2|];;
                          App_ACom lamAT @ [|Fin1; Fin4|])
                         None (* continue *)
                | Some appAT =>
                  Return (App_ACom appAT @ [|Fin1;Fin4|])
                         None (* continue *)
                | None => (* Variable *)
                  Return (Constr_varT ⇑ _ @ [|Fin3|];;
                          App_Com @ [|Fin1; Fin3; Fin4|])
                         None (* continue *)
                end))
     (Return Nop (Some false)) (* return false *)
.


Definition JumpTarget_Step_size (P Q : Pro) (k : nat) : Vector.t (nat->nat) 5 :=
  match P with
  | retT :: _ =>
    match k with
    | S _ =>
      [| (*0*) CaseList_size0 retT; (*1*) App_ACom_size retAT Q @>Fin0; (*2*) S;                (*3*) CaseList_size1 retT >> CaseCom_size retT; (*4*) App_ACom_size retAT Q @>Fin1 |]
    | 0 =>
      [| (*0*) CaseList_size0 retT; (*1*) id;                           (*2*) ResetEmpty1_size; (*3*) CaseList_size1 retT >> CaseCom_size retT; (*4*) id |]
    end
  | lamT :: _ =>
    [| (*0*) CaseList_size0 lamT; (*1*) App_ACom_size lamAT Q @>Fin0; (*2*) pred; (*3*) CaseList_size1 lamT >> CaseCom_size lamT; (*4*) App_ACom_size lamAT Q @>Fin1 |]
  | appT :: _ =>
    [| (*0*) CaseList_size0 appT; (*1*) App_ACom_size appAT Q @>Fin0; (*2*) id; (*3*) CaseList_size1 retT >> CaseCom_size appT; (*4*) App_ACom_size appAT Q @>Fin1 |]
  | varT n :: _ =>
    [| (*0*) CaseList_size0 (varT n); (*1*) App_Com_size Q (varT n) @>Fin0; (*2*) id; (*3*) CaseList_size1 (varT n) >> CaseCom_size (varT n) >> pred >> App_Com_size Q (varT n) @>Fin1; (*4*) App_Com_size Q (varT n) @>Fin2 |]
  | nil => Vector.const id _
  end.


Definition JumpTarget_Step_Rel : pRel sigPro^+ (option bool) 5 :=
  fun tin '(yout, tout) =>
    forall (P Q : Pro) (k : nat) (s0 s1 s2 s3 s4 : nat),
      let size := JumpTarget_Step_size P Q k in
      tin[@Fin0] ≃(;s0) P ->
      tin[@Fin1] ≃(;s1) Q ->
      tin[@Fin2] ≃(;s2) k ->
      isRight_size tin[@Fin3] s3 -> isRight_size tin[@Fin4] s4 ->
      match yout, P with
      | _, retT :: P =>
        match yout, k with
        | Some true, O => (* return true *)
          tout[@Fin0] ≃(;size @>Fin0 s0) P /\
          tout[@Fin1] ≃(;size @>Fin1 s1) Q /\
          isRight_size tout[@Fin2] (size @>Fin2 s2)
        | None, S k' => (* continue *)
          tout[@Fin0] ≃(;size @>Fin0 s0) P /\
          tout[@Fin1] ≃(;size @>Fin1 s1) Q ++ [retT] /\
          tout[@Fin2] ≃(;size @>Fin2 s2) k'
        | _, _ => False (* not the case *)
        end
      | None, lamT :: P => (* continue *)
        tout[@Fin0] ≃(;size@>Fin0 s0) P /\
        tout[@Fin1] ≃(;size@>Fin1 s1) Q ++ [lamT] /\
        tout[@Fin2] ≃(;size@>Fin2 s2) S k
      | None, t :: P => (* continue *)
        tout[@Fin0] ≃(;size@>Fin0 s0) P /\
        tout[@Fin1] ≃(;size@>Fin1 s1) Q ++ [t] /\
        tout[@Fin2] ≃(;size@>Fin2 s2) k
      | Some false, nil => (* return false *)
        True
      | _, _ => False (* not the case *)
      end /\
      isRight_size tout[@Fin3] (size@>Fin3 s3) /\
      isRight_size tout[@Fin4] (size@>Fin4 s4).


Lemma JumpTarget_Step_Realise : JumpTarget_Step ⊨ JumpTarget_Step_Rel.
Proof.
  eapply Realise_monotone.
  { unfold JumpTarget_Step. TM_Correct.
    - eapply RealiseIn_Realise. apply CaseCom_Sem.
    - apply App_ACom_Realise.
    - eapply RealiseIn_Realise. apply ResetEmpty1_Sem with (X := nat).
    - apply App_ACom_Realise.
    - apply App_ACom_Realise.
    - eapply RealiseIn_Realise. apply Constr_varT_Sem.
    - apply App_Com_Realise.
  }
  {
    intros tin (yout, tout) H. cbn. intros P Q k s0 s1 s2 s3 s4 HEncP HEncQ HEncK HInt3 HInt4.
    unfold sigPro in *. rename H into HIf.
    destruct HIf; TMSimp.
    { (* Then of [CaseList], i.e. P = t :: P' *) rename H into HCaseList, H0 into HCaseCom, H1 into HCase.
      modpon HCaseList. destruct P as [ | t P']; auto; modpon HCaseList.
      modpon HCaseCom.
      destruct ymid as [ [ | | ] | ]; try destruct t; auto; simpl_surject; TMSimp.
      { (* t = retT *)
        destruct HCase; TMSimp.
        { (* k = S k' *) rename H into HCaseNat, H0 into HApp.
          modpon HCaseNat. destruct k as [ | k']; auto; modpon HCaseNat.
          modpon HApp.
          repeat split; auto.
        }
        { (* k = 0 *) rename H into HCaseNat. rename H0 into HReset.
          modpon HCaseNat. destruct k as [ | k']; auto; modpon HCaseNat. modpon HReset .
          repeat split; auto.
        }
      }
      { (* t = lamT *) rename H into HS, H0 into HApp.
        modpon HS.
        modpon HApp.
        repeat split; auto.
      }
      { (* t = appT *) rename H into HApp.
        modpon HApp.
        repeat split; auto.
      }
      { (* t = varT *) rename H into HVar, H0 into HApp.
        modpon HVar.
        modpon HApp.
        repeat split; auto.
      }
    }
    { (* Else of [CaseList], i.e. P = nil *)
      modpon H. destruct P; auto; modpon H; auto.
    }
  }
Qed.

Arguments JumpTarget_Step_size : simpl never.


(* Steps after the [CaseCom], depending on [t] *)
Local Definition JumpTarget_Step_steps_CaseCom (Q: Pro) (k: nat) (t: Com) :=
  match t with
  | retT =>
    match k with
    | S _ => 1 + CaseNat_steps + App_ACom_steps Q retAT
    | 0 => 2 + CaseNat_steps + ResetEmpty1_steps
    end
  | lamT => 1 + Constr_S_steps + App_ACom_steps Q lamAT
  | appT => App_ACom_steps Q appAT
  | varT n => 1 + Constr_varT_steps + App_Com_steps Q t
  end.

(* Steps after the [CaseList] *)
Local Definition JumpTarget_Step_steps_CaseList (P Q : Pro) (k: nat) :=
  match P with
  | t :: P' => 1 + CaseCom_steps + JumpTarget_Step_steps_CaseCom Q k t
  | nil => 0
  end.

(* Total steps *)
Definition JumpTarget_Step_steps (P Q: Pro) (k: nat) :=
  1 + CaseList_steps P + JumpTarget_Step_steps_CaseList P Q k.


Definition JumpTarget_Step_T : tRel sigPro^+ 5 :=
  fun tin steps => (* Warning: I have to use another variable for the steps, since [k] is used. *)
    exists (P Q : Pro) (k : nat),
      tin[@Fin0] ≃ P /\
      tin[@Fin1] ≃ Q /\
      tin[@Fin2] ≃ k /\
      isRight tin[@Fin3] /\ isRight tin[@Fin4] /\
      JumpTarget_Step_steps P Q k <= steps.

Lemma JumpTarget_Step_Terminates : projT1 JumpTarget_Step ↓ JumpTarget_Step_T.
Proof.
  eapply TerminatesIn_monotone.
  { unfold JumpTarget_Step. TM_Correct.
    - eapply RealiseIn_Realise. apply CaseCom_Sem.
    - eapply RealiseIn_TerminatesIn. apply CaseCom_Sem.
    - apply App_ACom_Terminates.
    - eapply RealiseIn_TerminatesIn. apply ResetEmpty1_Sem with (X := nat).
    - apply App_ACom_Terminates.
    - apply App_ACom_Terminates.
    - eapply RealiseIn_Realise. apply Constr_varT_Sem.
    - eapply RealiseIn_TerminatesIn. apply Constr_varT_Sem.
    - apply App_Com_Terminates.
  }
  {
    intros tin steps (P&Q&k&HEncP&HEncQ&HEncK&HRight3&HRight4&Hk). unfold JumpTarget_Step_steps in Hk. cbn in *.
    unfold sigPro in *.
    exists (CaseList_steps P), (JumpTarget_Step_steps_CaseList P Q k). cbn; repeat split; try omega. eauto.
    intros tmid bmatchlist (HCaseList&HCaseListInj); TMSimp. modpon HCaseList.
    destruct bmatchlist, P as [ | t P']; auto; modpon HCaseList.
    { (* P = t :: P' (* other case is done by auto *) *)
      exists (CaseCom_steps), (JumpTarget_Step_steps_CaseCom Q k t). cbn; repeat split; try omega.
      intros tmid1 ytok (HCaseCom&HCaseComInj); TMSimp. modpon HCaseCom.
      destruct ytok as [ [ | | ] | ]; destruct t; auto; simpl_surject; TMSimp.
      { (* t = retT *)
        exists CaseNat_steps.
        destruct k as [ | k'].
        - (* k = 0 *)
          exists ResetEmpty1_steps. repeat split; try omega.
          intros tmid2 bCaseNat (HCaseNat&HCaseNatInj); TMSimp. modpon HCaseNat. destruct bCaseNat; auto.
        - (* k = S k' *)
          exists (App_ACom_steps Q retAT). repeat split; try omega.
          intros tmid2 bCaseNat (HCaseNat&HCaseNatInj); TMSimp. modpon HCaseNat. destruct bCaseNat; auto. hnf; cbn. eauto.
      }
      { (* t = lamT *)
        exists (Constr_S_steps), (App_ACom_steps Q lamAT). repeat split; try omega.
        intros tmid2 () (HS&HSInj); TMSimp. modpon HS. hnf; cbn. eauto.
      }
      { (* t = appT *) hnf; cbn; eauto. }
      { (* t = varT n *)
        exists (Constr_varT_steps), (App_Com_steps Q (varT n)). repeat split; try omega.
        intros tmid2 H (HVarT&HVarTInj); TMSimp. modpon HVarT. hnf; cbn. eauto 6.
      }
    }
  }
Qed.



Fixpoint jumpTarget_k (k:nat) (P:Pro) : nat :=
  match P with
  | retT :: P' => match k with
                 | 0 => 0
                 | S k' => jumpTarget_k k' P'
                 end
  | lamT :: P' => jumpTarget_k (S k) P'
  | t :: P'    => jumpTarget_k k P' (* either [varT n] or [appT] *)
  | []         => k
  end.

Goal forall k P, jumpTarget_k k P <= k + |P|.
Proof.
  intros k P. revert k. induction P as [ | t P IH]; intros; cbn in *.
  - omega.
  - destruct t; cbn.
    + rewrite IH. omega.
    + rewrite IH. omega.
    + rewrite IH. omega.
    + destruct k. omega. rewrite IH. omega.
Qed.


Definition JumpTarget_Loop := While JumpTarget_Step.


Fixpoint JumpTarget_Loop_size (P Q : Pro) (k : nat) {struct P} : Vector.t (nat->nat) 5 :=
      match P with
      | retT :: P' =>
        match k with
        | O => (* return true *)
          JumpTarget_Step_size P Q k
        | S k' => (* continue *)
          JumpTarget_Step_size P Q k >>> JumpTarget_Loop_size P' (Q ++ [retT]) k'
        end
      | lamT :: P' => (* continue; increase k *)
        JumpTarget_Step_size P Q k >>> JumpTarget_Loop_size P' (Q ++ [lamT]) (S k)
      | t :: P' => (* continue *)
        JumpTarget_Step_size P Q k >>> JumpTarget_Loop_size P' (Q ++ [t]) k
      | nil => (* return false *)
        JumpTarget_Step_size P Q k
      end.


Definition JumpTarget_Loop_Rel : pRel sigPro^+ bool 5 :=
  fun tin '(yout, tout) =>
    forall (P Q : Pro) (k : nat) (s0 s1 s2 s3 s4 : nat),
      let size := JumpTarget_Loop_size P Q k in
      tin[@Fin0] ≃(;s0) P ->
      tin[@Fin1] ≃(;s1) Q ->
      tin[@Fin2] ≃(;s2) k ->
      isRight_size tin[@Fin3] s3 -> isRight_size tin[@Fin4] s4 ->
      match yout with
      | true =>
        exists (P' Q' : Pro),
        jumpTarget k Q P = Some (Q', P') /\
        tout[@Fin0] ≃(;size@>Fin0 s0) P' /\
        tout[@Fin1] ≃(;size@>Fin1 s1) Q' /\
        isRight_size tout[@Fin2] (size@>Fin2 s2) /\
        isRight_size tout[@Fin3] (size@>Fin3 s3) /\ isRight_size tout[@Fin4] (size@>Fin4 s4)
      | false =>
        jumpTarget k Q P = None
      end.



Lemma JumpTarget_Loop_Realise : JumpTarget_Loop ⊨ JumpTarget_Loop_Rel.
Proof.
  eapply Realise_monotone.
  { unfold JumpTarget_Loop. TM_Correct.
    - apply JumpTarget_Step_Realise.
  }
  {
    apply WhileInduction; intros; intros P Q k s0 s1 s2 s3 s4 size HEncP HEncQ HEncK HRight3 HRight4; subst size; cbn in *.
    {
      modpon HLastStep. destruct yout, P as [ | [ | | | ] P']; auto. destruct k; auto. modpon HLastStep.
      cbn. eauto 10.
    }
    {
      modpon HStar.
      destruct P as [ | [ | | | ] P']; auto; modpon HStar.
      - (* P = varT n :: P' *) modpon HLastStep. destruct yout; auto.
      - (* P = appT :: P' *) modpon HLastStep. destruct yout; auto.
      - (* P = lamT :: P' *) modpon HLastStep. destruct yout; auto.
      - (* P = varT k :: P', k = S k' *) destruct k as [ | k']; auto; modpon HStar. modpon HLastStep. destruct yout; auto.
    }
  }
Qed.


Fixpoint JumpTarget_Loop_steps (P Q: Pro) (k: nat) : nat :=
  match P with
  | nil => JumpTarget_Step_steps P Q k
  | t :: P' =>
    match t with
    | retT =>
      match k with
      | S k' => 1 + JumpTarget_Step_steps P Q k + JumpTarget_Loop_steps P' (Q++[t]) k'
      | 0 =>        JumpTarget_Step_steps P Q k (* terminal case *)
      end
    | lamT =>   1 + JumpTarget_Step_steps P Q k + JumpTarget_Loop_steps P' (Q++[t]) (S k)
    | appT =>   1 + JumpTarget_Step_steps P Q k + JumpTarget_Loop_steps P' (Q++[t]) k
    | varT n => 1 + JumpTarget_Step_steps P Q k + JumpTarget_Loop_steps P' (Q++[t]) k
    end
  end.

Definition JumpTarget_Loop_T : tRel sigPro^+ 5 :=
  fun tin steps =>
    exists (P Q : Pro) (k : nat),
      tin[@Fin0] ≃ P /\
      tin[@Fin1] ≃ Q /\
      tin[@Fin2] ≃ k /\
      isRight tin[@Fin3] /\ isRight tin[@Fin4] /\
      JumpTarget_Loop_steps P Q k <= steps.


Lemma JumpTarget_Loop_Terminates : projT1 JumpTarget_Loop ↓ JumpTarget_Loop_T.
Proof.
  eapply TerminatesIn_monotone.
  { unfold JumpTarget_Loop. TM_Correct.
    - apply JumpTarget_Step_Realise.
    - apply JumpTarget_Step_Terminates. }
  {
    apply WhileCoInduction. intros tin steps. intros (P&Q&k&HEncP&HEncQ&HEncK&HRight3&HRight4&Hk).
    exists (JumpTarget_Step_steps P Q k). repeat split. hnf; cbn; eauto 10.
    intros ymid tmid HStep. cbn in HStep. modpon HStep. destruct ymid as [ [ | ] | ].
    { (* [Some true], i.e. [P = retT :: P'] and [k = 0] *)
      destruct P as [ | [ | | | ] ]; auto. destruct k; auto.
    }
    { (* [Some false], i.e. [P = nil] *)
      destruct P as [ | [ | | | ] ]; auto.
    }
    { (* recursion cases *)
      destruct P as [ | t P ]; auto.
      destruct t; modpon HStep.
      - (* t = varT n *)
        exists (JumpTarget_Loop_steps P (Q++[varT n]) k). split.
        + hnf. do 3 eexists; repeat split; eauto.
        + assumption.
      - (* t = appT *)
        exists (JumpTarget_Loop_steps P (Q++[appT]) k). split.
        + hnf. do 3 eexists; repeat split; eauto.
        + assumption.
      - (* t = lamT *)
        exists (JumpTarget_Loop_steps P (Q++[lamT]) (S k)). split.
        + hnf. do 3 eexists; repeat split; eauto.
        + assumption.
      - (* t = retT, k = S k' *)
        destruct k as [ | k']; auto; modpon HStep.
        exists (JumpTarget_Loop_steps P (Q++[retT]) k'). split.
        + hnf. do 3 eexists; repeat split; eauto.
        + assumption.
    }
  }
Qed.


Definition JumpTarget : pTM sigPro^+ bool 5 :=
  Constr_nil _ @ [|Fin1|];;
  Constr_O ⇑ _ @ [|Fin2|];;
  JumpTarget_Loop.

Definition JumpTarget_size (P : Pro) : Vector.t (nat->nat) 5 :=
  [| id; pred; Constr_O_size; id; id |] >>> JumpTarget_Loop_size P nil 0.


Definition JumpTarget_Rel : pRel sigPro^+ bool 5 :=
  fun tin '(yout, tout) =>
    forall (P : Pro) (s0 s1 : nat) (si : Vector.t nat 3),
      tin[@Fin0] ≃(;s0) P ->
      isRight_size tin[@Fin1] s1 ->
      (forall i : Fin.t 3, isRight_size tin[@FinR 2 i : Fin.t 5] si[@i]) ->
      match yout with
      | true =>
        exists (P' Q' : Pro),
        jumpTarget 0 nil P = Some (Q', P') /\
        tout[@Fin0] ≃(;JumpTarget_size P @>Fin0 s0) P' /\
        tout[@Fin1] ≃(;JumpTarget_size P @>Fin1 s1) Q' /\
        (forall i : Fin.t 3, isRight_size tout[@FinR 2 i : Fin.t 5] (JumpTarget_size P @>(FinR 2 i) si[@i]))
      | false =>
        jumpTarget 0 nil P = None
      end.


Lemma JumpTarget_Realise : JumpTarget ⊨ JumpTarget_Rel.
Proof.
  eapply Realise_monotone.
  { unfold JumpTarget. TM_Correct.
    - apply JumpTarget_Loop_Realise.
  }
  {
    intros tin (yout, tout) H. cbn. intros P s0 s1 sr HEncP HOut HInt.
    TMSimp ( unfold sigPro, sigCom in * ). rename H into HWriteNil, H0 into HWriteO, H1 into HLoop.
    specialize (HInt Fin0) as HRight2.
    modpon HWriteNil.
    modpon HWriteO.
    modpon HLoop.
    destruct yout.
    - destruct HLoop as (P'&Q'&HLoop); modpon HLoop. do 2 eexists; repeat split; eauto.
      intros i; destruct_fin i; TMSimp_goal; auto.
    - eauto.
  }
Qed.


Definition JumpTarget_steps (P : Pro) :=
  3 + Constr_nil_steps + Constr_O_steps + JumpTarget_Loop_steps P nil 0.


Definition JumpTarget_T : tRel sigPro^+ 5 :=
  fun tin k =>
    exists (P : Pro),
      tin[@Fin0] ≃ P /\
      isRight tin[@Fin1] /\
      (forall i : Fin.t 3, isRight tin[@Fin.R 2 i]) /\
      JumpTarget_steps P <= k.


Lemma JumpTarget_Terminates : projT1 JumpTarget ↓ JumpTarget_T.
Proof.
  eapply TerminatesIn_monotone.
  { unfold JumpTarget. TM_Correct.
    - apply JumpTarget_Loop_Terminates.
  }
  {
    intros tin k (P&HEncP&Hout&HInt&Hk). unfold JumpTarget_steps in Hk.
    specialize (HInt Fin0) as HRight2.
    exists (Constr_nil_steps), (1 + Constr_O_steps + 1 + JumpTarget_Loop_steps P nil 0).
    cbn; repeat split; try omega.
    intros tmid () (HWrite&HWriteInj); TMSimp. modpon HWrite.
    exists (Constr_O_steps), (1 + JumpTarget_Loop_steps P nil 0).
    cbn; repeat split; try omega.
    cbn in *. unfold sigPro in *. intros tmid1 () (HWrite'&HWriteInj'); TMSimp. modpon HWrite'.
    { hnf. do 3 eexists; repeat split; cbn in *; unfold sigPro in *; cbn in *; TMSimp_goal; eauto. }
  }
Qed.
