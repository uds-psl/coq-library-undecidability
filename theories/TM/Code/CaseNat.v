From Undecidability Require Import TM.Code.ProgrammingTools.

(* * Constructor and Deconstructor Machines for Natural Numbers *)

Lemma tl_length (X : Type) (xs : list X) :
  length (tl xs) = pred (length xs).
Proof. destruct xs; auto. Qed.

Hint Rewrite tl_length : list.


Section CaseNat.

  (* ** Deconstructor *)

  Definition CaseNat_Rel : Rel (tapes sigNat^+ 1) (bool * tapes sigNat^+ 1) :=
    Mk_R_p
      (fun tin '(yout, tout) =>
         forall (n : nat) (sn : nat),
           tin ≃(;sn) n ->
           match yout, n with
           | false, O => tout ≃(;sn) 0
           | true, S n' => tout ≃(;S sn) n'
           | _, _ => False
           end).

  Definition CaseNat : pTM sigNat^+ bool 1 :=
    Move Rmove;;
    Switch (ReadChar)
          (fun o => match o with
                 | Some (inr sigNat_S) => Return (Write (inl START)) true (* S *)
                 | Some (inr sigNat_O) => Return (Move Lmove) false (* O *)
                 | _ => Return (Nop) default (* invalid input *)
                 end).

  Definition CaseNat_steps := 5.

  Lemma CaseNat_Sem : CaseNat ⊨c(CaseNat_steps) CaseNat_Rel.
  Proof.
    unfold CaseNat_steps. eapply RealiseIn_monotone.
    { unfold CaseNat. TM_Correct. }
    { Unshelve. 4,8: reflexivity. all: lia. }
    {
      intros tin (yout&tout) H. intros n s HEncN. TMSimp.
      destruct HEncN as (r1&HEncN&Hs). TMSimp.
      destruct n; cbn in *; TMSimp.
      - repeat econstructor; auto.
      - hnf. eexists. split. f_equal. cbn. lia.
    }
  Qed.


  (* ** Constructors *)
  Section NatConstructor.

    Definition S_Rel : Rel (tapes sigNat^+ 1) (unit * tapes sigNat^+ 1) :=
      Mk_R_p (ignoreParam (fun tin tout => forall n sn : nat, tin ≃(;sn) n -> tout ≃(;pred sn) S n)).

    Definition Constr_S : pTM sigNat^+ unit 1 :=
      WriteMove (inr sigNat_S) Lmove;; Write (inl START).


    Definition Constr_S_steps := 3.

    Lemma Constr_S_Sem : Constr_S ⊨c(Constr_S_steps) S_Rel.
    Proof.
      unfold Constr_S_steps. eapply RealiseIn_monotone.
      { unfold Constr_S. TM_Correct. }
      { cbn. lia. }
      {
        intros tin (yout, tout) H. intros n sn HEncN.
        TMSimp. clear all except HEncN.
        destruct HEncN as (r1&->&Hs). cbn. simpl_tape.
        hnf. eexists. split. f_equal. simpl_list. lia.
      }
    Qed.


    Definition Constr_O_size := pred >> pred.

    Definition O_Rel : Rel (tapes sigNat^+ 1) (unit * tapes sigNat^+ 1) :=
      fun tin '(_, tout) => forall sn, isVoid_size tin[@Fin0] sn -> tout[@Fin0] ≃(;Constr_O_size sn) O.

    Definition Constr_O : pTM sigNat^+ unit 1 := WriteValue 0.

    Goal Constr_O = WriteMove (inl STOP) Lmove;; WriteMove (inr sigNat_O) Lmove;; Write (inl START).
    Proof. unfold Constr_O, WriteValue, WriteString.WriteString, encode, Encode_map, map, rev, Encode_nat, encode, repeat, app. reflexivity. Qed.
    Definition Constr_O_steps := 5.

    Lemma Constr_O_Sem : Constr_O ⊨c(Constr_O_steps) O_Rel.
    Proof.
      unfold Constr_O_steps. eapply RealiseIn_monotone.
      { unfold Constr_O. TM_Correct. }
      { cbn. reflexivity. }
      { intros tin (yout, tout) H. intros s HRight. cbn in H. unfold Constr_O_size in *.
        specialize (H _ HRight). contains_ext. unfold WriteValue_size. cbn. lia.
      }
    Qed.

  End NatConstructor.

End CaseNat.


(* ** Tactic Support *)

Ltac smpl_TM_CaseNat :=
  once lazymatch goal with
  | [ |- CaseNat ⊨ _ ] => eapply RealiseIn_Realise; apply CaseNat_Sem
  | [ |- CaseNat ⊨c(_) _ ] => apply CaseNat_Sem
  | [ |- projT1 (CaseNat) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply CaseNat_Sem
  | [ |- Constr_O ⊨ _ ] => eapply RealiseIn_Realise; apply Constr_O_Sem
  | [ |- Constr_O ⊨c(_) _ ] => apply Constr_O_Sem
  | [ |- projT1 (Constr_O) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply Constr_O_Sem
  | [ |- Constr_S ⊨ _ ] => eapply RealiseIn_Realise; apply Constr_S_Sem
  | [ |- Constr_S ⊨c(_) _ ] => apply Constr_S_Sem
  | [ |- projT1 (Constr_S) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply Constr_S_Sem
  end.

Smpl Add smpl_TM_CaseNat : TM_Correct.

From Undecidability Require Import HoareLogic HoareRegister HoareTactics.

Lemma Constr_O_SpecT_size (ss : Vector.t nat 1) :
  TripleT (≃≃(([], withSpace  [|Void |] ss))) Constr_O_steps Constr_O (fun _ => ≃≃(([], withSpace  [|Contains _ 0|] (appSize [|Constr_O_size|] ss)))).
Proof.  unfold withSpace.
  eapply RealiseIn_TripleT.
  - apply Constr_O_Sem.
  - intros tin [] tout H1 H2. cbn in *. specialize (H2 Fin0). simpl_vector in *; cbn in *. modpon H1. tspec_solve.
Qed.

Lemma Constr_S_SpecT_size :
  forall (y : nat) ss,
    TripleT (≃≃(([], withSpace  [|Contains _ y |] ss))) Constr_S_steps Constr_S
            (fun _ => ≃≃(([], withSpace  [|Contains _ (S y)|] (appSize [|S|] ss)))).
Proof.  unfold withSpace.
  intros y ss.
  eapply RealiseIn_TripleT.
  - apply Constr_S_Sem.
  - intros tin [] tout H HEnc. cbn in *.
    specialize (HEnc Fin0). simpl_vector in *; cbn in *. modpon H. tspec_solve.
Qed.

Definition CaseNat_size (n : nat) : Vector.t (nat->nat) 1 :=
  match n with
  | O => [|id|]
  | S n' => [|S|]
  end.

Lemma CaseNat_SpecT_size (y : nat) (ss : Vector.t nat 1) :
  TripleT
    ≃≃([], withSpace  [|Contains _ y |] ss)
    CaseNat_steps
    CaseNat
    (fun yout =>
       ≃≃([if yout then y <> 0 else y = 0],withSpace ([|Contains _ (pred y)|])
            (appSize (CaseNat_size y) ss))).
Proof.  unfold withSpace.
  eapply RealiseIn_TripleT.
  - apply CaseNat_Sem.
  - intros tin yout tout H HEnc. specialize (HEnc Fin0). simpl_vector in *; cbn in *. modpon H.
    destruct yout, y; cbn in *; auto.
    + tspec_solve. easy.
    + tspec_solve. easy.
Qed.

Ltac hstep_Nat :=
  lazymatch goal with
  | [ |- TripleT ?P ?k Constr_O ?Q ] => eapply Constr_O_SpecT_size
  | [ |- TripleT ?P ?k Constr_S ?Q ] => eapply Constr_S_SpecT_size
  | [ |- TripleT ?P ?k CaseNat ?Q ] => eapply CaseNat_SpecT_size
  end.

Smpl Add hstep_Nat : hstep_Spec.