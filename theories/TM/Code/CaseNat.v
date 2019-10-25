From Undecidability Require Import TM.Code.ProgrammingTools.

(** * Constructor and Deconstructor Machines for Natural Numbers *)

Lemma tl_length (X : Type) (xs : list X) :
  length (tl xs) = pred (length xs).
Proof. destruct xs; auto. Qed.

Hint Rewrite tl_length : list.


Section CaseNat.

  (** ** Deconstructor *)

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
    Move R;;
    Switch (ReadChar)
          (fun o => match o with
                 | Some (inr sigNat_S) => Return (Write (inl START)) true (* S *)
                 | Some (inr sigNat_O) => Return (Move L) false (* O *)
                 | _ => Return (Nop) default (* invalid input *)
                 end).

  Definition CaseNat_steps := 5.

  Lemma CaseNat_Sem : CaseNat ⊨c(CaseNat_steps) CaseNat_Rel.
  Proof.
    unfold CaseNat_steps. eapply RealiseIn_monotone.
    { unfold CaseNat. TM_Correct. }
    { Unshelve. 4,8: reflexivity. all: omega. }
    {
      intros tin (yout&tout) H. intros n s HEncN. TMSimp.
      destruct HEncN as (r1&HEncN&Hs). TMSimp.
      destruct n; cbn in *; TMSimp.
      - repeat econstructor; auto.
      - hnf. eexists. split. f_equal. cbn. omega.
    }
  Qed.


  (** ** Constructors *)
  Section NatConstructor.

    Definition S_Rel : Rel (tapes sigNat^+ 1) (unit * tapes sigNat^+ 1) :=
      Mk_R_p (ignoreParam (fun tin tout => forall n sn : nat, tin ≃(;sn) n -> tout ≃(;pred sn) S n)).

    Definition Constr_S : pTM sigNat^+ unit 1 :=
      WriteMove (inr sigNat_S) L;; Write (inl START).


    Definition Constr_S_steps := 3.

    Lemma Constr_S_Sem : Constr_S ⊨c(Constr_S_steps) S_Rel.
    Proof.
      unfold Constr_S_steps. eapply RealiseIn_monotone.
      { unfold Constr_S. TM_Correct. }
      { cbn. omega. }
      {
        intros tin (yout, tout) H. intros n sn HEncN.
        TMSimp. clear all except HEncN.
        destruct HEncN as (r1&->&Hs). cbn. simpl_tape.
        hnf. eexists. split. f_equal. simpl_list. omega.
      }
    Qed.


    Definition Constr_O_size := pred >> pred.

    Definition O_Rel : Rel (tapes sigNat^+ 1) (unit * tapes sigNat^+ 1) :=
      fun tin '(_, tout) => forall sn, isVoid_size tin[@Fin0] sn -> tout[@Fin0] ≃(;Constr_O_size sn) O.

    Definition Constr_O : pTM sigNat^+ unit 1 := WriteValue [ sigNat_O ].

    Goal Constr_O = WriteMove (inl STOP) L;; WriteMove (inr sigNat_O) L;; Write (inl START).
    Proof. unfold Constr_O, WriteValue, WriteString.WriteString, encode, Encode_map, map, rev, Encode_nat, encode, repeat, app. reflexivity. Qed.
    Definition Constr_O_steps := 5.

    Lemma Constr_O_Sem : Constr_O ⊨c(Constr_O_steps) O_Rel.
    Proof.
      unfold Constr_O_steps. eapply RealiseIn_monotone.
      { unfold Constr_O. TM_Correct. }
      { cbn. reflexivity. }
      { intros tin (yout, tout) H. intros s HRight. cbn in H. unfold Constr_O_size in *.
        specialize (H 0 s eq_refl HRight). contains_ext. unfold WriteValue_size. cbn. omega.
      }
    Qed.

  End NatConstructor.

End CaseNat.


(** ** Tactic Support *)

Ltac smpl_TM_CaseNat :=
  lazymatch goal with
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
