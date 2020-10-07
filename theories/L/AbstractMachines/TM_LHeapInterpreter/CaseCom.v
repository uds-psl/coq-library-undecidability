(** * Constructors and Deconstructors for Comens *)

From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import TM.Code.CaseNat TM.Code.CaseSum TM.Code.CaseFin LM_heap_def .
From Undecidability.L.AbstractMachines.TM_LHeapInterpreter Require Import Alphabets.

Definition CaseCom : pTM sigCom^+ (option ACom) 1 :=
  If (CaseSum _ _)
     (Return Nop None)
     (Relabel (ChangeAlphabet (CaseFin (FinType(EqType(ACom))) ) _) Some).


Definition CaseCom_size (t : Tok) : nat -> nat :=
  match t with
  | varT n => S
  | _ => S >> S >> S
  end.

Definition CaseCom_Rel : pRel sigCom^+ (FinType (EqType (option ACom))) 1 :=
  fun tin '(yout, tout) =>
    forall (t : Tok) (s : nat),
      tin[@Fin0] ≃(;s) t ->
      match yout, t with
      | Some appAT, appT => isVoid_size tout[@Fin0] (CaseCom_size t s)
      | Some lamAT, lamT => isVoid_size tout[@Fin0] (CaseCom_size t s)
      | Some retAT, retT => isVoid_size tout[@Fin0] (CaseCom_size t s)
      | None, varT n => tout[@Fin0] ≃(;CaseCom_size t s) n
      | _, _ => False
      end
.

Definition CaseCom_steps := 11.

Lemma CaseCom_Sem : CaseCom ⊨c(CaseCom_steps) CaseCom_Rel.
Proof.
  unfold CaseCom_steps. eapply RealiseIn_monotone.
  { unfold CaseCom. TM_Correct. }
  { cbn. reflexivity. }
  {
    intros tin (yout, tout) H. intros t s HEncT. TMSimp.
    unfold sigCom in *.
    destruct H; TMSimp.
    { (* "Then" branche *)
      specialize (H t s HEncT).
      destruct t; auto.
    }
    { (* "Else" branche *)
      rename H into HCaseSum.
      simpl_tape in *; cbn in *.
      specialize (HCaseSum t s HEncT).
      destruct t; cbn in *; eauto; modpon H1; subst; eauto.
    }
  }
Qed.


(** Constructors *)

(** Use [WriteValue] for [appT], [lamT], and [retT] *)

Definition Constr_ACom (t : ACom) : pTM sigCom^+ unit 1 := WriteValue (encode (ACom2Com t)).
Definition Constr_ACom_Rel (t : ACom) : pRel sigCom^+ unit 1 :=
  Mk_R_p (ignoreParam (fun tin tout => isVoid tin -> tout ≃ ACom2Com t)).
Definition Constr_ACom_steps := 7.
Lemma Constr_ACom_Sem t : Constr_ACom t ⊨c(Constr_ACom_steps)Constr_ACom_Rel t.
Proof.
  unfold Constr_ACom_steps. eapply RealiseIn_monotone.
  - unfold Constr_ACom. apply WriteValue_Sem.
  - cbn. destruct t; cbn; reflexivity.
  - intros tin ((), tout) H. cbn in *. intros HRight.
    specialize H with (x := t) (1 := eq_refl). modpon H. contains_ext.
Qed.



Definition Constr_varT : pTM sigCom^+ unit 1 := Constr_inl _ _.
Definition Constr_varT_Rel : pRel sigCom^+ (FinType (EqType unit)) 1 :=
  Mk_R_p (ignoreParam (fun tin tout => forall (x : nat) (s : nat), tin ≃(;s) x -> tout ≃(;pred s) varT x)).
Definition Constr_varT_steps := 3.
Lemma Constr_varT_Sem : Constr_varT ⊨c(Constr_varT_steps) Constr_varT_Rel.
Proof.
  unfold Constr_varT_steps. eapply RealiseIn_monotone.
  - unfold Constr_varT. apply Constr_inl_Sem.
  - reflexivity.
  - intros tin ((), tout) H. intros n s HEncN. TMSimp. modpon H. auto.
Qed.


Arguments CaseCom : simpl never.
Arguments Constr_ACom : simpl never.
Arguments Constr_varT : simpl never.
