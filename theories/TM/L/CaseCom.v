(** * Constructors and Deconstructors for Comens *)

From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import TM.Code.CaseNat TM.Code.CaseSum TM.Code.CaseFin LM_heap_def .
From Undecidability.TM.L Require Import Alphabets.

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
      match yout with
      | Some c => 
          isVoid_size tout[@Fin0] (CaseCom_size t s) /\ ACom2Com c = t
      | None => exists n, t = varT n /\ tout[@Fin0] ≃(;CaseCom_size t s) n
      end.

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
      destruct t; cbn in H;now eauto.
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

Definition Constr_ACom (t : ACom) : pTM sigCom^+ unit 1 := WriteValue (ACom2Com t).
Definition Constr_ACom_Rel (t : ACom) : pRel sigCom^+ unit 1 :=
  Mk_R_p (ignoreParam (fun tin tout => isVoid tin -> tout ≃ ACom2Com t)).
Definition Constr_ACom_steps := 7.
Lemma Constr_ACom_Sem t : Constr_ACom t ⊨c(Constr_ACom_steps)Constr_ACom_Rel t.
Proof.
  unfold Constr_ACom_steps. eapply RealiseIn_monotone.
  - unfold Constr_ACom. apply WriteValue_Sem.
  - cbn. destruct t; cbn; reflexivity.
  - intros tin ((), tout) H. cbn in *. intros HRight.
    modpon H. contains_ext.
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

From Undecidability Require Import Hoare.

Lemma CaseCom_SpecT_size (t : Tok) (ss : Vector.t nat 1) :
  TripleT
    ≃≃([], withSpace  [|Contains _ t |] ss)
    CaseCom_steps
    CaseCom
     (fun yout => ≃≃([match yout with Some c => t = ACom2Com c | None => exists n, t = varT n end]
        ,withSpace ([|match Com_to_sum t with inr _ => Void | inl n => Contains _ n end|]) (appSize ([|CaseCom_size t|]) ss))).  
Proof.
  unfold withSpace.
  eapply RealiseIn_TripleT.
  - apply CaseCom_Sem.
  - intros tin yout tout H HEnc. specialize (HEnc Fin0). simpl_vector in *; cbn in *. modpon H.
    destruct yout.
    +destruct H as [? <-]. tspec_solve. easy. destruct a;cbn in *. all:isVoid_mono.
    +destruct H as (?&->&?). cbn. tspec_solve. easy.
Qed.

Ltac hstep_Com :=
  lazymatch goal with
  | [ |- TripleT ?P ?k CaseCom ?Q ] => eapply CaseCom_SpecT_size
  end.

Smpl Add hstep_Com : hstep_smpl.