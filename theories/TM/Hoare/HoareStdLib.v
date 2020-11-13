(** ** Hoare Rules for Machines that do not reason on codes *)

From Undecidability.TM Require Import TMTac Basic.Basic Compound.MoveToSymbol.
From Undecidability.TM.Hoare Require Import HoareLogic HoareCombinators HoareRegister HoareTactics HoareTacticsView.


(** *** WriteValue *)

Lemma DoAct_SpecTReg (sig : finType) act (P : tape (boundary + sig) -> Prop):
TripleT (tspec (([], [|Custom P|]))) 1 (DoAct act)
        (fun _ => tspec (([], [|Custom (fun t => exists t', t = doAct t' act /\ P t')|]))).
Proof.
  eapply RealiseIn_TripleT.
  - apply DoAct_Sem.
  - intros tin [] tout H HEnc. cbn in *.
  specialize (HEnc Fin0). simpl_vector in *; cbn in *. tspec_solve. eauto.
Qed.


Ltac hstep_DoAct :=
  lazymatch goal with
  | [ |- TripleT ?P ?k (DoAct _) ?Q ] => eapply DoAct_SpecTReg
  | [ |- TripleT ?P ?k (Write _) ?Q ] => eapply DoAct_SpecTReg
  | [ |- TripleT ?P ?k (WriteMove _ _) ?Q ] => eapply DoAct_SpecTReg
  | [ |- TripleT ?P ?k (Move _) ?Q ] => eapply DoAct_SpecTReg
  end.

Smpl Add hstep_DoAct : hstep_smpl.


Lemma CaseChar_SpecTReg (sig F : finType) (f : option (boundary + sig) -> F) P:
TripleT ≃≃([],[|Custom P|])
  1 (CaseChar f) (fun y => ≃≃([exists t, y = f (current t) /\ P t],[|Custom (fun t => y = f (current t) /\ P t) |])).
Proof.
  eapply RealiseIn_TripleT. now apply CaseChar_Sem. cbn. intros ? ? ? [-> ->] [[] H']%tspecE.
  specialize  (H' Fin0). cbn in H'. eapply tspecI;cbn. now eauto. intros i; destruct_fin i. easy.
Qed.

Ltac hstep_CaseChar :=
lazymatch goal with
| [ |- TripleT ?P ?k (CaseChar _) ?Q ] => eapply CaseChar_SpecTReg
| [ |- TripleT ?P ?k ReadChar ?Q ] => refine (_ : TripleT _ _ (CaseChar (fun x => x)) _);eapply CaseChar_SpecTReg
end.
Smpl Add hstep_CaseChar : hstep_smpl.

Lemma MoveToSymbol_SpecTReg (sig : finType) (f : boundary + sig -> _) g tin:
TripleT ≃≃([],  [|Custom (eq tin) |])
    (MoveToSymbol_steps f g tin) (MoveToSymbol f g)
    (fun _ => ≃≃([], [|Custom (eq (MoveToSymbol_Fun f g tin))|])).
Proof. 
eapply Realise_TripleT.
- apply MoveToSymbol_Realise.
- apply MoveToSymbol_Terminates.
- intros ? [] tout H HEnc. cbn in *.
  specialize (HEnc Fin0). cbn in HEnc. subst. now tspec_solve.
- intros ? k HEnc Hk.
  specialize (HEnc Fin0) as HEnc0. simpl_vector in *; cbn in *. now subst.
Qed.

Ltac hstep_MoveToSymbol :=
lazymatch goal with
| [ |- TripleT ?P ?k (MoveToSymbol _ _) ?Q ] => eapply MoveToSymbol_SpecTReg
end.
Smpl Add hstep_MoveToSymbol : hstep_smpl.