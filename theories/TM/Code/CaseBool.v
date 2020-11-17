(** * Constructors and Deconstructors for Bool *)

From Undecidability Require Import ProgrammingTools Code.

Section CaseBool.

  Local Notation sig := bool.
 
  Definition CaseBool : pTM bool^+ bool 1 :=
    Move Rmove;;
    Switch (ReadChar)
    (fun s => match s with
           | Some (inr x) => Return (Move Rmove) x
           | _ => Return (Nop) default
           end).

  Definition CaseBool_Rel : pRel bool^+ bool 1 :=
    fun tin '(yout, tout) => forall (x : sig) (s : nat), tin[@Fin0] ≃(;s) x -> isVoid_size tout[@Fin0] (S(S(s))) /\ yout = x.

  Definition CaseBool_steps := 5.



  Lemma CaseBool_Sem : CaseBool ⊨c(CaseBool_steps) CaseBool_Rel.
  Proof.
    TM_Correct_noSwitchAuto.
    unfold CaseBool_steps. eapply RealiseIn_monotone.
    { unfold CaseBool. TM_Correct. intros b.
      destructBoth b as [ [] | ].
      all:eapply RealiseIn_monotone';[TM_Correct | ]. 2:reflexivity. all:Lia.nia. }
    { Lia.nia. }
    {
      intros tin (yout, tout) H. intros x s HEncX.
      destruct HEncX as (ls&HEncX&Hs).  
      TMSimp. split. 2:auto. hnf. do 2 eexists. split;[f_equal| ]. cbn;nia.
    }
  Qed.

  (** There is no need for a constructor, just use [WriteValue] *)

End CaseBool.


Arguments CaseBool : simpl never.

Ltac smpl_TM_CaseBool :=
  once lazymatch goal with
  | [ |- CaseBool ⊨ _ ] => eapply RealiseIn_Realise; apply CaseBool_Sem
  | [ |- CaseBool ⊨c(_) _ ] => apply CaseBool_Sem
  | [ |- projT1 CaseBool ↓ _ ] => eapply RealiseIn_TerminatesIn; apply CaseBool_Sem
  end.

Smpl Add smpl_TM_CaseBool : TM_Correct.


From Undecidability Require Import HoareLogic HoareRegister HoareTactics.

Definition CaseBool_size (_ : bool) : Vector.t (nat->nat) 1 :=
   [|plus 2|].

Lemma CaseBool_SpecT_size (b : bool) (ss : Vector.t nat 1) :
  TripleT
    (tspec (([], withSpace  [|Contains _ b |] ss)))
    CaseBool_steps
    CaseBool
    (fun yout =>
       tspec
         ([yout = b],withSpace
            ([|Void|])
            (appSize (CaseBool_size b) ss))). 
Proof.  unfold withSpace.
  eapply RealiseIn_TripleT.
  - apply CaseBool_Sem.
  - intros tin yout tout H HEnc. specialize (HEnc Fin0). simpl_vector in *; cbn in *. modpon H.
    subst yout. tspec_solve. easy.
Qed.

Ltac hstep_Bool :=
  lazymatch goal with
  | [ |- TripleT ?P ?k CaseBool ?Q ] => eapply CaseBool_SpecT_size
  end.

Smpl Add hstep_Bool : hstep_Spec.