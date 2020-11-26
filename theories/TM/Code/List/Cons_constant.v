From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import CaseList WriteString Hoare. 

Module Cons_constant.
Section Fix.

  Context {Σ__X: finType} {X : Type} {cX : codable Σ__X X}.

  
  (* Local Instance retr_X : Retract Σ__X Σ := (Retract_sigList_X _). *)

  Variable (c:X).

  Definition M : pTM (sigList Σ__X)^+ unit 1 :=
      WriteString Lmove (rev (inr sigList_cons::map (fun x => inr (sigList_X x)) ((encode c))));;
      Move Lmove;;
      Write (inl START).

  Definition Rel : pRel (sigList Σ__X)^+ unit 1 :=
    ignoreParam (
        fun tin tout =>
          forall l (s0 : nat),
            tin[@Fin0] ≃(;s0) l ->
            tout[@Fin0] ≃(;s0 - size c - 1) c :: l
    ).

  
  Lemma Realise : M ⊨ Rel.
  Proof.
    eapply Realise_monotone.
    { unfold M. TM_Correct. eapply RealiseIn_Realise,WriteString_Sem. }
    {
      intros tin ((), tout) H. TMSimp.
      destruct H2 as (?&->&?);cbn.
      simpl_tape.
      rewrite WriteString_L_left;cbn. autorewrite with list.
      erewrite !tape_right_move_left. 
      2:{rewrite WriteString_L_current. autorewrite with list. cbn. reflexivity. }   
      rewrite WriteString_L_right. cbn.
      eexists. repeat (cbn;autorewrite with list;try rewrite !map_map).
      split. reflexivity.
      rewrite tl_length,List.skipn_length. unfold size. nia.
    }
  Qed.

  Definition time {sigX} {X : Type} {cX : codable sigX X} (c:X) := 5 + 2 * size c.

  Lemma Terminates :
    projT1 M ↓
           (fun tin k =>
              exists (l: list X) ,
                tin[@Fin0] ≃ l /\
                time c<= k).
  Proof.
    unfold Constr_cons_steps. eapply TerminatesIn_monotone.
    { unfold M. TM_Correct.
      eapply RealiseIn_Realise. 2:eapply RealiseIn_TerminatesIn.
      all:apply WriteString_Sem.
    }
    {
      intros tin k (l&Hin&Hk). cbn. autorewrite with list.
      infTer 4.
      2:{
        intros. infTer 4. intros. reflexivity.   
      }
      cbn. unfold time,size in Hk. nia.
    } 
  Qed.

  Lemma SpecT (l:list X) ss:
    TripleT ≃≃([],withSpace [|Contains _ l|] ss) (time c) M (fun _ => ≃≃([],withSpace [|Contains _ (c::l)|] (appSize [|fun s0 => s0 - size c - 1|] ss ))).
  Proof.
    unfold withSpace in *.
    eapply Realise_TripleT. now apply Realise. now apply Terminates.
    - intros tin yout tout H HEnc. cbn in *.
      specialize (HEnc Fin0). simpl_vector in *; cbn in *. modpon H. tspec_solve.
    - intros tin k HEnc Hk. cbn in *.
      specialize (HEnc Fin0). simpl_vector in *; cbn in *. do 2 eexists. 2:assumption. contains_ext.
  Qed.

End Fix.  
End Cons_constant.

Ltac hstep_Cons_constant :=
  match goal with
  | [ |- TripleT ?P ?k (Cons_constant.M _) ?Q ] => eapply Cons_constant.SpecT
  end.

Smpl Add hstep_Cons_constant : hstep_Spec.
