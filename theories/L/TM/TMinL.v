From Undecidability.L.Datatypes Require Import LOptions.
From Undecidability.L Require Import Computability.MuRec.

From Undecidability.TM Require Import TM_facts.

From Undecidability.L.Datatypes Require LBool LNat LProd LFinType LVector List.List_basics.
From Undecidability.L.Functions Require FinTypeLookup.
From Undecidability.L.TM Require TapeFuns.

Module TMinL_extract.
Import TapeFuns FinTypeLookup LBool List.List_basics LProd LFinType.

Local Notation L := TM.Lmove.
Local Notation R := TM.Rmove.
Local Notation N := TM.Nmove.

Section loopM.
  Context (sig : finType).
  Let reg_sig := @registered_finType sig.
  Existing Instance reg_sig.
  
  Let eqb_sig := eqbFinType_inst (X:=sig).
  Existing Instance eqb_sig.
  Variable n : nat.
  Variable M : TM sig n.

  Let reg_state := @registered_finType (state M).
  Existing Instance reg_state.

  Let eqb_state := eqbFinType_inst (X:=state M).
  Existing Instance eqb_state.
  Import Vector.

  (* *** Computability of transition relation *)
  Global Instance term_trans : computable (trans (m:=M)).
  Proof.
    pose (t:= (funTable (trans (m:=M)))).
    apply computableExt with (x:= (fun c => lookup c t (start M,Vector.const (None , N) _ ) )).
    2:{ extract. }
    cbn -[t] ;intro. subst t. setoid_rewrite lookup_funTable. reflexivity.
  Qed.

  Definition step' (c :  mconfig sig (state M) n) : mconfig sig (state M) n :=
    let (news, actions) := trans (cstate c, current_chars (ctapes c)) in
    mk_mconfig news (doAct_multi (ctapes c) actions).

  Global Instance term_doAct_multi: computable (doAct_multi (n:=n) (sig:=sig)).
  Proof.
    extract.
  Qed.

  Global Instance term_step' : computable (TM_facts.step (M:=M)).
  Proof.
    extract.
  Qed.

  Global Instance term_halt : computable (halt (m:=M)).
  Proof.
    pose (t:= (funTable (halt (m:=M)))).
    apply computableExt with (x:= fun c => lookup c t false).
    2:{ extract. }
    cbn;intro. subst t. setoid_rewrite lookup_funTable. reflexivity.
  Qed.

  Global Instance term_haltConf : computable (haltConf (M:=M)).
  Proof.
    extract.
  Qed.

  (* *** Computability of step-ndexed interpreter *)
  Global Instance term_loopM :
    computable (loopM (M:=M)).
  Proof.
    unfold loopM. (* as loop is already an registered instance, this here is a bit out of the scope. Therefore, we unfold manually here. *)
    extract.
  Qed.

  Instance term_test cfg :
    computable (fun k => LOptions.isSome (loopM (M := M) cfg k)).
  Proof.
    extract.
  Qed.

End loopM.
End TMinL_extract.

Definition Halt' (Sigma : finType) n (M: TM Sigma n) (start: mconfig Sigma (state M) n) :=
  exists (f: mconfig _ (state M) _), halt (cstate f)=true /\ exists k, loopM start k = Some f.

Section loopM.
  Context (sig : finType) (n : nat) (M : TM sig n).

  Definition term_test := TMinL_extract.term_test.
  Existing Instance term_test.

  Import L_Notations.
  Lemma Halt_red cfg :
    Halt' cfg <-> converges (mu (ext ((fun k => LOptions.isSome (loopM (M := M) cfg k))))).
  Proof.
    split; intros.
    - destruct H as (f & ? & k & ?).
      edestruct (mu_complete) with (P:= ext (fun k0 : nat => isSome (loopM cfg k0))) (n:=k).
      + Lproc.
      + intros. eexists. rewrite !ext_is_enc. now Lsimpl.
      + Lsimpl. now rewrite H0.
      + exists (ext x). split. eauto. Lproc.
    - destruct H as (v & ? & ?). edestruct mu_sound as (k & ? & ? & _).
      + eapply term_test.
      + intros. eexists. now Lsimpl_old.
      + eassumption.
      + eauto.
      + subst.
        assert ((ext (fun k : nat => LOptions.isSome (loopM cfg k))) (ext k) ==
                ext (LOptions.isSome (loopM cfg k))) by now Lsimpl.
        rewrite H1 in H2. clear H1.
        eapply unique_normal_forms in H2; try Lproc. eapply inj_enc in H2.
        destruct (loopM cfg k) eqn:E.
        * exists m. split. 2: eauto.
          unfold loopM in E. now eapply loop_fulfills in E.
        * inv H2.
  Qed.

End loopM.
