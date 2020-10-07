From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LNat Lists LProd LFinType LVector LOptions.
From Undecidability.L Require Import Computability.MuRec Functions.FinTypeLookup Functions.EqBool.
From Undecidability.L Require Export TM.TMEncoding.
From Undecidability.L Require Import TM.TapeFuns.


From Undecidability Require Import TM.Util.TM_facts.

Local Notation L := TM.Lmove.
Local Notation R := TM.Rmove.
Local Notation N := TM.Nmove.

Definition Halt' (Sigma : finType) n (M: TM Sigma n) (start: mconfig Sigma (state M) n) :=
  exists (f: mconfig _ (state M) _), halt (cstate f)=true /\ exists k, loopM start k = Some f.

Definition Halt :{ '(Sigma, n) : finType * nat & TM Sigma n & tapes Sigma n} -> _ :=
  fun '(existT2 (Sigma, n) M tp) =>
    exists (f: mconfig _ (state M) _), halt (cstate f) = true
                                   /\ exists k, loopM (mk_mconfig (start M) tp) k = Some f.

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

  Local Definition c__trans :=
       (length ( elem (state M) ) * 4 + (n * (4 * length ( elem sig ) + 10) + 4) + 4) *
       c__eqbComp (finType_CS (state M * VectorDef.t (option sig) n)).
  Definition transTime := (| funTable (trans (m:=M)) |) * (c__trans + 24) + 4 + 9.
  (** *** Computability of transition relation *)
  Global Instance term_trans : computableTime' (trans (m:=M)) (fun _ _ => (transTime,tt)).
  Proof.
    pose (t:= (funTable (trans (m:=M)))).
    apply computableTimeExt with (x:= (fun c => lookup c t (start M,Vector.const (None , N) _ ) )).
    2:{ remember t as lock__t .
        Import Vector. extract. solverec. subst lock__t .
        rewrite lookupTime_leq.
                                        setoid_rewrite size_prod;cbn [fst snd].
         unfold reg_state;rewrite (size_finType_le a).
         
         rewrite enc_vector_eq. evar (c__elem' : nat).
         evar (c__elem : nat). 
         rewrite size_list,sumn_le_bound with (c:=c__elem).
         2:{
           intros ? (?&<-&?)%in_map_iff.
           rewrite LOptions.size_option.
           [c__elem]: exact( c__elem' + 10). subst c__elem.
           destruct x. 2: { unfold c__listsizeCons. lia. } 
           unfold reg_sig;rewrite (size_finType_le e).
           ring_simplify.
           [c__elem']: exact (4 * (| elem sig |)). subst c__elem'. unfold c__listsizeCons. lia.
         }
         rewrite map_length,to_list_length.
         unfold c__elem',transTime,c__trans,t,c__elem. reflexivity.
    }
    
    cbn -[t] ;intro. subst t.  setoid_rewrite lookup_funTable. reflexivity.
  Qed.

  Definition step' (c :  mconfig sig (state M) n) : mconfig sig (state M) n :=
    let (news, actions) := trans (cstate c, current_chars (ctapes c)) in
    mk_mconfig news (doAct_multi (ctapes c) actions).

  Global Instance term_doAct_multi: computableTime' (doAct_multi (n:=n) (sig:=sig)) (fun _ _ => (1,fun _ _ =>(n * 108 + 123,tt))).
  Proof.
    extract.
    solverec.
    rewrite time_map2_leq with (k:=90).
    2:now solverec.
    solverec. now rewrite to_list_length.
  Qed.


  Global Instance term_step' : computableTime' (step (M:=M)) (fun _ _ => (n* 130+ transTime + 172,tt)).
  Proof.
    extract.
    solverec.
  Qed.

  Local Definition cHalt := ((| elem (state M) |) * 4 * c__eqbComp (state M) + 24).

  Definition haltTime := length (funTable (halt (m:=M))) * cHalt + 12.

  Global Instance term_halt : computableTime' (halt (m:=M)) (fun _ _ => (haltTime,tt)).
  Proof.
    pose (t:= (funTable (halt (m:=M)))).
    apply computableTimeExt with (x:= fun c => lookup c t false).
    2:{extract.
       solverec.
       rewrite lookupTime_leq.
       unfold reg_state at 1;rewrite size_finType_le.
       unfold haltTime. subst t. unfold cHalt. nia.
    }
    cbn;intro. subst t. setoid_rewrite lookup_funTable. reflexivity.
  Qed.

  Global Instance term_haltConf : computableTime' (haltConf (M:=M)) (fun _ _ => (haltTime+8,tt)).
  Proof.
    extract.
    solverec.
  Qed.

  (** *** Computability of step-ndexed interpreter *)
  Global Instance term_loopM :
  let c1 := (haltTime + n*130 + transTime + 85 + 108) in
    let c2 := 15 + haltTime in
    computableTime' (loopM (M:=M)) (fun _ _ => (5,fun k _ => (c1 * k + c2,tt))).
  Proof.
    unfold loopM. (* as loop is already an registered instance, this here is a bit out of the scope. Therefore, we unfold manually here. *)
    extract.
    solverec. 
  Qed.

  Instance term_test cfg :
    computable (fun k => LOptions.isSome (loopM (M := M) cfg k)).
  Proof.
    extract.
  Qed.


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
      + intros. eexists. now Lsimpl.
      + eassumption.
      + eauto.
      + subst.
        assert ((ext (fun k : nat => LOptions.isSome (loopM cfg k))) (ext k) ==
                ext (LOptions.isSome (loopM cfg k))) by Lsimpl.
        rewrite H1 in H2. clear H1.
        eapply unique_normal_forms in H2; try Lproc. eapply inj_enc in H2.
        destruct (loopM cfg k) eqn:E.
        * exists m. split. 2: eauto.
          unfold loopM in E. now eapply loop_fulfills in E.
        * inv H2.
  Qed.

End loopM.
