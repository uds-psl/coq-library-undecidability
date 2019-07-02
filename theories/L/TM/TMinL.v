From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LNat Lists LProd LFinType LVector.
From Undecidability.L Require Import Computability.MuRec Functions.FinTypeLookup.
From Undecidability.L Require Export TM.TMEncoding.
From Undecidability.L Require Import TM.TapeFuns.


From Undecidability Require Import TM.TM.

Definition Halt' Sigma n (M: mTM Sigma n) (start: mconfig Sigma (states M) n) :=
  exists (f: mconfig _ (states M) _), halt (cstate f)=true /\ exists k, loopM start k = Some f.

Definition Halt :{ '(Sigma, n) : _ & mTM Sigma n & tapes Sigma n} -> _ :=
  fun '(existT2 _ _ (Sigma, n) M tp) =>
    exists (f: mconfig _ (states M) _), halt (cstate f) = true
                                   /\ exists k, loopM (mk_mconfig (start M) tp) k = Some f.

Fixpoint loopTime {X} `{registered X} f (fT: timeComplexity (X -> X)) (p: X -> bool) (pT : timeComplexity (X -> bool)) (a:X) k :=
  fst (pT a tt) +
  match k with
    0 => 7
  |  S k =>
     fst (fT a tt) + 13 + loopTime f fT p pT (f a) k
  end.

Instance term_loop A `{registered A} :
  computableTime' (@loop A)
                 (fun f fT => (1,fun p pT => (1,fun a _ => (5,fun k _ =>(loopTime f fT p pT a k,tt))))).
Proof.
  extract.
  solverec.
Qed.

Section loopM.
  Context (sig : finType).
  Let reg_sig := @registered_finType sig.
  Existing Instance reg_sig.
  Variable n : nat.
  Variable M : mTM sig n.

  Let reg_states := @registered_finType (states M).
  Existing Instance reg_states.

  Definition transTime := (length (elem (states M) )*17 + n * 17 * (length ( elem sig )+ 4) + 71) * length (funTable (trans (m:=M))) + 16.

  (** *** Computability of transition relation *)
  Instance term_trans : computableTime' (trans (m:=M)) (fun _ _ => (transTime,tt)).
  Proof.
    pose (t:= (funTable (trans (m:=M)))).
    apply computableTimeExt with (x:= fun c => lookup (prod_eqb finType_eqb (Vector.eqb (LOptions.option_eqb finType_eqb))) c t (start M,Vector.const (None,N) _)).
    2:{extract.
       cbn [fst snd]. intuition ring_simplify.


       rewrite lookupTime_leq with (k:=(17* length (elem (states M)) + 17 * n * (length (elem sig) + 4) + 52)).
       -unfold transTime.

        repeat match goal with
                 |- context C[length _] =>let G:= context C [length t] in progress change G
               end.
        ring_simplify.  omega.
       -intros y. unfold callTime2.
        cbn [fst snd]. ring_simplify.
        setoid_rewrite index_leq at 1 2. rewrite Nat.min_id.
        rewrite list_eqbTime_leq with (k:= | elem sig| * 17 + 29).
        +rewrite to_list_length. ring_simplify. omega.
        +intros [] [];unfold callTime2;cbn [fst snd].
         setoid_rewrite index_leq at 1 2. rewrite Nat.min_id.
         all:ring_simplify. all:omega.
    }
    cbn -[t] ;intro. subst t.  setoid_rewrite lookup_funTable. reflexivity.
    apply prod_eqb_spec. apply finType_eqb_reflect. apply vector_eqb_spec,LOptions.option_eqb_spec,finType_eqb_reflect.
  Qed.

  Instance term_current: computableTime' ((current (sig:=sig))) (fun _ _ => (10,tt)).
  Proof.
    extract.
    solverec.
  Qed.

  Instance term_current_chars: computableTime' (current_chars (sig:=sig) (n:=n))  (fun _ _ => (n * 22 +12,tt)).
  Proof.
    extract.
    solverec.
    rewrite map_time_const,to_list_length.  omega.
  Qed.

  Definition step' (c :  mconfig sig (states M) n) : mconfig sig (states M) n :=
    let (news, actions) := trans (cstate c, current_chars (ctapes c)) in
    mk_mconfig news (doAct_multi (ctapes c) actions).


  Instance term_doAct: computableTime' (doAct (sig:=sig)) (fun _ _ => (1,fun _ _ => (89,tt))).
  Proof.
    extract.
    solverec.
  Qed.

  Instance term_doAct_multi: computableTime' (doAct_multi (n:=n) (sig:=sig)) (fun _ _ => (1,fun _ _ =>(n * 108 + 19,tt))).
  Proof.
    extract.
    solverec.
    rewrite time_map2_leq with (k:=90).
    2:now solverec.
    solverec. now rewrite to_list_length.
  Qed.


  Instance term_step' : computableTime' (step (M:=M)) (fun _ _ => (n* 130+ transTime + 64,tt)).
  Proof.
    extract.
    solverec.
  Qed.

  Definition haltTime := length (funTable (halt (m:=M))) * (length (elem (states M)) * 17 + 37) + 12.

  Instance term_halt : computableTime' (halt (m:=M)) (fun _ _ => (haltTime,tt)).
  Proof.
    pose (t:= (funTable (halt (m:=M)))).
    apply computableTimeExt with (x:= fun c => lookup finType_eqb c t false).
    2:{extract.
       solverec.
       rewrite lookupTime_leq with (k:=17 * (| elem (states M) |) + 18).
       2:{
         intros. cbn [callTime2 fst].
         repeat rewrite index_leq. rewrite Nat.min_id. omega.
       }
       unfold haltTime. subst t.
       ring_simplify. reflexivity.
    }
    cbn;intro. subst t. setoid_rewrite lookup_funTable. reflexivity.
    apply finType_eqb_reflect.
  Qed.

  Instance term_haltConf : computableTime' (haltConf (M:=M)) (fun _ _ => (haltTime+8,tt)).
  Proof.
    extract.
    solverec.
  Qed.

  (** *** Computability of step-ndexed interpreter *)
  Global Instance term_loopM :
    let c1 := (haltTime + n*130 + transTime + 85) in
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

  Lemma Halt_red cfg :
    Halt' cfg <-> converges (mu (ext ((fun k => LOptions.isSome (loopM (M := M) cfg k))))).
  Proof.
    split; intros.
    - destruct H as (f & ? & k & ?).
      edestruct (mu_complete).
      + eapply term_test.
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
