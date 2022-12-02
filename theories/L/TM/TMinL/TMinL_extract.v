From Undecidability.L.Datatypes Require Import LNat Lists LProd LFinType LVector .
From Undecidability.L Require Import Functions.FinTypeLookup Functions.EqBool.

From Undecidability.L Require Import TM.TapeFuns TM.TMEncoding.

From Undecidability.TM Require Import TM_facts.

Local Notation L := TM.Lmove.
Local Notation R := TM.Rmove.
Local Notation N := TM.Nmove.

Section loopM.
  Context (sig : finType).
  Let reg_sig := @encodable_finType sig.
  Existing Instance reg_sig.
  
  Let eqb_sig := eqbFinType_inst (X:=sig).
  Existing Instance eqb_sig.
  Variable n : nat.
  Variable M : TM sig n.

  Let reg_state := @encodable_finType (state M).
  Existing Instance reg_state.

  Let eqb_state := eqbFinType_inst (X:=state M).
  Existing Instance eqb_state.
  Import Vector.
  
  (* *** Computability of transition relation *)
  #[export] Instance term_trans : computable (trans (m:=M)).
  Proof.
    pose (t:= (funTable (trans (m:=M)))).
    apply computableExt with (x:= (fun c => lookup c t (start M,Vector.const (None , N) _ ) )).
    2:{ remember t as lock__t .
         extract. }
    
    cbn -[t] ;intro. subst t.  setoid_rewrite lookup_funTable. reflexivity.
  Qed.

  Definition step' (c :  mconfig sig (state M) n) : mconfig sig (state M) n :=
    let (news, actions) := trans (cstate c, current_chars (ctapes c)) in
    mk_mconfig news (doAct_multi (ctapes c) actions).

  #[export] Instance term_doAct_multi: computable (doAct_multi (n:=n) (sig:=sig)).
  Proof.
    extract.
  Qed.


  #[export] Instance term_step' : computable (step (M:=M)).
  Proof.
    extract.
  Qed.

  #[export] Instance term_halt : computable (halt (m:=M)).
  Proof.
    pose (t:= (funTable (halt (m:=M)))).
    apply computableExt with (x:= fun c => lookup c t false).
    2:{ extract. }
    cbn;intro. subst t. setoid_rewrite lookup_funTable. reflexivity.
  Qed.

  #[export] Instance term_haltConf : computable (haltConf (M:=M)).
  Proof.
    extract.
  Qed.

  (* *** Computability of step-ndexed interpreter *)
  #[export] Instance term_loopM :
    computable (loopM (M:=M)).
  Proof.
    unfold loopM. (* as loop is already an encodable instance, this here is a bit out of the scope. Therefore, we unfold manually here. *)
    extract. 
  Qed.

  Instance term_test cfg :
    computable (fun k => LOptions.isSome (loopM (M := M) cfg k)).
  Proof.
    extract.
  Qed.

End loopM.
