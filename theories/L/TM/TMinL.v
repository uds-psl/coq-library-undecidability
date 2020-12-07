From Undecidability.L.Datatypes Require Import LOptions.
From Undecidability.L Require Import Computability.MuRec.

From Undecidability.TM Require Import TM_facts.

Require Import Undecidability.L.TM.TMinL.TMinL_extract.

Set Default Proof Using "Type".

Definition Halt' (Sigma : finType) n (M: TM Sigma n) (start: mconfig Sigma (state M) n) :=
  exists (f: mconfig _ (state M) _), halt (cstate f)=true /\ exists k, loopM start k = Some f.

Definition Halt :{ '(Sigma, n) : finType * nat & TM Sigma n & tapes Sigma n} -> _ :=
  fun '(existT2 (Sigma, n) M tp) =>
    exists (f: mconfig _ (state M) _), halt (cstate f) = true
                                   /\ exists k, loopM (mk_mconfig (start M) tp) k = Some f.

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
