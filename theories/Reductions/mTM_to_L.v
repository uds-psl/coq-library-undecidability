From Undecidability.Problems Require Import TM Reduction.
Require Import Undecidability.L.TM.TMEncoding.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LNat Lists LProd LBool.
From Undecidability.L.Computability Require Import MuRec.

From Undecidability Require Import TM.TM.
Require Import PslBase.FiniteTypes.FinTypes.

Lemma TM_to_L :
  HaltMTM ⪯ HaltL.
Proof.
  unshelve eexists.
  - intros [[n sig] M t].
    exact ((mu
     (@ext (nat -> bool) (! nat ~> ! bool)
        (fun k : nat => @LOptions.isSome (mconfig sig (@state sig n M) n) (@loopM sig n M (initc M t) k))
        (@term_test sig n M (initc M t))))).
  - intros [[n sig] M t].
    unfold HaltL.
    intuition.
    + destruct H as [cfg [k ]].
      edestruct Halt_red as [? _].
      edestruct H0.
      2:{ destruct H1. exists x. split. 2:eauto.
          eapply equiv_lambda; eauto. }
      exists cfg. split.
      * unfold loopM in H. eapply loop_fulfills in H.
        eassumption.
      * eauto.
    + destruct H as [v H].
      edestruct Halt_red as [_ ?].
      edestruct H0.
      destruct H. exists v; split; eauto.
      destruct H1, H2.
      now repeat eexists. 
Qed.
