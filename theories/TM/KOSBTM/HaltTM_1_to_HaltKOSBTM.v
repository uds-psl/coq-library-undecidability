From Undecidability Require TM.TM TM.KOSBTM.KOSBTM.
Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypes Undecidability.Shared.Libs.PSL.Vectors.Vectors.
Require Undecidability.TM.Util.TM_facts.
Import VectorNotations2.
Local Open Scope vector.

Section red.

    Variable M : TM.TM (finType_CS bool) 1.

    Definition num_states := (projT1 (finite_n (TM.state M))).
    Definition f := (projT1 (projT2 (finite_n (TM.state M)))).
    Definition g := (proj1_sig (projT2 (projT2 (finite_n (TM.state M))))).
    Definition Hf := (proj1 (proj2_sig (projT2 (projT2 (finite_n (TM.state M)))))).
    Definition Hg := (proj2 (proj2_sig (projT2 (projT2 (finite_n (TM.state M)))))).
    
    Definition conv_move : TM.move -> KOSBTM.move :=
        fun m => match m with TM.Lmove => KOSBTM.Lmove | TM.Nmove => KOSBTM.Nmove | TM.Rmove => KOSBTM.Rmove end.

    Definition conv_state : TM.state M -> Fin.t (S num_states) := fun q => (Fin.FS (f q)).
  
    Definition trans : Fin.t (S num_states) * option bool -> option (Fin.t (S num_states) * option bool * KOSBTM.move) :=
        fun '(q, o) => Fin.caseS' q (fun _ => _) (Some (conv_state (TM.start M), None, KOSBTM.Nmove)) 
           (fun q => if TM.halt (g q) then None
                                      else let '(q', vec) := TM.trans M (g q, [| o |]) in
                                           let '(w, m) := Vector.hd vec in
                                           Some (conv_state q', w, conv_move m)
           ).

    Definition conv_tape (t : Vector.t (TM.tape bool) 1) : KOSBTM.tape := 
    let t := Vector.hd t in
    match TM.current t with
    | Some c => (TM.Util.TM_facts.left t, Some c, TM.Util.TM_facts.right t)
    | None => (TM.Util.TM_facts.left t, None, TM.Util.TM_facts.right t)
    end.

    Lemma current_red t : KOSBTM.curr (conv_tape [| t |]) = TM.current t.
    Proof.
      destruct t; reflexivity.
    Qed.

    Lemma wr_red w t : KOSBTM.wr w (conv_tape [| t |]) = conv_tape [| TM.wr w t |].
    Proof.
      unfold conv_tape. cbn.
      destruct t, w; reflexivity.
    Qed.

    Lemma mv_red m t : KOSBTM.mv (conv_move m) (conv_tape [| t |]) = conv_tape [| TM.mv m t |].
    Proof.
      unfold conv_tape. cbn.
      destruct t, m; try reflexivity.
      all: destruct l, l0; reflexivity.
    Qed.

    Lemma red_correct1 q q' t t' :
      TM.eval M q t q' t' -> KOSBTM.eval (KOSBTM.Build_KOSBTM num_states trans) (conv_state q) (conv_tape t) (conv_state q') (conv_tape t').
    Proof.
      induction 1.
        + eapply KOSBTM.eval_halt. cbn. now rewrite Hg, H.
        + TM_facts.destruct_tapes. cbn in *.
          rewrite <- current_red in H0.
          destruct TM.trans eqn:E. inv H0. destruct h0 as (w, m).
          eapply KOSBTM.eval_step with (q' := conv_state q') (w := w) (m := conv_move m). cbn. rewrite Hg, H, E.
          reflexivity.
          now rewrite wr_red, mv_red.
    Qed.

    Lemma red_correct2 q t q'_ t'_ :
      KOSBTM.eval (KOSBTM.Build_KOSBTM num_states trans) (conv_state q) (conv_tape t) q'_ t'_ ->
      exists q' t', q'_ = conv_state q' /\ t'_ = conv_tape t' /\
      TM.eval M q t q' t'.
    Proof.
      intros H.
        remember (conv_state q) as q_.
        remember (conv_tape t) as t_.
        induction H in q, t, Heqq_, Heqt_ |- *; subst.
        + exists q, t. repeat split. econstructor.
          unfold KOSBTM.trans, trans in H.
          revert H.
          generalize (eq_refl (conv_state q)).
            pattern (conv_state q) at 1 3.
            eapply Fin.caseS'; cbn.
            -- intros ? [=].
            -- intros ? ? ?. destruct TM.halt eqn:E.
               ++ unfold conv_state in H.
                  eapply Fin.FS_inj in H as ->. now rewrite Hg in E.
               ++ now destruct TM.trans, Vector.hd.
        + unfold KOSBTM.trans, trans in H. revert H.
          generalize (eq_refl (conv_state q)).
          pattern (conv_state q) at 1 3.
          eapply Fin.caseS'; cbn.
          * intros ? [=]. unfold conv_state in *. inv H.
          * intros ? ?. unfold conv_state in *. eapply Fin.FS_inj in H; subst.
            rewrite Hg.
            destruct TM.halt eqn:E.
            -- intros [=].
            -- TM_facts.destruct_tapes.
               destruct TM.trans eqn:Et.
               destruct (Vector.hd _) eqn:E't.
               intros [=]; subst.
               rewrite current_red in Et.
               cbn. edestruct IHeval as (q''' & t''' & ? & ? & ?).
               ++ reflexivity.
               ++ rewrite wr_red, mv_red. reflexivity.
               ++ destruct_vector. cbn in *. subst. repeat esplit; [eassumption..|]. econstructor; eassumption.
    Qed.

End red.

Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts.
Require Undecidability.TM.Reductions.Arbitrary_to_Binary.
Require Fin.

Lemma KOSBTM_simulation (M : TM.TM (finType_CS bool) 1) :
  {M' : KOSBTM.KOSBTM |
        (forall q t t', TM.eval M (TM.start M) t q t' -> exists q', KOSBTM.eval M' Fin.F1 (conv_tape t) q' (conv_tape t')) /\
        (forall t, (exists q' t', KOSBTM.eval M' Fin.F1 (conv_tape t) q' t') -> (exists q' t', TM.eval M (TM.start M) t q' t'))}.
Proof.
  exists (KOSBTM.Build_KOSBTM (num_states M) (@trans M)). split.
  - intros q t t' H % red_correct1. eexists. econstructor. cbn. reflexivity. eapply H.
  - intros t (q' & t' & H).  inversion H; subst; clear H. cbn in H0. inv H0. cbn in *. inv H0.
    eapply red_correct2 in H1 as (? & ? & -> & -> & H). eexists. eexists. eauto.
Qed.

Theorem reduction :
  TM.HaltTM 1 ⪯ KOSBTM.HaltKOSBTM.
Proof.
  eapply reduces_transitive. eapply Arbitrary_to_Binary.reduction.
  unshelve eexists. { intros [M t]. refine (_, conv_tape t). refine (KOSBTM.Build_KOSBTM (num_states M) (@trans M)). }
  intros [M t]. split.
  - intros [q' [t' H]]. eapply red_correct1 in H.
    exists (conv_state q'), (conv_tape t'). econstructor. cbn. reflexivity. eapply H.
  - intros [q' [t' H]]. inversion H; subst; clear H. cbn in H0. inv H0. cbn in *. inv H0.
    eapply red_correct2 in H1 as (? & ? & -> & -> & H). eexists. eexists. eauto.
Qed.

