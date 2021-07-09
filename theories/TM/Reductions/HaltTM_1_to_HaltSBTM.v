From Undecidability Require TM.TM TM.SBTM.
Require Import Undecidability.Shared.FinTypeEquiv.
(* Require Import Undecidability.L.Functions.FinTypeLookup. *)
Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypes Undecidability.Shared.Libs.PSL.Vectors.Vectors.
Require Undecidability.TM.Util.TM_facts.
Import VectorNotations2.
Local Open Scope vector.

Notation vector_hd v := (projT1 (destruct_vector_cons v)).  

Section red.

    Variable M : TM.TM (finType_CS bool) 1.

    Definition num_states := (projT1 (finite_n (TM.state M))).
    Definition f := (projT1 (projT2 (finite_n (TM.state M)))).
    Definition g := (proj1_sig (projT2 (projT2 (finite_n (TM.state M))))).
    Definition Hf := (proj1 (proj2_sig (projT2 (projT2 (finite_n (TM.state M)))))).
    Definition Hg := (proj2 (proj2_sig (projT2 (projT2 (finite_n (TM.state M)))))).
    
    Definition conv_move : TM.move -> SBTM.move :=
        fun m => match m with TM.Lmove => SBTM.Lmove | TM.Nmove => SBTM.Nmove | TM.Rmove => SBTM.Rmove end.

    Definition conv_state : TM.state M -> Fin.t (S num_states) := fun q => (Fin.FS (f q)).
  
    Definition trans : Fin.t (S num_states) * option bool -> option (Fin.t (S num_states) * option bool * SBTM.move) :=
        fun '(q, o) => Fin.caseS' q (fun _ => _) (Some (conv_state (TM.start M), None, SBTM.Nmove)) 
           (fun q => if TM.halt (g q) then None
                                      else let '(q', vec) := TM.trans M (g q, [| o |]) in
                                           let '(w, m) := vector_hd vec in
                                           Some (conv_state q', w, conv_move m)
           ).

    Definition conv_tape (t : Vector.t (TM.tape bool) 1) : SBTM.tape := 
    let t := vector_hd t in
    match TM.current t with
    | Some c => (TM.Util.TM_facts.left t, Some c, TM.Util.TM_facts.right t)
    | None => (TM.Util.TM_facts.left t, None, TM.Util.TM_facts.right t)
    end.

    Lemma current_red t : SBTM.curr (conv_tape [| t |]) = TM.current t.
    Proof.
      unfold conv_tape. cbn. destruct (destruct_vector_cons [| t |]) as (? & ? & E); cbn in *. inv E. clear H1.
      unfold TM.current.
      destruct x eqn:E; reflexivity.
    Qed.

    Lemma wr_red w t : SBTM.wr w (conv_tape [| t |]) = conv_tape [| TM.wr w t |].
    Proof.
      unfold conv_tape. cbn.
      destruct (destruct_vector_cons [| t |]) as (? & ? & E); cbn in *. inv E. clear H1.
      destruct (destruct_vector_cons [| _ |]) as (? & ? & E); cbn in *. inv E. clear H1.
      destruct x eqn:E1, w eqn:E2; cbn; reflexivity.
    Qed.

    Lemma mv_red m t : SBTM.mv (conv_move m) (conv_tape [| t |]) = conv_tape [| TM.mv m t |].
    Proof.
      unfold conv_tape. cbn.
      destruct (destruct_vector_cons [| t |]) as (? & ? & E); cbn in *. inv E. clear H1.
      destruct (destruct_vector_cons [| _ |]) as (? & ? & E); cbn in *. inv E. clear H1.
      destruct x eqn:E1, m eqn:E2; cbn; try reflexivity.
      all: destruct l, l0; try reflexivity.
    Qed.

    Lemma red_correct1 q q' t t' :
      TM.eval M q t q' t' -> SBTM.eval (SBTM.Build_SBTM num_states trans) (conv_state q) (conv_tape t) (conv_state q') (conv_tape t').
    Proof.
      induction 1.
        + eapply SBTM.eval_halt. cbn. now rewrite Hg, H.
        + TM_facts.destruct_tapes. cbn in *.
          rewrite <- current_red in H0.
          destruct TM.trans eqn:E. inv H0. destruct h0 as (w, m).
          eapply SBTM.eval_step with (q' := conv_state q') (w := w) (m := conv_move m). cbn. rewrite Hg, H, E.
          destruct destruct_vector_cons as (? & ? & ?), x; cbn. inv e. reflexivity.
          now rewrite wr_red, mv_red.
    Qed.

    Lemma red_correct2 q t q'_ t'_ :
      SBTM.eval (SBTM.Build_SBTM num_states trans) (conv_state q) (conv_tape t) q'_ t'_ ->
      exists q' t', q'_ = conv_state q' /\ t'_ = conv_tape t' /\
      TM.eval M q t q' t'.
    Proof.
      intros H.
        remember (conv_state q) as q_.
        remember (conv_tape t) as t_.
        induction H in q, t, Heqq_, Heqt_ |- *; subst.
        + exists q, t. repeat split. econstructor.
          unfold SBTM.trans, trans in H.
          revert H.
          generalize (eq_refl (conv_state q)).
            pattern (conv_state q) at 1 3.
            eapply Fin.caseS'; cbn.
            -- intros ? [=].
            -- intros ? ? ?. destruct TM.halt eqn:E.
               ++ unfold conv_state in H.
                  eapply Fin.FS_inj in H as ->. now rewrite Hg in E.
               ++ destruct TM.trans, destruct_vector_cons, x; inv H0.
        + unfold SBTM.trans, trans in H. revert H.
          generalize (eq_refl (conv_state q)).
          pattern (conv_state q) at 1 3.
          eapply Fin.caseS'; cbn.
          * intros ? [=]. unfold conv_state in *. inv H.
          * intros ? ?. unfold conv_state in *. eapply Fin.FS_inj in H; subst.
            rewrite Hg.
            destruct TM.halt eqn:E.
            -- intros [=].
            -- TM_facts.destruct_tapes.
               destruct TM.trans eqn:Et, destruct_vector_cons as (? & ? & ?), x; cbn. intros [=]; subst.
               rewrite current_red in Et.
               cbn. edestruct IHeval as (q' & t'_ & -> & -> & H); eauto.
               ++ rewrite wr_red, mv_red. destruct_vector; cbn. reflexivity.
               ++ repeat esplit. cbn in *. econstructor. eauto. eauto. cbn. destruct_vector. eassumption.
    Qed.

End red.

Require Undecidability.TM.TM Undecidability.TM.SBTM.
Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts.
Require Undecidability.TM.Reductions.Arbitrary_to_Binary.

Theorem reduction :
  TM.HaltTM 1 ⪯ SBTM.HaltSBTM.
Proof.
  eapply reduces_transitive. eapply Arbitrary_to_Binary.reduction_tobin.
  unshelve eexists. { intros [M t]. refine (_, conv_tape t). refine (SBTM.Build_SBTM (num_states M) (@trans M)). }
  intros [M t]. split.
  - intros [q' [t' H]]. eapply red_correct1 in H.
    exists (conv_state q'), (conv_tape t'). econstructor. cbn. reflexivity. eapply H.
  - intros [q' [t' H]]. inversion H; subst; clear H. cbn in H0. inv H0. cbn in *. inv H0.
    eapply red_correct2 in H1 as (? & ? & -> & -> & H). eexists. eexists. eauto.
Qed.

