(*
Require Export LNat LOptions LTactics.

Section PartialFunctions.

Variable F : term.
Hypothesis proc_F : proc F.

Variable X : Type.
Variable in_enc : X -> term.

Variable Y : Type.
Variable out_enc : Y -> term.

Hypothesis in_enc_proc : forall x, proc (in_enc x).
Hypothesis out_enc_proc : forall x, proc (out_enc x).

Hint Resolve in_enc_proc out_enc_proc: LProc.

Hypothesis total_F : forall t n, (exists v, F (enc n) (in_enc t) == oenc out_enc (Some v)) \/ F (enc n) (in_enc t) == (none out_enc).

Definition S' := rho (.\"S'", "n", "F", "t"; ("F" "n" "t")
                                               !K
                                               ((.\"Sn","x"; "S'" "Sn" "F" "x") (!Succ "n")) "t").

Lemma S'_proc : recProc S'.
Proof.
  cLproc.
Qed.

Hint Resolve S'_proc : LProc.

Hint Unfold S' : cbv.
(*
Lemma S'_rec n t : S' (enc n) F (tenc t) ==  (F (enc n) (tenc t)) K (lam ( S' (Succ (enc n)) F (tenc t))) I.
Proof.
  Lsimpl.
Qed.*)


Hypothesis mono_F : forall n t v, F (enc n) (in_enc t) == oenc out_enc (Some v) -> F (enc (S n)) (in_enc t) == oenc out_enc (Some v).

Lemma S'_n_Sn n t : S' (enc n) F (in_enc t)  == S' (enc (S n)) F (in_enc t).
Proof.
  repeat recStep S'. destruct (@total_F t n) as [[v Hv] | H].
  -assert (H := mono_F Hv). Lsimpl. 
  -Lsimpl. rewrite none_correct with (enc:=in_enc). Lsimpl. recStep S'. Lsimpl. 
Qed.

Lemma S'_n_Sn_none n t : F (enc n) (in_enc t) == oenc out_enc None ->( lam (S' (enc n) F 0)) (in_enc t)  >* (lam (S' (enc (S n)) F 0) )(in_enc t).
Proof.
  intros R. wLsimpl. subst. recStep S'. wLsimpl. subst.  apply star_step_app_proper;[|reflexivity]. apply equiv_lambda. Lsimpl.
Qed.

Definition Se F :term := .\"x"; !(S' (enc 0)) !F "x".

Lemma Se_proc : proc (Se F).
Proof.
  unfold Se;simpl. wLproc.
Qed.

Hint Resolve Se_proc : LProc.

Lemma S'_0_n n t : Se F (in_enc t) == S' (enc n) F (in_enc t).
Proof.
  unfold Se;simpl. Lsimpl. induction n. 
  -Lsimpl.
  -Lsimpl. apply S'_n_Sn.
Qed.

Lemma Se_converges t v : Se F (in_enc t) == lam v -> closed (lam v).
Proof.
  intros eq. apply equiv_lambda' in eq;[|Lproc]. apply closed_star in eq;Lproc.
Qed.

Lemma Se_correct' t (v : term) : proc v ->
                                    ( Se F (in_enc t) == v <-> exists n, F (enc n) (in_enc t) == some v ).
Proof.
  intros proc_v; split...
  - unfold Se;simpl; generalize 0 at 1; intros n H.
    eapply equiv_lambda' in H;Lproc... assert (R:=H). rewrite star_pow in H. destruct H as [k H].
    revert n R H.
    eapply complete_induction with (x := k). clear k.
    intros k IHn n R H.
    destruct (total_F t n) as [[v' H'] | HH]...
    + assert (out_enc v' = v). {
        apply unique_normal_forms;Lproc. rewrite <- R. Lsimpl. recStep S'. Lsimpl.
      }
      subst.
      exists n. Lsimpl.
    + assert (R':= S'_n_Sn_none HH).
      apply star_pow in R' as [k' R']. destruct k'.
      *inversion R'. apply enc_injective in H1. lia.
      *destruct proc_v as [? [? ?]]. subst v. destruct (pow_trans_lam H R') as [k'' [le R'']].
       assert (R1 : (λ ((S' (enc (S n))) F) 0) (in_enc t) >* (λ x)) by (rewrite star_pow; eauto).
       specialize (IHn _ le _ R1 R''). auto.
  - intros [m Hm]. rewrite S'_0_n with (n := m). recStep S'. Lsimpl. unfold some. simpl. Lsimpl.
Qed.

(* TODO *)

Ltac standardizeHypo _n:=
match goal with
  | eq : ?s == ?t |- _=>
    revert eq;try standardizeHypo _n; intros eq;
    try (progress (let R:= fresh "R" in
                   standardize R _n s;apply (stHypo R) in eq;clear R ));
      try (progress (let R':= fresh "R'" in
                     symmetry;standardize R' _n s;
                     apply (stHypo R') in eq;symmetry;clear R' ))
end.

Corollary Se_correct t (v : term) : lambda v -> (Se F (in_enc t) == v <-> exists n, F (enc n) (in_enc t) == some v).
Proof.
  intros lam_v; split.
  - intros. destruct lam_v; subst.
    eapply Se_correct' in H. firstorder.
    eapply Se_converges in H. split;auto.
  - intros [n H].
    assert (closed v).
    { destruct (total_F t n) as [[v' Hv'] | Hv'].
      + rewrite H in Hv'. Lsimpl. cbv in Hv'. inv lam_v.
        
        clear H. revert Hv'. try standardizeHypo 10. intros Hv'. rewrite !(eqStep (stepApp _ _)) in Hv'. cbv in Hv'. apply unique_normal_forms in Hv';[|Lproc..]. rewrite oenc_def_eq in Hv'. injection Hv'. intros;subst. rewrite H. Lproc.
      + rewrite H in Hv'. symmetry in Hv'. cbv in Hv'. inv lam_v. rewrite (eqStep (stepApp _ _)) in Hv'. simpl in Hv'. apply unique_normal_forms in Hv';[|Lproc..]. discriminate Hv'. 
    }
    rewrite Se_correct';[|Lproc].
    eauto.
Qed.

End PartialFunctions.


Hint Resolve S'_proc : LProc.

Hint Resolve Se_proc : LProc.
*)
