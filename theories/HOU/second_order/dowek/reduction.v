Set Implicit Arguments.
Require Import List Omega Lia.
From Undecidability.HOU Require Import std.std unification.unification calculus.calculus.
Import ListNotations.
From Undecidability.HOU.second_order Require Import diophantine_equations dowek.encoding.

Set Default Proof Using "Type".

(* ** Equivalences *)
Section EquationEquivalences.

  Variable (X: Const) (sigma: fin -> exp X).
  Hypothesis (N: forall x, normal (sigma x)).


  Section Variables.

    Lemma forward_vars x n:
      sigma x = enc n -> sigma • fst (varEQ x) ≡ sigma • snd (varEQ x).
    Proof.
      intros; unfold varEQ, fst, snd.
      cbn. unfold shift, var_zero, funcomp; rewrite H; asimpl.
      rewrite !enc_app.
      change (var 0 (var 1)) with (@AppL X (repeat (var 0) 1) (var 1)).
      now rewrite <-AppL_app, <-repeated_plus, plus_comm.
    Qed.

    Lemma backward_vars x:
      sigma • fst (varEQ x) ≡ sigma • snd (varEQ x) ->  exists n, sigma x = enc n.
    Proof using N.
      intros ?. eapply enc_characteristic; eauto.
      cbn in H. asimpl. asimpl in H.
      unfold shift in *. unfold funcomp at 5 in H.
      asimpl in H. rewrite <-H.
      unfold funcomp at 4. asimpl.
      reflexivity.
    Qed.

  End Variables.

  Section Constants.
    Variable (x n c: nat).
    Hypothesis (EQx: sigma x = enc n).


    Lemma forward_consts:
      n = 1 -> sigma • fst (constEQ x) ≡ sigma • snd (constEQ x).
    Proof using EQx.
      intros; unfold constEQ, fst, snd. subst.
      asimpl; now rewrite EQx.
    Qed.

    Lemma backward_consts:
      sigma • fst (constEQ x) ≡ sigma • snd (constEQ x) -> n = 1.
    Proof using EQx.
      intros EQ; unfold constEQ, fst, snd in EQ.
      asimpl in EQ. rewrite EQx in EQ.
      eapply enc_equiv_injective; eauto.
    Qed.

  End Constants.


  Section Addition.
    Variable (x y z n m p c: nat).
    Hypothesis (EQx: sigma x = enc m) (EQy: sigma y = enc n) (EQz: sigma z = enc p).

    Lemma forward_add:
      m + n = p -> sigma • fst (addEQ x y z) ≡ sigma • snd (addEQ x y z).
    Proof using EQz EQy EQx.
      intros; unfold addEQ, fst, snd; asimpl.
      now rewrite EQx, EQy, EQz, <-enc_add, H.
    Qed.


    Lemma backward_add:
      sigma • fst (addEQ x y z) ≡ sigma • snd (addEQ x y z) -> m + n = p.
    Proof using EQz EQy EQx.
      intros EQ; unfold addEQ, fst, snd in EQ; asimpl in EQ.
      rewrite EQx, EQy, EQz, <-enc_add in EQ.
      eauto using enc_equiv_injective.
    Qed.

  End Addition.


  Section Multiplication.
    Variable (x y z n m p c: nat).
    Hypothesis (EQx: sigma x = enc m) (EQy: sigma y = enc n) (EQz: sigma z = enc p).

    Lemma forward_mult :
      m * n = p -> sigma • fst (mulEQ x y z) ≡ sigma • snd (mulEQ x y z).
    Proof using EQz EQy EQx.
      intros; unfold mulEQ, fst, snd; asimpl.
      now rewrite EQx, EQy, EQz, <-enc_mul, H.
    Qed.


    Lemma backward_mult:
      sigma • fst (mulEQ x y z) ≡ sigma • snd (mulEQ x y z) -> m * n = p.
    Proof using EQz EQy EQx.
      intros EQ; unfold mulEQ, fst, snd in EQ; asimpl in EQ.
      rewrite EQx, EQy, EQz, <-enc_mul in EQ.
      eauto using enc_equiv_injective.
    Qed.

  End Multiplication.
End  EquationEquivalences.



(* ** Forward Direction **)
Section Forward.
  Variable (X: Const) (E: list deq).

  Implicit Types (x y z: nat) (c: nat).

  Definition encs theta: fin -> exp X := theta >> enc.

  Lemma forward_typing theta:
    nil ⊩( 3) encs theta : Gamma__dwk E.
  Proof.
    intros ?? <- % nth_error_In % repeated_in.
    eapply typing_enc.
  Qed.

  Lemma H10_DWK : H10 E -> SOU X 3 (H10_to_DWK X E).
  Proof.
    intros [theta H].
    exists []. exists (encs theta). split.
    now eapply forward_typing.
    intros s t H'; cbn.
    change s with (fst (s, t)); change t with (snd (s, t)) at 2.
    remember (s,t) as q. clear Heqq.
    cbn in *. eapply in_Equations in H' as (e & ? & ?).
    eapply H in H0.
    destruct e; cbn in *; intuition; subst.
    all: try eapply forward_add. all: try eapply forward_consts.
    all: try eapply forward_mult. all: try eapply forward_vars.
    all: unfold encs, funcomp; eauto. try eapply enc_sol_encodes.
    all: inv H0; eauto.
  Qed.


End Forward.


(* ** Backward Direction **)
Section Backward.
  Variable (X: Const).
  Implicit Types (sigma: nat -> exp X) (x y z c n: nat).

  Definition sub_sol sigma x :=
    match dec_enc (sigma x) with
    | inl (exist _ k _) => k
    | inr _ => 0
    end.

  Lemma sub_sol_enc sigma x n:
    sigma x = enc n -> sub_sol sigma x = n.
  Proof.
    intros H; unfold sub_sol; destruct dec_enc as [[m H']|H'].
    rewrite H' in H; eapply enc_injective in H; eauto.
    eapply H' in H; intuition.
  Qed.

  Lemma DWK_H10 E: SOU X 3 (H10_to_DWK X E) -> H10 E.
  Proof.
    rewrite SOU_NSOU; eauto. intros (Delta & tau & T & EQ & N).
    exists (sub_sol tau).
    assert (forall e, e ∈ Eqs E -> tau • fst e ≡ tau • snd e) as H by now intros []; eauto. 
    intros e Hin. destruct e; econstructor.
    all: edestruct (@in_Equations X (varEQ x) E) as [_ EQx]; mp EQx;
      [eexists; intuition eauto; cbn; intuition | eapply H in EQx].
    2, 3: edestruct (@in_Equations X (varEQ y) E) as [_ EQy]; mp EQy;
      [eexists; intuition eauto; cbn; intuition| eapply H in EQy].
    2, 3: edestruct (@in_Equations X (varEQ z) E) as [_ EQz]; mp EQz;
      [eexists; intuition eauto; cbn; intuition| eapply H in EQz].
    all: eapply backward_vars in EQx as [n]; eauto.
    2 - 3: eapply backward_vars in EQy as [m]; eauto.
    2 - 3: eapply backward_vars in EQz as [p]; eauto.
    all: repeat (erewrite sub_sol_enc; [|eauto]).
    - eapply backward_consts; eauto.
      eapply H, in_Equations; eexists; intuition eauto.
      cbn; intuition.
    - eapply backward_add; eauto.
      eapply H, in_Equations; eexists; intuition eauto.
      cbn; intuition.
    - eapply backward_mult; eauto.
      eapply H, in_Equations; eexists; intuition eauto.
      cbn; intuition.
  Qed.
End Backward.



Lemma Dowek X : H10 ⪯ SOU X 3.
Proof.
  exists (H10_to_DWK X). intros E.
  split; eauto using H10_DWK, DWK_H10.
Qed.
