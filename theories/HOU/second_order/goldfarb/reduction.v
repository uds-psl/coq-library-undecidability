Set Implicit Arguments.
Require Import RelationClasses Morphisms Init.Wf List Lia Init.Nat Setoid.
From Undecidability.HOU Require Import calculus.calculus unification.unification.
From Undecidability.HOU.second_order Require Export diophantine_equations goldfarb.encoding goldfarb.multiplication.
Import ListNotations ArsInstances.


(* ** Equivalences *)
Section EquationEquivalences.

  Variable (sigma: fin -> exp ag).
  Hypothesis (N: forall x, normal (sigma x)).


  Section Variables.
    Lemma forward_vars x n: encodes (sigma (F x)) n -> sigma • fst (varEQ x) ≡ sigma • snd (varEQ x).
    Proof.
      intros H. unfold varEQ; cbn; unfold funcomp.
      change shift with (add 1); rewrite ren_plus_combine, !H; cbn; unfold var_zero.
      change (g a (var 1)) with (enc 1 (var 1)); now simplify.
    Qed.

    Lemma backward_vars x: sigma • fst (varEQ x) ≡ sigma • snd (varEQ x) -> exists n, encodes (sigma (F x)) n.
    Proof using N.
      cbn; simplify.
      unfold funcomp; change shift with (add 1); rewrite ren_plus_combine; unfold var_zero; cbn.
      intros H; eapply normal_forms_encodes in H; (eauto 2).
    Qed.

  End Variables.

  Section Constants.
      Variable (n: nat) (x: nat).
      Hypothesis (Ex: encodes (sigma (F x)) n).

      Lemma forward_consts: n = 1 -> sigma • fst (constEQ x) ≡ sigma • snd (constEQ x).
      Proof using Ex.
        cbn; unfold funcomp; change shift with (add 1); rewrite ren_plus_combine; unfold var_zero; cbn.
        rewrite Ex; asimpl; now intros ->.
      Qed.

      Lemma backward_consts:  sigma • fst (constEQ x) ≡ sigma • snd (constEQ x) -> n = 1.
      Proof using Ex.
        cbn.
        unfold funcomp; change shift with (add 1); rewrite ren_plus_combine; unfold var_zero; cbn.
        rewrite Ex. asimpl. intros ? % equiv_lam_elim % equiv_lam_elim.
        eapply enc_injective;[| |eauto]; (eauto 2).
      Qed.

  End Constants.


  Section Addition.
    Variable (m n p: nat) (x y z: nat).
    Hypothesis (Ex: encodes (sigma (F x)) m) (Ey: encodes (sigma (F y)) n) (Ez: encodes (sigma (F z)) p).


    Lemma forward_add: m + n = p -> sigma • fst (addEQ x y z) ≡ sigma • snd (addEQ x y z).
    Proof using Ex Ey Ez.
      intros <-; cbn.
      unfold funcomp; change shift with (add 1); rewrite !ren_plus_combine; unfold var_zero; cbn.
      erewrite Ex, Ey, Ez; now simplify.
    Qed.

    Lemma backward_add:
      sigma • fst (addEQ x y z) ≡ sigma • snd (addEQ x y z) -> m + n = p.
    Proof using Ex Ey Ez.
      cbn.
      unfold funcomp; change shift with (add 1); rewrite !ren_plus_combine; unfold var_zero; cbn.
      rewrite Ex, Ey, Ez; simplify; intros H % equiv_lam_elim % equiv_lam_elim.
      rewrite <-enc_app in H.
      eapply enc_injective;[| |eauto]; (eauto 2).
    Qed.

  End Addition.


  (* *** Multiplication *)
  Section Multiplication.

    Variable (m n p: nat) (x y z: nat).
    Hypothesis
      (Ex: encodes (sigma (F x)) m) (Ey: encodes (sigma (F y)) n) (Ez: encodes (sigma (F z)) p).


    Lemma forward_mul:
        m * n = p -> sigma (G x y z) = T n m -> sigma • fst (mulEQ x y z) ≡ sigma • snd (mulEQ x y z).
    Proof using Ex Ey Ez.
      intros H1 H2. unfold mulEQ; cbn. unfold funcomp.
      rewrite H2. change shift with (add 1); rewrite !ren_plus_combine; cbn [plus].
      rewrite Ex, Ey, Ez. subst p. eapply G_forward.
    Qed.

    Lemma backward_mult:
      sigma • fst (mulEQ x y z) ≡ sigma • snd (mulEQ x y z) -> m * n = p /\ sigma (G x y z) = T n m.
    Proof using N Ex Ey Ez.
      unfold mulEQ; cbn. unfold funcomp.
      change shift with (add 1); rewrite !ren_plus_combine; cbn [plus].
      rewrite Ex, Ey, Ez. intros H. apply G_iff in H; (eauto 2).
    Qed.

  End Multiplication.


End EquationEquivalences.


(* ** Forward Direction **)
Section Forward.


  Variables (E: list deq).

  Definition gf n := lambda enc n (var 0).


  Lemma tab_typing {X} n (f: nat -> exp X) g k Gamma:
    (forall i, Gamma ⊢(n) f i : g i) -> Gamma ⊢₊(n) tab f k : tab g k.
  Proof.
    intros; induction k; cbn; (eauto 2).
    eapply orderlisttyping_app; (eauto 2).
  Qed.

  Lemma gf_typing Gamma n: Gamma ⊢(2) gf n : alpha → alpha.
  Proof.
    econstructor. eapply enc_typing. eauto.
  Qed.

  Lemma GT_typing Gamma m n: Gamma ⊢(2) T n m : alpha → alpha → alpha → alpha.
  Proof.
    do 3 econstructor. eapply lin_typing; [|eauto].
    rewrite repeated_tab. simplify.
    eapply tab_typing.
    intros; econstructor; cbn. econstructor.
    all: eauto using enc_typing.
  Qed.

  Definition enc_sol (sigma: nat -> nat) (x: fin) :=
    match partition_F_G x with
    | inl (exist _ x _) => gf (sigma x)
    | inr (exist _ (x,y,z) _) => T (sigma y) (sigma x)
    end.

  Lemma enc_sol_encodes theta h: encodes (enc_sol theta (F h)) (theta h).
  Proof.
    unfold enc_sol.
    destruct partition_F_G as [[x ?]|[((x,y),z) ?]].
    - eapply F_injective in e as ->.
      intros t delta. unfold gf. cbn; rewrite stepBeta; asimpl; (eauto 2).
    - exfalso; eapply disjoint_F_G; (eauto 2).
  Qed.

  Lemma enc_sol_T theta x y z: (enc_sol theta (G x y z)) = T (theta y) (theta x).
  Proof.
    unfold enc_sol.
    destruct partition_F_G as [[x' ?]|[((x',y'),z') ?]].
    - exfalso; eapply disjoint_F_G; (eauto 2).
    - now eapply G_injective in y0 as (-> & -> & ->).
  Qed.


  Lemma typing_forward sigma:
    (sigma ⊢⁺ₑ E) -> [] ⊩(2) enc_sol sigma : Gamma__deq E.
  Proof.
    eauto; intros ????; unfold enc_sol.
    destruct partition_F_G as [[]|[((x & y) & z) ?]]; subst.
    + eapply nth_Gamma__deq_F in H0 as ->. eapply gf_typing.
    + eapply nth_Gamma__deq_G in H0 as ->. eapply GT_typing.
  Qed.

  Lemma H10_SU: H10 E -> SOU ag 2 (H10_to_SOU  E).
  Proof.
    intros [sigma H].
    exists []. exists (enc_sol sigma).
    split. now eapply typing_forward.
    intros s t; change s with (fst (s,t)) at 2; change t with (snd (s,t)) at 3.
    remember (s,t) as e. clear Heqe s t.
    intros H'; cbn in *. eapply in_Equations in H' as (d & ? & ?).
      destruct d; cbn in *; intuition idtac; subst.
      all: try eapply forward_add. all: try eapply forward_consts.
      all: try eapply forward_mul.
      all: try eapply forward_vars.
      all: try eapply enc_sol_encodes.
      all: eapply H in H0; inv H0; (eauto 2).
      apply enc_sol_T.
    Qed.

End Forward.

(* ** Backward Direction **)
Section Backward.


  Definition decode_subst (sigma: fin -> exp ag) (N: forall x, normal (sigma x)) (x: fin) :=
    match dec_enc (N (F x)) with
    | inl  (exist _ n _) => n
    | inr _ => 0
    end.

  Lemma decode_subst_encodes (sigma: fin -> exp ag) N x n:
    encodes (sigma (F x)) n -> decode_subst sigma N x = n.
  Proof.
    intros H; unfold decode_subst.
    destruct dec_enc as [[m H1]|H1].
    - specialize (H a id); asimpl in H. rewrite H in H1. eapply enc_injective in H1 as []; (eauto 2).
    - exfalso. eapply H1. exists n. specialize (H a id); asimpl in H. now rewrite H.
  Qed.



  Lemma SU_H10 E: SOU ag 2 (H10_to_SOU E) -> H10 E.
  Proof.
    rewrite SOU_NSOU; (eauto 2). intros (Delta & sigma & T & EQ & N).
    exists (decode_subst sigma N). intros e H; pose (Q := eqs e).
    assert (forall p, p ∈ Q -> sigma • fst p ≡ sigma • snd p) as EQs; [|clear EQ].
    - intros [s t] G. eapply EQ.
      eapply in_Equations. eauto.
    - destruct e; econstructor; cbn in Q, EQs.
      all: specialize (EQs (varEQ x)) as EQx; mp EQx; intuition idtac; eapply backward_vars in EQx as [n EQx]; (eauto 2).
      2 - 3: specialize (EQs (varEQ y)) as EQy; mp EQy; intuition idtac; eapply backward_vars in EQy as [m EQy]; (eauto 2).
      2 - 3: specialize (EQs (varEQ z)) as EQz; mp EQz; intuition idtac; eapply backward_vars in EQz as [p EQz]; (eauto 2).
      all: repeat (erewrite decode_subst_encodes;[|eauto]).
      + eapply backward_consts; (eauto 4).
      + eapply backward_add; (eauto 1); eapply EQs; (eauto 5).
      + eapply backward_mult; (eauto 1); eapply EQs; intuition idtac.
  Qed.
End Backward.



Lemma Goldfarb': H10 ⪯ SOU ag 2.
Proof.
  exists H10_to_SOU; intros x; split.
  - eapply H10_SU.
  - eapply SU_H10.
Qed.




Definition nileq: eq ag := (lambda lambda a, lambda lambda a).
Definition conseqs e1 e2 :=
  match e1, e2 with
  | (lambda lambda s1, lambda lambda t1), (lambda lambda s2, lambda lambda t2) => (lambda lambda g s1 s2, lambda lambda g t1 t2)
  | _, _ => nileq
  end.

Notation foldeqs := (fold_right conseqs nileq).


Lemma conseqs_combine sigma s1 s2 t1 t2:
  sigma • (lambda lambda s1) ≡ sigma • (lambda lambda t1) /\ sigma • (lambda lambda s2) ≡ sigma • (lambda lambda t2) <-> sigma • (lambda lambda g s1 s2) ≡ sigma • (lambda lambda g t1 t2).
Proof.
  cbn; split.
  - intros [H1 H2]; do 2 (eapply equiv_lam_elim in H1; eapply equiv_lam_elim in H2). now rewrite H1, H2.
  - intros H1; do 2 eapply equiv_lam_elim in H1. Injection H1. Injection H. now rewrite H0, H2.
Qed.

Lemma foldeqs_lambda_lambda E:
  exists s t, foldeqs E = (lambda lambda s, lambda lambda t).
Proof.
  induction E as [|[s t]]; cbn; (eauto 2).
  - do 2 eexists; reflexivity.
  - destruct IHE as (s'&t'&IH).
    do 2 (destruct s; try solve [do 2 eexists; reflexivity]).
    do 2 (destruct t; try solve [do 2 eexists; reflexivity]).
    rewrite IH; do 2 eexists; reflexivity.
Qed.

Lemma foldeqs_correct sigma E:
  (forall s1 s2, (s1, s2) ∈ E -> (exists t, s1 = lambda lambda t) /\ (exists t, s2 = lambda lambda t)) ->
  (sigma •₊ left_side E) ≡₊ (sigma •₊ right_side E) <->
  (sigma • fst (foldeqs E) ≡ sigma • snd (foldeqs E)).
Proof.
  induction E as [| [s t]]; simplify.
  - cbn; firstorder.
  - intros H. apply id in H as H'. specialize (H' s t) as ([t1 H1]&[t2 H2]); lauto; subst.
    cbn. specialize (foldeqs_lambda_lambda E) as (u&v&H'); rewrite H' in *.
    mp IHE; (eauto 2). intros; eapply H; firstorder. cbn in IHE.
    cbn; unfold left_side, right_side in *.
    split; [intros [H1 H2] % equiv_lstep_cons_inv| intros H1]; do 2 eapply equiv_lam_elim in H1.
    + destruct IHE as [IHE _]; rewrite H1; mp IHE; (eauto 1);
        do 2 eapply equiv_lam_elim in IHE; now rewrite IHE.
    + Injection H1. Injection H0. rewrite H3.
      destruct IHE as [_ ->]; (eauto 2). now rewrite H2.
Qed.


Lemma foldeqs_typing Gamma E:
  Gamma ⊢₊₊(2) E : repeat (alpha → alpha → alpha) (length E) -> Gamma ⊢₂(2) (foldeqs E) : alpha → alpha → alpha.
Proof.
  remember (repeat (alpha → alpha → alpha) (| E |)) as L. induction 1 in HeqL |- *; cbn.
  - repeat econstructor.
  - do 2 (destruct s; try solve [repeat econstructor]).
    do 2 (destruct t; try solve [repeat econstructor]).
    specialize (foldeqs_lambda_lambda E) as (u&v&H'); rewrite H' in *.
    cbn in HeqL. injection HeqL as -> ->. mp IHeqs_ordertyping; (eauto 2).
    inv H0. inv H4. inv H. inv H4. destruct IHeqs_ordertyping as [T1 T2]. inv T1. inv H4.
    inv T2. inv H4. repeat econstructor; (eauto 2).
Qed.


Lemma Goldfarb : H10 ⪯ OU 2 ag.
Proof.
  unshelve eexists.
  - intros E. unshelve econstructor.
    exact (Gamma__deq E). 1: eapply fst. 2: eapply snd.
    1 - 2: eapply foldeqs, (H10_to_SOU E).
    exact (alpha → alpha → alpha).
    all: eapply foldeqs_typing; cbn -[Gamma__deq].
    all: eapply H10_to_SOU.
  - intros E. split.
    + intros H % H10_SU. destruct H as (Delta & sigma & H1 & H2).
      exists Delta. exists sigma. intuition idtac. eapply foldeqs_correct, equiv_pointwise_eqs; (eauto 2).
      cbn. intros s1 s2 (d&H3&H4) % in_flat_map.
      destruct d; cbn in H4; intuition idtac.
      all: change s1 with (fst (s1, s2)); rewrite <-?H, <-?H0.
      all: change s2 with (snd (s1, s2)); rewrite <-?H, <-?H0.
      all: cbn; (eauto 2).
    + intros (Delta & sigma & T & EQ). eapply SU_H10. exists Delta, sigma.
      intuition idtac.  eapply equiv_eqs_pointwise; (eauto 1); eapply foldeqs_correct; (eauto 2).
      cbn. intros s1 s2 (d&H3&H4) % in_flat_map.
      destruct d; cbn in H4; intuition idtac.
      all: change s1 with (fst (s1, s2)); rewrite <-?H1, <-?H0.
      all: change s2 with (snd (s1, s2)); rewrite <-?H1, <-?H0.
      all: cbn; (eauto 2).
Qed.
