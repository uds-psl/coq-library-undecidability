Set Implicit Arguments.
Require Import RelationClasses Morphisms List Arith Lia Init.Nat Setoid.
From Undecidability.HOU Require Import std.std calculus.calculus unification.unification.
From Undecidability.HOU Require Import third_order.pcp third_order.encoding.
Import ListNotations.

Set Default Proof Using "Type".

(* * Huet Reduction *)
Section HuetReduction.

  Variable (X: Const).
  Let v n: fin := n.
  Let u n: fin := (S n).
  
  Let h: exp X := var 0.
  Let f: exp X := var 3.
  Let g: exp X := var 4.

  Lemma HGamma₀s₀A₀ (S: list card) : 
    [Arr (repeat (alpha → alpha) (length S)) alpha; (alpha → alpha) → alpha] ⊢( 3) 
    (lambda lambda lambda h (AppR f (Enc 1 2 (heads S))) (AppR f (repeat (var (u 1)) (length S)))) :
    ((alpha → alpha) → (alpha → alpha) → (alpha → alpha → alpha) →  alpha).
  Proof.
    do 4 econstructor. econstructor. econstructor; cbn; (eauto 1); cbn; (eauto 2).
    - eapply AppR_ordertyping with (L := repeat (alpha → alpha)  (length S) ); simplify.
      erewrite <-map_length; eapply Enc_typing.
      all: econstructor; (eauto 2).
      simplify; cbn; (eauto 3). 
    - eapply AppR_ordertyping. 
      + eapply repeated_ordertyping; simplify; [|eauto]. 
        intros s H'. eapply repeated_in in H'. subst.
        econstructor; cbn. 2: eauto. eauto.
      + econstructor; simplify; (eauto 3).
  Qed.

  Lemma HGamma₀t₀A₀ (S: list card) : 
    [Arr (repeat (alpha → alpha) (length S)) alpha; (alpha → alpha) → alpha] ⊢( 3) 
    (lambda lambda lambda h (AppR f (Enc 1 2 (tails S))) (var (u 1) (g (var (u 1))))) :
    ((alpha → alpha) → (alpha → alpha) → (alpha → alpha → alpha) →  alpha).
  Proof with cbn [ord' ord alpha]; simplify; cbn; (eauto 3).
    do 4 econstructor. econstructor. econstructor; (eauto 2)...
    cbn; (eauto 4). 
    2: do 2 econstructor...
    2 - 3: econstructor...
    eapply AppR_ordertyping with (L := repeat (alpha → alpha) (length S)); simplify.
    erewrite <-map_length; eapply Enc_typing.
    all: econstructor...
  Qed.

  (* ** Reduction Function *)
  Instance PCP_to_U (S: list card) : orduni 3 X.
  Proof with cbn [ord' ord alpha]; simplify; cbn; (eauto 2).
    refine {|
      Gamma₀ := [Arr (repeat (alpha → alpha) (length S)) alpha; (alpha → alpha) → alpha];
      s₀ :=  lambda lambda lambda h (AppR f (Enc 1 2 (heads S))) (AppR f (repeat (var (u 1)) (length S)));
      t₀ :=  lambda lambda lambda h (AppR f (Enc 1 2 (tails S))) (var (u 1) (g (var (u 1))));
      A₀ := (alpha → alpha) → (alpha → alpha) → (alpha → alpha → alpha) →  alpha;
      H1₀ := HGamma₀s₀A₀ S;
      H2₀ := HGamma₀t₀A₀ S;
    |}.
  Defined.

  Section ForwardDirection.

    Definition ginst (I: list nat) : exp X :=
      lambda AppL (repeat (var 0) (pred (|I|))) (var 1).

    (* ** Forward Direction *)
    
    Lemma ginst_typing I:
      [alpha] ⊢(3) ginst I : (alpha → alpha) → alpha. 
    Proof.
      econstructor. eapply AppL_ordertyping_repeated.
      eapply repeated_ordertyping.
      intros ? ? % repeated_in; subst; (eauto 2).
      simplify; (eauto 2).
      econstructor; (eauto 2).
    Qed.

    Lemma ginst_equivalence I (S: stack):
      I <> nil -> I ⊆ nats (length S) ->
      AppR (ren (add 3) (finst I (length S)))
           (repeat (var (u 1)) (| S |)) ≡ var (u 1) (ren (add 3) (ginst I) (var (u 1))).
    Proof.
      intros H H0. unfold finst. rewrite !Lambda_ren, !AppL_ren.
      rewrite !map_id_list.
      2: intros ? ?; mapinj; cbn; eapply H0, nats_lt in H3; now rewrite it_up_ren_lt.
      rewrite AppR_Lambda'; simplify; (eauto 2).
      unfold ginst; cbn [ren]; erewrite stepBeta.
      2: asimpl; simplify; cbn; unfold funcomp; (eauto 2).      
      cbn [ren]. rewrite it_up_ren_ge; simplify; (eauto 2).
      asimpl. rewrite select_variables_subst; simplify; (eauto 2).
      rewrite select_repeated; (eauto 2).
      unfold ginst; cbn; asimpl; simplify.
      rewrite sapp_ge_in; simplify; (eauto 3).
      replace (_ - _) with 3 by lia.
      destruct I; intuition.
    Qed.

    
    Lemma PCP_MU S:
      PCP S -> OU 3 X (PCP_to_U S).
    Proof.
      intros (I & ? & ? & ?).
      pose (sigma := finst I (length S) .: ginst I .: var).  
      exists [alpha]. exists sigma. split. 
      - intros x A. destruct x as [| [| x]]; try discriminate; cbn.
        3: intros [] % nth_error_In. 
        all: injection 1 as ?; subst.
        eapply finst_typing; (eauto 2).
        eapply ginst_typing.
      - cbn -[ginst].  do 3 eapply equiv_lam_proper.
        eapply equiv_app_proper.
        eapply equiv_app_proper. reflexivity.
        all: unfold shift, var_zero.
        all: rewrite !AppR_subst; rewrite ?Enc_subst_id; (eauto 2).        
        2: rewrite map_id_list.
        3: intros ? ? % repeated_in; subst; reflexivity.
        all: cbn; rewrite !ren_plus_base, !ren_plus_combine;
          change (1 + 1 + 1) with 3.
        2: rewrite !AppL_ren; simplify; cbn [ren]; unfold upRen_exp_exp.
        2: unfold up_ren, funcomp; cbn [scons].
        replace (|S|) with (|heads S|) at 1 by now simplify.
        replace (|S|) with (|tails S|) at 1 by now simplify.
        rewrite !finst_equivalence, H1; simplify; (eauto 2). 
        rewrite ginst_equivalence; (eauto 2). 
        unfold ginst; asimpl. now simplify.  
    Qed.

  End ForwardDirection.

  Section BackwardDirection.

    Variables  (s t: exp X) (x: nat) (sigma: fin -> exp X) (S: list (exp X)).
    Hypothesis (H1: forall y, isVar (sigma y) /\ sigma y <> var x).
    Hypothesis (N: normal s).
    Hypothesis (EQ: S .+ sigma • s ≡ (var x) t).

    Lemma end_is_var:
      (forall x, x ∈ S -> isVar x) -> exists i e, i < |S| /\ s = var i e.
    Proof using x t sigma N H1 EQ.
      intros H2; edestruct @end_head_var with (X:=X) as (h' & T & s' & H5 & ?); (eauto 2). subst s. 
      destruct T as [| t1 [| t2 T]]. 
      all: cbn in EQ; specialize (H1 h'). 
      all: destruct (sigma h') eqn: H'; cbn in *; intuition.
      1, 3: eapply nth_error_In in H as H7; eapply H2 in H7.
      1, 2: eapply nth_error_sapp in H; rewrite ?H in EQ.
      + destruct s'; cbn in *; intuition.  Discriminate.
      + rewrite AppR_subst in EQ; cbn in EQ. 
        eapply equiv_app_elim in EQ as (EQ1 & EQ2); cbn; (eauto 1); simplify.
        destruct s'; cbn in *; intuition.
        rewrite H in EQ1. 2: rewrite H; (eauto 3).
        exfalso. symmetry in EQ1.
        eapply equiv_neq_var_app; (eauto 1); simplify; (eauto 3).  
      + exists h'. exists t1. intuition. eauto using nth_error_Some_lt.
      Unshelve. exact 0.
    Qed.

  End BackwardDirection.


  (* ** Backward Direction *)
  Lemma MU_PCP S':
    NOU 3 (PCP_to_U S') -> PCP S'.
  Proof.
    intros (Delta & sigma & T & H & N); cbn in *.
    repeat apply equiv_lam_elim in H.
    eapply equiv_app_elim in H as [EQ2 EQ1]; cbn; intuition. 
    eapply equiv_app_elim in EQ2 as [_ EQ2]; cbn; intuition. 
    rewrite !AppR_subst in EQ1; rewrite !AppR_subst in EQ2.
    rewrite !Enc_subst_id in EQ2;try reflexivity.
    cbn in *.  unfold funcomp in *.
    rewrite !ren_plus_base, !ren_plus_combine in *;
      change (1 + 1 + 1) with 3 in *.
    unfold shift, var_zero in *.
    rewrite map_id_list in EQ1; [| intros ? ? % repeated_in; now subst ]. 
    assert (Delta ⊢(3) sigma 0 : Arr (repeat (alpha → alpha) (length S')) alpha) as T1
        by now apply T.
    specialize (N 0) as N2; eapply normal_nf in N2 as N3.
    destruct N3 as [k x t' T' Hi H ->]. 
    eapply Lambda_ordertyping_inv in T1 as (L & B & H0 & H1 & <-).
    eapply id in H0 as T2.
    assert (|L | <= |S'|) as L1 by
          (eapply (f_equal arity) in H1; simplify in H1; rewrite H1; eauto).
    symmetry in H1; eapply Arr_inversion in H1 as (L2 & H1 & H2); simplify; try lia.
    eapply repeated_app_inv in H1 as (H1 & H3 & H4); (eauto 2).
    rewrite H4 in H2; subst B.
    rewrite H3 in *; simplify in *. clear H3 H4 L1. revert H0 H1 EQ1 EQ2 T2 N2.
    generalize (length L); generalize (length L2); clear L L2. intros l k H0 H1 EQ1 EQ2 T2 N2.
    edestruct (@list_decompose_alt  k _ S') as (S1 & S2 & H4 & H5); try lia; subst S'. 
    rewrite !Lambda_ren in EQ1; rewrite !Lambda_ren in EQ2. 
    simplify in EQ1 EQ2; rewrite !AppR_app in EQ1; rewrite !AppR_app in EQ2.
    simplify in H1; assert (length S1 = l) as H2 by lia; clear H1; subst.
    rewrite !AppR_Lambda' in EQ1, EQ2; simplify; (eauto 2).
    rewrite AppR_Lambda' in EQ2; simplify; (eauto 2).
    rewrite it_up_var_sapp in EQ1; simplify; intros; try lia.
    rewrite !it_up_var_sapp in EQ2; simplify; intros; try lia. 

    destruct (AppL_decomposition (AppR x T') (|S2|)) as [[I t] (H1&H2&H3)]. 
    rewrite H2 in EQ1, EQ2.
    destruct S1.
    + rewrite H2 in *. assert (normal t) by now eapply normal_AppL_right, normal_Lambda.
      rewrite !AppL_subst in EQ1; rewrite !AppL_subst in EQ2. cbn -[add] in *.
      rewrite !select_variables_subst in EQ2. 
      rewrite !select_variables_subst in EQ1.
      all: simplify; (eauto 2). 
      rewrite <-!select_map, !enc_concat in EQ2.
      eapply AppL_ordertyping_inv in T2 as (L' & B & H8 & H9).
      eapply enc_eq in EQ2; (eauto 2).
      2 - 3: split; intros EQ3;
        eapply end_is_var_typed in EQ3 as (? & ? & ? & ?); cbn; simplify.
      6, 9, 15, 21 :now eauto. 
      3, 8, 13, 16 : now eauto.
      (* close False goals *) 
      2, 6, 10, 13: eapply H3; cbn; (eauto 1); cbn; now simplify in *.
      (* close normal term goals *)
      3, 5, 8, 11: eauto.
      (* close typing goals *)
      3, 5, 9: eauto. 3, 4, 6:eauto.
      (* close var goals *)
      2 - 3: intros; cbn; unfold funcomp, u, v; intuition discriminate.
      exists I; intuition; eauto using nats_lt; (eauto 2).
      2: rewrite <-!select_map; (eauto 2). 
      subst; cbn [map select concat AppL] in H6, EQ1.
      eapply end_is_var in EQ1 as (? & ? & ? & ?);
        eauto; simplify.
      eapply H3; cbn; (eauto 1); cbn; now simplify in *.
      intros; cbn; intuition; discriminate.
      intros ? ? % repeated_in; subst; (eauto 2).
    + eapply id in T2 as T3. 
      eapply AppR_ordertyping_inv in T2 as (L' & T2 & T4).          
      destruct x as [i | | |]; cbn in H; (eauto 2).  
      * inv T4.       
        assert (i < length S2 \/ i >= length S2) as [H42|H42] by lia.
        ** rewrite nth_error_app1, nth_error_repeated in H6; simplify; (eauto 2).
           injection H6 as H6. eapply (f_equal ord) in H6. simplify in H6.
           symmetry in H6; eapply Nat.eq_le_incl in H6; simplify in H6.
           intuition. cbn in H6. lia. 
        ** rewrite <-H2 in EQ1. asimpl in EQ1. rewrite sapp_ge_in in EQ1; simplify; (eauto 2).
           eapply equiv_head_equal in EQ1; simplify; cbn; (eauto 2).
           simplify in EQ1; cbn in EQ1. discriminate EQ1.
      * rewrite <-H2 in EQ1. exfalso. asimpl in EQ1. 
        eapply equiv_head_equal in EQ1; cbn; simplify; cbn; intuition.
        cbn in EQ1; simplify in EQ1; discriminate. 
  Qed. 

  Theorem PCP_U3: PCP ⪯ OU 3 X.
  Proof.
    exists PCP_to_U. intros C; split; eauto using  PCP_MU.
    rewrite OU_NOU; eauto using MU_PCP.
  Qed.

End HuetReduction.
