Set Implicit Arguments.
Require Import RelationClasses Morphisms List Lia
        Omega Lia Init.Nat Setoid.
From Undecidability.HOU Require Import std.std calculus.calculus third_order.pcp.
Import ListNotations.

Set Default Proof Using "Type".

(* * Third-Order Encoding *)
Section Encoding.

  Context {X: Const}.
  Variable  (u v: nat).
  Hypothesis (u_neq_v: u <> v).
  
  
  (* Encoding of symbols *)
  Definition encb (b: symbol) : exp X :=
    var (if b then u else v).

  (* Encoding of words *)
  Definition enc (w: word) : exp X :=
    lambda (AppL (renL shift (map encb w)) (var 0)).

  (* Encoding of words *)
  Notation Enc := (map enc).


  (* ** Encoding Typing *)
  Section Typing.
    
    Lemma encb_typing (Gamma: ctx) b:
      (Gamma ⊢(3) @var X u : alpha → alpha) ->
      (Gamma ⊢(3) @var X v : alpha → alpha) ->
      Gamma ⊢(3) encb b : (alpha → alpha).
    Proof.
      intros H1 H2. destruct b; eauto.
    Qed.
    

    Lemma enc_typing (Gamma: ctx) w:
      (Gamma ⊢(3) @var X u : alpha → alpha) ->
      (Gamma ⊢(3) @var X v : alpha → alpha) ->
      Gamma ⊢(3) enc w : alpha → alpha.
    Proof.      
      intros.
      econstructor; eauto. inv H; inv H0.
      eapply AppL_ordertyping_repeated;eauto.
      eapply orderlisttyping_preservation_under_renaming.
      eapply repeated_ordertyping; simplify.
      intros; mapinj. eapply encb_typing. all: eauto. 
      intros ??; cbn; eauto.
    Qed.
    
    Lemma Enc_typing (Gamma: ctx) W:
      (Gamma ⊢(3) @var X u : alpha → alpha) ->
      (Gamma ⊢(3) @var X v : alpha → alpha) ->
      Gamma ⊢₊(3) Enc W : repeat (alpha → alpha) (length W).
    Proof.
      intros. eapply repeated_ordertyping; simplify; eauto.
      intros; mapinj. eapply enc_typing; eauto.
    Qed.
  End Typing.



  (* ** Encoding Properities *)
  

  (* *** Reduction *)
  Section Reduction.
    
    Lemma enc_nil s: enc [] s ≡ s.
    Proof.
      unfold enc; cbn.
      rewrite stepBeta; asimpl; cbn; eauto.
    Qed.

    Lemma enc_cons b w s: enc (b :: w) s ≡ encb b (enc w s).
    Proof.
      unfold enc. eapply equiv_join; rewrite stepBeta; asimpl;  eauto.
      rewrite map_map, map_id_list. rewrite map_map, map_id_list. eauto.
      all: intros; now asimpl.
    Qed.

    Hint Rewrite enc_nil enc_cons : simplify.

    Lemma enc_app w1 w2 s:
      enc (w1 ++ w2) s ≡ enc w1 (enc w2 s).
    Proof.
      induction w1; cbn; simplify; eauto.
      now rewrite IHw1. 
    Qed.

    Hint Rewrite enc_app : simplify.
    
    Lemma enc_concat W s:
      AppL (Enc W) s ≡ enc (concat W) s.
    Proof.
      induction W; cbn; simplify; eauto.
      now rewrite IHW. 
    Qed.
  End Reduction.

  
  Hint Rewrite enc_nil enc_cons enc_app : simplify.
  


  (* *** Substitution *)
  Section Substitution.

    Lemma encb_subst_id a (sigma: fin -> exp X):
      sigma u = var u -> sigma v = var v -> sigma • encb a = encb a.
    Proof.
      intros; unfold encb; cbn; destruct a; eauto.
    Qed.

    Lemma enc_subst_id (sigma: fin -> exp X) w:
      sigma u = var u -> sigma v = var v ->  sigma • (enc w) = enc w.
    Proof.
      unfold enc.
      intros H1 H2. cbn. f_equal.
      asimpl. f_equal. rewrite map_id_list; eauto.
      intros x ?; mapinj; mapinj. asimpl.
      rewrite <-compComp_exp, encb_subst_id; eauto.
    Qed.
    
    Lemma Enc_subst_id (sigma: fin -> exp X) W:
      sigma u = var u -> sigma v = var v ->  sigma •₊ Enc W = Enc W.
    Proof.
      intros. eapply map_id_list.
      intros; mapinj;eapply enc_subst_id; eauto.
    Qed.
    
  End Substitution.

  (* *** Injectivity *)
  
  Definition nostring (t: exp X) :=
    forall s, ~ t ≡ var u s /\  ~ t ≡ var v s.

  Section Injectivity.
    Lemma encb_eq a b:
      encb a ≡ encb b -> a = b.
    Proof using u u_neq_v.
      intros H % equiv_head_equal; cbn in *; eauto.
      injection H; destruct a, b; intros; eauto; exfalso; eapply u_neq_v; eauto.
    Qed.

    
    Lemma enc_eq w1 w2 s t:
      enc w1 s ≡ enc w2 t -> nostring s -> nostring t ->
      w1 = w2 /\ s ≡ t.
    Proof using u_neq_v.
      simplify. intros. induction w1 in w2, H |-*; destruct w2; cbn in *; eauto.
      - simplify in H; intuition. 
      - simplify in H. destruct b; firstorder. 
      - simplify in H; symmetry in H; destruct a; firstorder. 
      - simplify in H; Injection H.
        eapply IHw1 in H3 as [-> ->].
        now rewrite encb_eq with (a := a) (b := b).
    Qed.
  End Injectivity.


  Section EquivalenceInversion.

    Variables  (s t: exp X) (x: nat) (sigma: fin -> exp X) (S: list (exp X)).
    Hypothesis (H1: forall y, isVar (sigma y) /\ sigma y <> var x).
    Hypothesis (N: normal s).
    Hypothesis (EQ: S .+ sigma • s ≡ (var x) t).


    Lemma end_head_var:
      exists (h: nat) T s', s = AppR (var h) T /\ nth S h = Some s'.
    Proof using x v u_neq_v t sigma N H1 EQ.
      eapply normal_nf in N as N'. inv N'. destruct k; cbn in *; eauto; [|Discriminate].
      destruct (s0); cbn in H; intuition; clear H.
      - assert(f < |S| \/ f >= |S|) as [] by lia; eauto.
        eapply nth_error_lt_Some in H as H2; destruct H2; eauto.
        asimpl in EQ; rewrite sapp_ge_in in EQ; eauto.
        specialize (H1 (f - |S|)). intuition.
        eapply equiv_head_equal in EQ; cbn; simplify; eauto. simplify in EQ; cbn in EQ; eauto.
        destruct (sigma (f - (|S|))); cbn in *; intuition.
      - eauto. asimpl in EQ.
        eapply equiv_head_equal in EQ; cbn; simplify in *; eauto.
        cbn in EQ; discriminate.
    Qed.


    Lemma end_is_var_typed Gamma A C:
      S = Enc C -> 
      (repeat (alpha → alpha) (|S|) ++ Gamma ⊢(3) s : A) ->
      exists i e, i < |S| /\ s = var i e.
    Proof using x u_neq_v t sigma N H1 EQ.
      intros H2 H4; destruct end_head_var as (h' & T & s' & H5); intuition; subst.   
      destruct T as [| t1 [| t2 T]].
      + cbn in EQ. erewrite nth_error_sapp in EQ; eauto.
        rewrite nth_error_map_option in H0; destruct nth; try discriminate.
        cbn in H0; injection H0 as <-.
        unfold enc in EQ; Discriminate. 
      + exists h'. exists t1. intuition. now eapply nth_error_Some_lt in H0.
      + eapply AppR_ordertyping_inv in H4.
        destruct H4 as [L]; intuition.
        inv H3. rewrite nth_error_app1, nth_error_repeated in H5; simplify in *; eauto.
        inv H2. inv H8. cbn in H5; injection H5 as ?.
        rewrite !Arr_app in H; cbn in H. eapply (f_equal arity) in H.
        rewrite arity_Arr in H; cbn in H. lia.
        all: eapply nth_error_Some_lt in H0; simplify in H0; eauto.
    Qed.

    
  End EquivalenceInversion.

  

  Lemma AppL_decomposition (s: exp X) (n: nat):
    { '(I, u) | I ⊆ nats n /\ s = AppL (map var I) u /\ forall x v, u = var x v -> ~ x < n }.
  Proof.
    destruct (@AppL_largest _ (fun s => match s with var x => x < n | _ => False end) s)
      as (S & t & H2 & H3 & H4). intros []; intuition; now right.
    subst. induction S.
    - exists (nil, t). cbn; intuition. eapply H4; eauto.
    - edestruct IHS as [[I s'] (H1 & H3 & H5)].
      intros; eapply H2; intuition.
      specialize (H2 a); mp H2; lauto; destruct a; intuition.
      exists (f :: I, s'); cbn; intuition try congruence.
      eapply lt_nats in H2; lauto.
  Qed.


  Section MainLemma.

    Variable (Gamma : ctx) (s: exp X) (n: nat).

    Hypothesis (Ts: Gamma ⊢(3) s : Arr (repeat (alpha → alpha) n) alpha).
    Hypothesis (Vu: ~ u ∈ vars s) (Vv: ~ v ∈ vars s).


    Lemma main_lemma:
      exists I, I ⊆ nats n /\ forall W, |W| = n -> exists t,
        AppR s (Enc W) ≡ AppL (select I (Enc W)) t /\ nostring t.
    Proof using u_neq_v Vv Vu Ts Gamma.
      pose (mv := fun x => match x == u, x == v with right _,right _ => x | _,_ => S(u + v + x) end).
      assert (forall x, mv x >= x) as GE.
      { eauto; intros; unfold funcomp; intuition; unfold mv in *.
        eauto; intros; edestruct eq_dec; [lia|]; destruct eq_dec; eauto.
      }
      assert (forall x, var (mv x) <> @var X u) as Nu.
      { intros x H; injection H; unfold mv; destruct eq_dec; [lia|]; destruct eq_dec; [lia|].
        intros; subst; eauto.
      }
      assert (forall x, var (mv x) <> @var X v) as Nv.
      { intros x H; injection H; unfold mv; destruct eq_dec; [lia|]; destruct eq_dec; [lia|].
        intros; subst; eauto.
      }
      replace s with (ren mv s).
      2: { asimpl; erewrite subst_extensional with (tau := var); asimpl; eauto.
        intros; unfold funcomp, mv; destruct eq_dec; subst; [exfalso; eapply Vu; eauto|].
        destruct eq_dec; subst; [exfalso; eapply Vv; eauto|eauto].
      }
      eapply ordertyping_termination_steps in Ts as N; destruct N as [t [E N]].
      eapply normal_nf in N as N2. destruct N2 as [k a ? T _ isA ->].
      eapply ordertyping_preservation_under_steps in Ts as Tv; eauto. 
      eapply Lambda_ordertyping_inv in Tv as (L & B & H0 & H1 & <-).
      destruct (Nat.lt_total n (|L|)) as [?|[?|?]].
      - exfalso. eapply (f_equal arity) in H1; simplify in H1; lia.
      - destruct (AppL_decomposition (AppR a T) n) as [[I v''] (H2&H3&H4)].
        exists I. intuition. exists (Enc W .+ mv >> var • v'').
        split.
        + rewrite E.
          rewrite Lambda_ren, AppR_Lambda'; simplify; try congruence.
          rewrite it_up_var_sapp, H3, AppL_subst, select_variables_subst; simplify; eauto.
          all: rewrite ?H5; eauto. 
        + eapply Arr_inversion in H1 as [[] [H1 H6]]; simplify; try lia.
          2: discriminate. cbn in H1, H6. simplify in H1. subst.
          rewrite H3 in H0; eapply AppL_ordertyping_inv in H0 as (?&?&?&?).
          split; intros EQ; eapply end_is_var_typed in EQ  as (? & ? & ? & ?).
          1, 6: eapply H4; simplify in H6; eauto;
            rewrite <-H5; eauto. 3, 7: eauto.
          1, 4: intros; unfold funcomp; intuition eauto.
          1, 3: rewrite H3 in N; eapply normal_AppL_right, normal_Lambda, N.
          all: simplify; rewrite H1 in H0; simplify in H0; rewrite <-H5 in H0; eauto.
      - remember mv as delta. exists nil; intuition; cbn; simplify. eexists. rewrite E. intuition eauto.
        edestruct (@list_decompose_alt (length L) _ W) as (W1&W2&?&?);
          subst; eauto.
        simplify. rewrite !AppR_app, !Lambda_ren. split; rewrite !AppR_Lambda'; simplify; eauto.
        all: rewrite !it_up_var_sapp; simplify; eauto; rewrite AppR_subst.
        all: intros EQ.
        all: destruct a as [y| d | |]; cbn in isA;
          intuition; [destruct (le_lt_dec (length W2) y)|].
        all: revert EQ.
        (* a constant *)
        3, 6: cbn; intros EQ' % equiv_head_equal; cbn; simplify; cbn; auto 1.
        3, 4: simplify in EQ'; cbn in EQ'; subst; discriminate.
        (* x like constant *)
        1, 3: cbn; rewrite sapp_ge_in; simplify; eauto.
        1, 2: intros EQ' % equiv_head_equal; cbn; simplify; cbn; auto 1.
        1, 2: simplify in EQ'; cbn in EQ'; subst; eauto. 
        (* x is x_i *)
        all: eapply AppR_ordertyping_inv in H0 as [? [_ T2]]; intuition; inv T2.
        all: symmetry in H1; eapply Arr_inversion in H1 as H6; simplify; try lia.
        all: destruct H6 as (?&?&?); eapply repeated_app_inv in H0.
        all: intuition; subst; rewrite H0 in *; simplify in H4; simplify in H3; rewrite H4 in l.  
        all: eapply id in H3 as HH;
          rewrite nth_error_app1, nth_error_repeated in HH; simplify; eauto.
        all: injection HH as HH; destruct x0; simplify in H6; simplify in H3.
        all: simplify in H; try lia; cbn in H8; injection H8 as ->. 
        all: eapply (f_equal ord) in HH; simplify in HH.
        all: symmetry in HH; eapply Nat.eq_le_incl in HH; simplify in HH.
        all: intuition; cbn [ord'] in H9.
        all: cbn [add] in H9; rewrite Max.succ_max_distr in H9.
        all: eapply Nat.max_lub_l in H9; cbn in H9; lia.
    Qed.
  End MainLemma.

  
End Encoding.

Hint Rewrite @enc_app @enc_nil: simplify. 
Notation Enc u v := (map (enc u v)).



Section ReductionEncodings.

  Context {X: Const}.
  
  Definition finst I n := Lambda n (AppL (map var I) (@var X n)).

  Lemma finst_typing I n :
    I ⊆ nats n ->
    [alpha] ⊢(3) finst I n : Arr (repeat (alpha → alpha) n) alpha.
  Proof.
    intros H; eapply Lambda_ordertyping; simplify; eauto.
    eapply AppL_ordertyping_repeated.
    eapply repeated_ordertyping; simplify; eauto.
    intros; mapinj.  
    econstructor; simplify; cbn; eauto.
    rewrite nth_error_app1; simplify; eauto.
    eapply nth_error_repeated; eauto.
    1 - 2: eapply nats_lt, H, H2.
    econstructor; simplify; eauto.  
    rewrite nth_error_app2; simplify; eauto.
  Qed.
  
  
  Lemma finst_equivalence u v I W delta:
    I ⊆ nats (length W) ->
    AppR (ren delta (finst I (length W))) (Enc u v W) ≡ enc u v (concat (select I W)) (var (delta 0)).
  Proof.
    intros. unfold finst. rewrite !Lambda_ren, !AppL_ren.
    rewrite !map_id_list.
    2: intros ? ?; mapinj; cbn; eapply H, nats_lt in H2; now rewrite it_up_ren_lt. 
    cbn; rewrite it_up_ren_ge; eauto; simplify.
    rewrite !AppR_Lambda'; simplify; eauto. asimpl.
    rewrite !sapp_ge_in; simplify; eauto.
    rewrite !select_variables_subst; [|simplify; eauto..].
    now rewrite <-!select_map, enc_concat.  
  Qed.

End ReductionEncodings.


