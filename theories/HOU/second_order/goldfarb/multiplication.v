Set Implicit Arguments.
Require Import List Lia Program.Program.
From Undecidability.HOU Require Import std.std axioms.
Require Import RelationClasses Morphisms Init.Wf Init.Nat Setoid.
From Undecidability.HOU Require Import calculus.calculus second_order.goldfarb.encoding.
Require Import FinFun Coq.Arith.Wf_nat.
Import ListNotations ArsInstances.


Section Multiplication.

  Variable (n: nat).
  Implicit Type (X Y: list (nat * nat)).



  Lemma Cons_subst sigma s t:
    sigma • (s ::: t) = (sigma • s) ::: (sigma • t).
  Proof. reflexivity. Qed.
  Hint Rewrite Cons_subst : asimpl.

  Lemma Cons_injective s s' u u': s ::: u = s' ::: u' -> s = s' /\ u = u'.
  Proof. injection 1; eauto. Qed.

  Lemma Pair_subst sigma s t: sigma • ⟨s, t⟩ = ⟨sigma • s, sigma • t⟩.
  Proof. reflexivity. Qed.
  Hint Rewrite Pair_subst : asimpl.

  Lemma Pair_injective s s' u u': ⟨s, u⟩ = ⟨s', u'⟩ -> s = s' /\ u = u'.
  Proof. injection 1; eauto. Qed.


  Notation r := (var 2).
  Notation A := (var 1).
  Notation B := (var 0).

  Let σ p q :=  B .: A .: ⟨enc p A, enc q B⟩ ::: Nil .: (add 2) >> var.
  Let τ :=  Succ B .: enc n A .: Nil .:((add 2) >> var).

  Definition t k := ⟨enc (k * n) A, enc k B⟩.
  Definition T k := lambda lambda lambda lin (tab t k) r.


  Lemma T_subst m sigma: sigma • (T m) = T m.
  Proof.
    unfold T; cbn; asimpl. rewrite !map_id_list; eauto.
    rewrite tab_map_nats.
    intros; mapinj. unfold t; cbn; now asimpl.
  Qed.

  Lemma T_ren m delta: ren delta (T m) = T m.
  Proof.
    asimpl; now rewrite T_subst.
  Qed.

  Hint Rewrite T_subst T_ren : asimpl.


  Section G_subst.
  Lemma G_left_subst m p q: (T m) (⟨ enc p A, enc q B⟩ ::: Nil) A B ≡ σ p q • (lin (tab t m) r).
  Proof.
    rewrite <-T_ren with (delta := add 2).
    unfold T. eapply equiv_join.
    cbn. do 3 (dostep; cbn). unfold beta. rewrite rinstInst_exp, !compComp_exp. reflexivity.
    eapply refl_star. eapply ext_exp.
    intros [|[|[]]]; cbn; eauto. now asimpl.
  Qed.

  Lemma G_right_subst m: (T m) Nil (enc n A) (Succ B) ≡ τ • lin (tab t m) r.
  Proof.
    rewrite <-T_ren with (delta := add 2).
    unfold T. eapply equiv_join.
    cbn. do 3 (dostep; cbn). unfold beta. rewrite rinstInst_exp, !compComp_exp. reflexivity.
    eapply refl_star. eapply ext_exp.
    intros [|[|[]]]; cbn; eauto. now asimpl.
  Qed.
  End G_subst.


  Section t_subst.
  Lemma hat_t_sigma p q k: σ p q • t k = t k.
  Proof. cbn; now asimpl. Qed.
  
  Lemma hat_t_tau k: τ • t k = t (S k).
  Proof.
    cbn; asimpl; cbn; simplify.
    rewrite <-!enc_app.
    now replace (k * n + n) with (n + k * n) by lia.
  Qed.
  End t_subst.
  Hint Rewrite hat_t_sigma hat_t_tau : asimpl.


  Section G_reduce.
  Lemma G_left_reduce m p q:
    (T m) (⟨ enc p A, enc q B⟩ ::: Nil) A B ≡ lin (tab t m) (⟨ enc p A, enc q B⟩ ::: Nil).
  Proof.
    rewrite G_left_subst. asimpl. rewrite map_id_list; eauto.
   rewrite tab_map_nats.
   intros; mapinj. unfold t; cbn; now asimpl.
  Qed.

  Lemma G_right_reduce m:
    (T m) Nil (enc n A) (Succ B) ≡ lin (tab (S >> t) m) Nil.
  Proof.
    rewrite G_right_subst. asimpl. eapply eq_equiv. f_equal.
    rewrite tab_map. eapply tab_ext.
    intros ?; unfold funcomp, t; cbn; asimpl. unfold Pair, τ; cbn.
    f_equal. f_equal. rewrite <-enc_app. f_equal; lia.
    now simplify.
  Qed.
  End G_reduce.


  Definition Grel m p G :=
    lambda lambda (ren (add 2) G) (⟨ enc p A, enc m B⟩ ::: Nil) A B ≡
    lambda lambda ⟨ A, B ⟩ ::: (ren (add 2) G) Nil (enc n A) (Succ B).


  Lemma G_forward m: Grel m (m * n) (T m).
  Proof.
    unfold Grel. asimpl. do 2 eapply equiv_lam_proper.
    unfold Cons at 2. rewrite G_left_reduce, G_right_reduce.
    rewrite <-lin_cons. change (⟨ A, B ⟩) with (t 0). rewrite <-tab_S.
    change (_ ::: _) with (lin [t m] Nil). now rewrite <-lin_app.
  Qed.



  Lemma multiplication_lambdas M m p:
    normal M -> Grel m p M -> (exists M', M = (lambda lambda lambda M') /\ σ p m • M' =  t 0 ::: (τ • M')).
  Proof.
    unfold  Grel, Pair, Cons. cbn. intros Nu EQ.
    remember (fun m : nat => S (S m)) as delta. rename M into u.
    assert (normal (ren delta u)) as N' by (subst; eapply normal_ren; eauto).
    do 2 apply equiv_lam_elim in EQ.
    destruct u as [| | u' | ]; unfold funcomp; cbn in EQ.
    4: eapply head_atom in N'; eauto.
    1, 2, 4: Injection EQ; Injection H; Discriminate.
    rewrite stepBeta in EQ; eauto.  asimpl in EQ.
    rewrite stepBeta in EQ; eauto.  asimpl in EQ.
    destruct u' as  [[]| | u' | ]; cbn in EQ.
    1 - 3: Injection EQ; Injection H; Discriminate.
    - do 2 (rewrite stepBeta in EQ; eauto; asimpl in EQ; cbn in EQ).
      destruct u' as [[|[]] | | u' | u1 u2 ]; cbn in EQ.
      1 - 4: Injection EQ; unfold funcomp in *; Discriminate.
      + exists u'. intuition. do 2 (rewrite stepBeta in EQ; eauto; asimpl in EQ; cbn in EQ).
        repeat eapply normal_lam_elim in Nu.
        eapply equiv_unique_normal_forms; [eauto | eauto |idtac..]. subst delta; exact EQ.
        2: eapply normal_app_intro; cbn; intuition.
        2: repeat eapply normal_app_intro; eauto.
        all: eapply normal_subst; try eassumption.
        all: intros [|[|[]]]; cbn; eauto 2.
        all: unfold funcomp, Nil; (repeat eapply normal_app_intro); eauto 2.
        destruct n; simplify; eauto.
      + exfalso. repeat eapply normal_lam_elim in Nu.
        eapply head_atom in Nu as H'; eauto.
        eapply atom_head_lifting
          with (sigma := A .: g (g (enc p A) (enc m B)) (id Nil) .: delta >> var) in H' as H4.
        2: intros [|[]]; cbn; eauto.
        cbn in H4. Injection EQ. Injection H.
        destruct u1 as [[|[]]|[]| |]; cbn in H1; try Injection EQ; try Discriminate.
    - eapply normal_lam_elim in Nu.
      eapply head_atom in Nu; eauto.
      eapply atom_head_lifting with (sigma := g (g (enc p A) (enc m B)) Nil .: delta >> var) in Nu; cbn in Nu.
      2: intros []; cbn; eauto.
      Injection EQ. Injection H. Discriminate.
  Qed.


  Section InvertSubstitution.

    Variable (p q: nat).

    Lemma subst_var_a s':
      σ p q • s' = A -> s' = A.
    Proof.
      intros H4. destruct s'; try discriminate. cbn in H4.
      destruct f as [|[|[]]]; cbn in H4; try discriminate; eauto.
    Qed.

    Lemma subst_var_b s':
      σ p q • s' = B -> s' = B.
    Proof.
      intros H4. destruct s'; try discriminate. cbn in H4.
      destruct f as [|[|[]]]; cbn in H4; try discriminate; eauto.
    Qed.


    Lemma subst_enc k e u:
      σ p q • e = enc k u -> exists e', e = enc k e' /\ σ p q  • e' = u.
    Proof using τ n.
      induction k in e |-*; cbn.
      - intros; eexists; intuition; eauto.
      - intros. simplify in *.
        destruct e as [ [| [| []]] | | | e1 e3 ]; try discriminate.
        destruct e1 as [ [| [| []]] | | | e1 e2 ]; try discriminate.
        destruct e1 as [ [| [| []]] | [] | | ]; try discriminate.
        destruct e2 as [ [| [| []]] | [[]|] | | ]; try discriminate.
        simplify in H.
        injection H as H.
        destruct (IHk _ H) as [e']; intuition; subst.
        exists e'. simplify. intuition.
    Qed.

    Lemma subst_t e k:
      σ p q • e = t k -> e = t k.
    Proof.
      unfold t; intros.
      destruct e as [ [| [| []]] | | | e1 e3 ] ; try discriminate.
      { cbn in *. asimpl in H. cbn in *.
        injection H as ?. destruct k; discriminate. }
      destruct e1 as [ [| [| []]] | | | e1 e2 ]; try discriminate.
      destruct e1 as [ [| [| []]] | [] | | ]; try discriminate.
      cbn -[add] in *. f_equal; injection H as H H'.
      asimpl in H. asimpl in H'. cbn in H, H'. unfold funcomp in H, H'.
      eapply subst_enc in H as [? []]; eauto.
      eapply subst_enc in H' as [? []]; eauto. subst.
      eapply subst_var_a in H0. eapply subst_var_b in H2.
      now subst.
    Qed.

  End InvertSubstitution.

  Section RecoverStructure.

    Lemma step_u u p q k:
      σ p q • u = t k ::: (τ • u) ->
      u = r \/ (exists u', u = t k ::: u').
    Proof.
      intros EQ. destruct u as [| | | t1 t3]; try discriminate; eauto.
      - cbn in *. asimpl in EQ.
        destruct f as [|[|[]]]; try discriminate. now left.
      - destruct t1 as [[|[|[]]]| | | t1 t2]; cbn in *; try discriminate; eauto.
        destruct t1 as [[|[|[]]]| [] | |]; cbn in *; try discriminate; eauto.
        injection EQ as EQ1 EQ2. intros. asimpl in EQ1.
        eapply subst_t in EQ1; subst; eauto.
        right. now (exists t3).
    Qed.

    Fixpoint size_exp {Z} (s: exp Z) :=
      match s with
      | var _ => 0
      | const c => 0
      | app s t => S (size_exp s + size_exp t)
      | lambda s => S (size_exp s)
      end.

    Lemma steps_u u p q k:
      σ p q • u = t k ::: (τ • u) ->
      exists l, u = lin (tab (fun i => t (i + k)) l) r.
    Proof.
      specialize (well_founded_ind (measure_wf lt_wf (@size_exp ag))) as ind.
      revert k. induction u as [u IH] using ind; intros k EQ.
      destruct (step_u _ _ _ EQ) as [H1|H1].
      - subst. exists 0. reflexivity.
      - destruct H1 as [u' H1]. rewrite H1 in EQ.
        rewrite !Cons_subst in EQ. asimpl in EQ.
        eapply Cons_injective in EQ as [_ EQ].
        eapply IH in EQ as [l]; [|subst u; hnf; cbn; lia].
        exists (S l). rewrite tab_S, H1, H.
        simplify. unfold Cons. f_equal. f_equal. rewrite !tab_map_nats. eapply map_ext.
        intros. f_equal; lia.
    Qed.


  End RecoverStructure.



  Lemma G_backward_exists m p M: normal M -> Grel m p M -> exists l, M = T l.
  Proof.
    intros N [M' [-> [l ->] % steps_u]] % multiplication_lambdas; eauto.
    exists l; erewrite tab_ext; now eauto.
  Qed.

  Lemma G_backward_equations m p l: Grel m p (T l) -> m = l /\ m * n = p.
  Proof.
    unfold Grel. rewrite <-G_forward.
    rewrite !T_ren. rewrite !G_left_reduce.
    intros H % equiv_lam_elim % equiv_lam_elim.
    eapply equiv_unique_normal_forms in H; [|eauto| |].
    eapply lin_injective in H as [_ H]; eauto.
    eapply Cons_injective in H as [[H1 H2] % Pair_injective _].
    eapply eq_equiv, enc_injective in H1; eauto.
    eapply eq_equiv, enc_injective in H2; eauto.
    intuition; subst; lia.
    all:  eapply lin_normal.
    1, 3: rewrite tab_map_nats; intros; mapinj; unfold t; cbn.
    all: repeat eapply normal_app_intro; eauto.
  Qed.


  Lemma G_iff m p G: normal G -> ((m * n = p /\ G = T m) <-> Grel m p G).
  Proof.
    intros N. split.
    - intros [<- ->]. apply G_forward.
    - intros H. specialize (G_backward_exists N H) as [l ->].
      eapply G_backward_equations in H; intuition.
  Qed.


End Multiplication.
