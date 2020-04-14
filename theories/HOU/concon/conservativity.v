Set Implicit Arguments.
Require Import Morphisms Omega List.
From Undecidability.HOU Require Import std.std calculus.calculus 
        unification.higher_order_unification unification.systemunification
        unification.nth_order_unification.
Import ListNotations.



(** * Conservativity *)

Section Constants.

  (** ** Constant Operations *)
  Section ConstantsOfTerm.
    Context {X: Const}.
    Implicit Types (s t: exp X).

    Fixpoint consts s :=
      match s with
      | var x => nil
      | const c => [c]
      | lambda s => consts s
      | app s t => consts s ++ consts t
      end.
    Definition Consts S := (flat_map consts S).

    Lemma Consts_consts s S:
      s ∈ S -> consts s ⊆ Consts S.
    Proof.
      unfold Consts; eauto using flat_map_in_incl.
    Qed.

    Lemma Consts_montone S T:
      S ⊆ T -> Consts S ⊆ Consts T.
    Proof.
      unfold Consts; eauto using flat_map_incl.
    Qed.

    Lemma consts_ren delta s:
      consts (ren delta s) = consts s.
    Proof.
      induction s in delta |-*; cbn; intuition; congruence.
    Qed.

    Lemma vars_subst_consts x s sigma:
      x ∈ vars s -> consts (sigma x) ⊆ consts (sigma • s).
    Proof.
      intros H % vars_varof; induction H in sigma |-*; cbn; intuition.
      rewrite <-IHvarof; cbn; unfold funcomp; now rewrite consts_ren.
    Qed.

    Lemma consts_subst_in x sigma s:
      x ∈ consts (sigma • s) -> x ∈ consts s \/
                           exists y, y ∈ vars s /\ x ∈ consts (sigma y).
    Proof.
      induction s in sigma |-*.
      - right; exists f; intuition.
      - cbn; intuition.
      - intros H % IHs; cbn -[vars]; intuition.
        destruct H0 as [[]]; cbn -[vars] in *; intuition.
        right. exists n. intuition.
        unfold funcomp in H1; now rewrite consts_ren in H1.
      - cbn; simplify; intuition.
        + specialize (IHs1 _ H0); intuition.
          destruct H as [y]; right; exists y; intuition.
        + specialize (IHs2 _ H0); intuition.
          destruct H as [y]; right; exists y; intuition.
    Qed.


    Lemma consts_subset_step s t:
      s > t -> consts t ⊆ consts s.
    Proof.
      induction 1; cbn; intuition.
      subst. unfold beta.
      intros x ? % consts_subst_in; simplify; intuition.
      destruct H as [[|y] ?]; cbn in *; intuition.
    Qed.

    Lemma consts_subset_steps s t:
      s >* t -> consts t ⊆ consts s.
    Proof.
      induction 1; firstorder using consts_subset_step.
    Qed.



    Lemma consts_subst_vars sigma s:
      consts (sigma • s) ⊆ consts s ++ Consts (map sigma (vars s)).
    Proof.
      intros x [|[y]] % consts_subst_in; simplify; intuition.
      right; eapply Consts_consts; eauto using in_map.
    Qed.

    Lemma consts_Lam k s:
      consts (Lambda k s) === consts s.
    Proof.
      induction k; cbn; intuition.
    Qed.

    Lemma consts_AppL S t:
      consts (AppL S t) === Consts S ++ consts t.
    Proof.
      induction S; cbn; intuition.
      rewrite IHS; now rewrite app_assoc.
    Qed.

    Lemma consts_AppR s T:
      consts (AppR s T) === consts s ++ Consts T.
    Proof.
      induction T; cbn; intuition.
      rewrite IHT. intuition.
      split; intros c; simplify; intuition.
    Qed.



  End ConstantsOfTerm.


  Section ConstantSubstitution.

    Implicit Types (X Y Z : Const).

    Fixpoint subst_consts {X Y} (kappa: X -> exp Y) s :=
      match s with
      | var x => var x
      | const c => kappa c
      | lambda s => lambda (subst_consts (kappa >> ren shift) s)
      | app s t => (subst_consts kappa s) (subst_consts kappa t)
      end.


    Lemma ren_subst_consts_commute X Y (zeta: X -> exp Y) delta s:
      subst_consts (zeta >> ren delta) (ren delta s) = ren delta (subst_consts zeta s).
    Proof.
      induction s in delta, zeta |-*; cbn; eauto.
      - f_equal. rewrite <-IHs. f_equal.
        asimpl. reflexivity.
      - now rewrite IHs1, IHs2.
    Qed.


    Lemma subst_consts_comp X Y Z (zeta: X -> exp Y) (kappa: Y -> exp Z) s:
      subst_consts kappa (subst_consts zeta s) =
      subst_consts (zeta >> subst_consts kappa) s.
    Proof.
      induction s in zeta, kappa |-*; cbn; eauto.
      - f_equal. rewrite IHs. f_equal. fext.
        unfold funcomp at 4; unfold funcomp at 4.
        intros; rewrite <-ren_subst_consts_commute.
        reflexivity.
      - now rewrite IHs1, IHs2.
    Qed.


    Lemma subst_consts_ident Y zeta s:
      (forall x: Y, x ∈ consts s -> zeta x = const x) -> subst_consts zeta s = s.
    Proof.
      intros; induction s in zeta, H |-*; cbn; eauto.
      eapply H; cbn; eauto.
      rewrite IHs; eauto.
      unfold funcomp; now intros x -> % H.
      rewrite IHs1, IHs2; eauto.
      all: intros; apply H; cbn; simplify; intuition.
    Qed.


    Lemma subst_const_comm {X Y} (zeta: X -> exp Y) sigma delta s:
      (forall x, sigma (delta x) = var x) ->
      subst_consts zeta (sigma • s) = (sigma >> subst_consts zeta) • (subst_consts (zeta >> ren delta) s).
    Proof.
      induction s in zeta, sigma, delta |-*; intros H; cbn.
      - reflexivity.
      - unfold funcomp; asimpl.
        rewrite idSubst_exp; eauto.
        intros y; unfold funcomp; cbn.
        rewrite H; reflexivity.
      - f_equal. erewrite IHs with (delta := 0 .: delta >> shift).
        2: intros []; cbn; unfold funcomp; eauto; rewrite H; reflexivity.
        f_equal; [| now asimpl].
        fext; intros []; cbn; eauto.
        unfold funcomp at 2.
        now rewrite ren_subst_consts_commute.
      - erewrite IHs1, IHs2; eauto.
    Qed.


    Global Instance step_subst_consts X Y:
      Proper (Logic.eq ++> step ++> step) (@subst_consts X Y).
    Proof.
      intros ? zeta -> s t H; induction H in zeta |-*; cbn; eauto.
      econstructor; subst; unfold beta.
      erewrite subst_const_comm with (delta := shift).
      f_equal. fext.
      all: intros []; cbn; eauto.
    Qed.


    Global Instance steps_subst_consts X Y:
      Proper (Logic.eq ++> star step ++> star step) (@subst_consts X Y).
    Proof.
      intros ? zeta -> s t H; induction H in zeta |-*; cbn; eauto; rewrite H; eauto.
    Qed.


    Global Instance equiv_subst_consts X Y:
      Proper (Logic.eq ++> equiv step ++> equiv step) (@subst_consts X Y).
    Proof.
      intros ? zeta -> s t [v [H1 H2]] % church_rosser; eauto;
        now rewrite H1, H2.
    Qed.


    Lemma subst_consts_consts X Y (zeta: X -> exp Y) (s: exp X):
      consts (subst_consts zeta s) === Consts (map zeta (consts s)).
    Proof.
      unfold Consts; induction s in zeta |-*; cbn; simplify; intuition.
      - rewrite IHs.
        unfold funcomp; rewrite <-map_map, !flat_map_concat_map, map_map.
        erewrite map_ext with (g := consts); intuition.
        now rewrite consts_ren.
      - rewrite IHs1, IHs2, !flat_map_concat_map; simplify.
        now rewrite concat_app.
    Qed.

    Lemma consts_in_subst_consts X Y (kappa: X -> exp Y) c s:
      c ∈ consts (subst_consts kappa s) -> exists d, d ∈ consts s /\ c ∈ consts (kappa d).
    Proof.
      rewrite subst_consts_consts.
      unfold Consts; rewrite in_flat_map; intros [e []]; mapinj.
      exists x; intuition.
    Qed.


    Lemma subst_consts_up Y Z (zeta: Y -> exp Z) (sigma: fin -> exp Y):
      up (sigma >> subst_consts zeta) = up sigma >> subst_consts (zeta >> ren shift).
    Proof.
      fext; intros []; cbn; eauto.
      unfold funcomp at 1 2.
      now rewrite <-ren_subst_consts_commute.
    Qed.

    Lemma subst_const_comm_id Y zeta sigma (s: exp Y):
      subst_consts zeta s = s ->
      (sigma >> subst_consts zeta) • s = subst_consts zeta (sigma • s).
    Proof.
      induction s in zeta, sigma |-*; cbn; eauto.
      - injection 1 as H. f_equal.
        rewrite <-IHs; eauto.
        now rewrite subst_consts_up.
      - injection 1 as H. f_equal; eauto.
    Qed.



    Lemma typing_constants X n Gamma s A :
      Gamma ⊢(n) s : A -> forall c, c ∈ consts s -> ord (ctype X c) <= S n.
    Proof.
      induction 1; cbn;  intuition; subst; eauto.
      simplify in H1; intuition.
    Qed.


    Lemma typing_Consts X c n Gamma S' L:
      Gamma ⊢₊(n) S' : L -> c ∈ Consts S' -> ord (ctype X c) <= S n.
    Proof.
      induction 1; cbn; simplify; intuition eauto using typing_constants.
    Qed.




    Lemma preservation_consts X Y Gamma s A (zeta: X -> exp Y):
      Gamma ⊢ s : A -> (forall x, x ∈ consts s -> Gamma ⊢ zeta x : ctype X x) ->
      Gamma ⊢ subst_consts zeta s : A.
    Proof.
      induction 1 in zeta |-*; cbn; eauto.
      - intros H'. econstructor. eapply IHtyping.
        intros; eapply preservation_under_renaming; eauto.
        intros ?; cbn; eauto.
      - intros H'. econstructor.
        eapply IHtyping1; intros ??; eapply H'; simplify; intuition.
        eapply IHtyping2; intros ??; eapply H'; simplify; intuition.
    Qed.


    Lemma ordertyping_preservation_consts X Y n Gamma s A (zeta: X -> exp Y):
      Gamma ⊢(n) s : A -> (forall x, x ∈ consts s -> Gamma ⊢(n) zeta x : ctype X x) ->
      Gamma ⊢(n) subst_consts zeta s : A.
    Proof.
      induction 1 in zeta |-*; cbn; eauto.
      - intros H'. econstructor. eapply IHordertyping.
        intros; eapply ordertyping_preservation_under_renaming; eauto.
        intros ?; cbn; eauto.
      - intros H'. econstructor.
        eapply IHordertyping1; intros ??; eapply H'; simplify; intuition.
        eapply IHordertyping2; intros ??; eapply H'; simplify; intuition.
    Qed.

    Lemma subst_consts_Lambda Y Z (zeta: Y -> exp Z) k s:
        subst_consts zeta (Lambda k s) = Lambda k (subst_consts (zeta >> ren (plus k)) s).
    Proof.
        induction k in zeta |-*; cbn; asimpl; eauto.
        f_equal. rewrite IHk. f_equal. f_equal.
        asimpl. fext; intros x; unfold funcomp; f_equal; fext; intros ?.
        unfold shift; simplify; f_equal; omega.
    Qed.

    Lemma subst_consts_AppL X Y (tau: X -> exp Y) S t:
        subst_consts tau (AppL S t) = AppL (map (subst_consts tau) S) (subst_consts tau t).
    Proof.
        induction S; cbn; congruence.
    Qed.

    Lemma subst_consts_AppR X Y (tau: X -> exp Y) s T:
        subst_consts tau (AppR s T) = AppR (subst_consts tau s) (map (subst_consts tau) T).
    Proof.
        induction T; cbn; congruence.
    Qed.

  End ConstantSubstitution.
End Constants.

Hint Rewrite @consts_Lam @consts_AppL @consts_AppR : simplify.


(** ** Inhabiting Types *)
Section InhabitingTypes.

  Variable (X: Const).
  Implicit Types (s t: exp X) (Gamma Delta: ctx) (sigma tau: fin -> exp X).



  Definition inhab (x: fin) (A: type) := Lambda (arity A) (@var X (arity A + x)).

  Lemma inhab_ren delta x A: ren delta (inhab x A) = inhab (delta x) A.
  Proof.
    unfold inhab. asimpl. f_equal. f_equal.
    rewrite it_up_ren_ge; simplify; eauto.
  Qed.

  Lemma inhab_typing Delta x A:
    nth Delta x = Some (target A) -> Delta ⊢(1) inhab x A : A.
  Proof.
    intros H2. unfold inhab.
    destruct (type_decompose A) as (L & beta & ->); simplify in H2; cbn in H2.
    specialize (arity_decomposed L beta) as H3.
    rewrite H3. eapply Lambda_ordertyping; eauto.
    econstructor; cbn; eauto.
    rewrite nth_error_app2; simplify; eauto; omega.
  Qed.



  Lemma inhab_typing_inv Gamma x A:
    Gamma ⊢(1) inhab x A : A -> nth Gamma x = Some (target A).
  Proof.
    intros H; unfold inhab in H.
    eapply Lambda_ordertyping_inv in H as (L & B & ? & ? & ?); subst.
    inv H. rewrite <-H1 in H3.
    rewrite nth_error_app2 in H3; simplify in *; eauto.
    destruct B; cbn in H1; try omega. now rewrite H3.
  Qed.

  Lemma inhab_app Gamma Delta x A:
      Gamma ⊢(1) inhab x A : A -> Delta ++ Gamma ⊢(1) inhab (length Delta + x) A : A.
  Proof.
    intros H % inhab_typing_inv. eapply inhab_typing.
    rewrite nth_error_app2; simplify; eauto.
  Qed.


  Lemma inhab_typing' Gamma x A:
    nth Gamma x = Some A -> target' Gamma ⊢(1) inhab x A : A.
  Proof.
    intros H; eapply inhab_typing.
    unfold target'; erewrite map_nth_error; now eauto.
  Qed.

  Lemma consts_inhab x A: consts (inhab x A) === nil.
  Proof.
    unfold inhab; rewrite consts_Lam; reflexivity.
  Qed.

  Lemma normal_inhab x A: normal (inhab x A).
  Proof.
    unfold inhab. generalize (arity A + x) as k.
    induction (arity A); cbn; eauto using normal_lam_intro.
  Qed.

End InhabitingTypes.


Hint Resolve inhab_app inhab_typing inhab_typing' ord_target' : core.


(** ** Conservativity *)
Section Conservativity.
  Variable (X: Const).


  Section DowncastLemmas.

    Implicit Types (s t: exp X) (Gamma: ctx)  (A: type).
    Variable (n: nat).
    Hypothesis (Leq: 1 <= n).

    Lemma downcast_variables Gamma s t Delta sigma:
      Delta ⊩ sigma : Gamma -> sigma • s ≡ sigma • t ->
      exists Sigma tau, Sigma ⊩ tau : Gamma /\ tau • s ≡ tau • t /\ ord' Sigma <= 1.
    Proof.
      intros.
      pose (tau x := match nth Delta x with
                  | Some A => inhab X x A
                  | None => var x
                  end).
      exists (target' Delta). exists (sigma >> subst_exp tau). split; [|split].
      - intros ???; eapply preservation_under_substitution; eauto.
        unfold tau; intros ?? EQ; rewrite EQ.
        eauto using ordertyping_soundness.
      - erewrite <-compSubstSubst_exp; eauto. symmetry.
        erewrite <-compSubstSubst_exp; eauto. symmetry.
        now rewrite H0.
      - eauto.
    Qed.



    Lemma downcast_constants_ordered m Gamma s t Delta sigma:
      1 <= m -> Delta ⊩(m) sigma : Gamma -> sigma • s ≡ sigma • t ->
      exists Sigma tau, Delta ++ Sigma ⊩(m) tau : Gamma /\ tau • s ≡ tau • t /\
      ord' Sigma <= 1 /\ (forall x c, c ∈ consts (tau x) -> c ∈ Consts [s; t]).
    Proof.
      intros L' T EQ.
      pose (C0 := Consts [s; t]).
      pose (C := Consts (map sigma (nats (length Gamma)))).
      pose (zeta c := match find c C0 with
                  | Some n => const c
                  | None =>
                    match find c C with
                    | Some x => inhab X (length Delta + x) (ctype X c)
                    | None => var 0
                    end
                  end).
      exists (target' (map (ctype X) C)). exists (sigma >> subst_consts zeta). intuition.
      - intros ???. eapply ordertyping_preservation_consts.
        now eapply weakening_ordertyping_app, T.
        intros c H1. unfold zeta.
        destruct (find c C0); eauto.
        + econstructor; eapply typing_constants; eauto.
        + eapply Consts_consts
            with (S := (map sigma (nats (length Gamma)))) in H1 as H2.
          unfold C; eapply find_in in H2 as [y H2]. rewrite H2.
          eapply ordertyping_monotone, inhab_app, inhab_typing'; eauto.
          erewrite map_nth_error; eauto. now eapply find_Some.
          eapply in_map, lt_nats, nth_error_Some_lt; eauto.
      - rewrite !subst_const_comm_id. now rewrite EQ.
        all: eapply subst_consts_ident; intros x;
          rewrite Consts_consts with (S := [s; t]); intuition.
        all: now unfold zeta, C0; eapply find_in in H as [? ->].
      - eapply consts_in_subst_consts in H as [d []].
        unfold zeta in *. destruct find eqn: H1.
        + cbn in H0; intuition; subst.
          eapply find_Some, nth_error_In in H1; exact H1.
        + destruct (find d C) eqn: H2.
          all: rewrite ?consts_inhab in H0; cbn in H0; intuition.
    Qed.

    Lemma downcast_constants Gamma s t Delta sigma:
      Delta ⊩ sigma : Gamma -> sigma • s ≡ sigma • t ->
      exists Sigma tau, Delta ++ Sigma ⊩ tau : Gamma /\ tau • s ≡ tau • t /\
      ord' Sigma <= 1 /\ (forall x c, c ∈ consts (tau x) -> c ∈ Consts [s; t]).
    Proof.
      intros [m H] % ordertypingSubst_complete EQ.
      eapply ordertypingSubst_monotone with (m0 := S m) in H; eauto.
      eapply downcast_constants_ordered in H as (Sigma & tau & ?); [|omega|eauto].
      exists Sigma; exists tau; intuition. eapply ordertypingSubst_soundness; eauto.
    Qed.

    Lemma ordertyping_from_basetyping Sigma u B:
      (forall c, c ∈ consts u -> ord (ctype X c) <= S n) ->
      Sigma ⊢ u : B -> normal u -> ord B <= S n -> ord' Sigma <= n ->
      Sigma ⊢(n) u : B.
    Proof.
      induction 2; [eauto|eauto| |].
      - simplify; intros; econstructor; eapply IHtyping; intuition.
        eauto using normal_lam_elim. cbn; simplify; intuition.
      - intros; enough (ord A <= n).
        + econstructor; [eapply IHtyping1 | eapply IHtyping2].
          1, 5: intros; eapply H; cbn; intuition.
          1, 4: eauto using normal_app_r, normal_app_l.
          2, 4: eauto.
          1, 2: simplify; eauto; intuition.
        + eapply head_atom in H0; eauto; cbn in H0.
          destruct (head_decompose s) as [T].
          rewrite H3 in H0_.
          eapply AppR_typing_inv in H0_ as (? & ? & ?).
          enough (ord (Arr (rev x) (A → B)) <= S n)
            as H6 by (simplify in H6; intuition).
          destruct (head s); cbn in H0; eauto.
          all: inv H5.
          eapply ord'_elements in H2; eauto.
          eapply H; cbn; simplify; cbn; intuition.
    Qed.


  Lemma ordertyping_weak_ordertyping Gamma Delta sigma (s t: exp X):
    (forall x A, nth Gamma x = Some A -> x ∈ vars s ++ vars t -> Delta ⊢(n) sigma x : A) ->  sigma • s ≡ sigma • t ->
    (exists Sigma tau, Sigma ⊩(n) tau : Gamma /\ tau • s ≡ tau • t).
  Proof.
    intros T EQ.
    pose (tau x := if x el (vars s ++ vars t)
                then sigma x
                else match nth Gamma x with
                      | Some A => inhab X (length Delta + x) A
                      | None => var x
                      end).
    exists (Delta ++ target' Gamma). exists tau. split.
    - intros x B H'. unfold tau. rewrite H'; destruct dec_in.
      eapply weakening_ordertyping_app, T; eauto.
      eapply ordertyping_monotone; eauto.
    - rewrite !(subst_extensional) with (sigma0 := tau) (tau0 := sigma); eauto.
      all: intros; unfold tau; destruct dec_in; eauto; simplify in *.
      all: exfalso; eauto.
  Qed.


  Lemma unification_downcast sigma Gamma s t Delta A:
    Delta ⊩ sigma : Gamma -> Gamma ⊢(n) s : A -> Gamma ⊢(n) t : A -> sigma • s ≡ sigma • t ->
    exists Sigma tau, Sigma ⊩(n) tau : Gamma /\ tau • s ≡ tau • t.
  Proof.
    intros T T1 T2 H.
    pose (P x := x ∈ vars s ++ vars t).
    edestruct (downcast_variables) as (Sigma' & tau' & T' & H' & O');
      eauto; clear T H sigma Delta.
    edestruct (downcast_constants) as (Sigma'' & tau'' & T'' & H'' & O'' & C'');
      eauto; clear T' H' tau'.
    edestruct (normalise_subst) as (tau''' & R & H & T); eauto.
    eapply ordertyping_weak_ordertyping with (sigma := tau''').
    - intros. eapply ordertyping_from_basetyping.
      + intros ?; erewrite consts_subset_steps; eauto.
        intros H2 % C''; cbn in H2; simplify in H2.
        destruct H2; eapply typing_constants; [|eauto| |eauto]; eauto.
      + eauto.
      + domin H0; eauto.
      + simplify in H1; destruct H1; eapply vars_ordertyping_nth; eauto.
      + simplify; rewrite O', O''; cbn; eauto.
    - rewrite !subst_pointwise_equiv with (sigma := tau''') (tau := tau''); eauto.
  Qed.


  Lemma linearize_consts (S: list (exp X)):
    consts (linearize_terms S) === Consts S.
  Proof.
    unfold linearize_terms. cbn; simplify.
    split; unfold Consts; intros ? [x] % in_flat_map; eapply in_flat_map.
    all: intuition; try mapinj. eexists; intuition; eauto.
    now rewrite consts_ren in H1.
    exists (ren shift x); intuition. now rewrite consts_ren.
  Qed.


  Lemma unification_downcast_eqs sigma Delta (E: eqs X) Gamma L:
    (Gamma ⊢₊₊(n) E : L) ->
    (Delta ⊩ sigma : Gamma) -> (sigma •₊ left_side E) ≡₊ (sigma •₊ right_side E) ->
    exists Sigma tau, Sigma ⊩(n) tau : Gamma /\ (tau •₊ left_side E) ≡₊ (tau •₊ right_side E).
  Proof.
    intros T1 T2 H.
    pose (P x := x ∈ Vars' E). pose (s := linearize_terms (left_side E)).
    pose (t := linearize_terms (right_side E)).
    edestruct (downcast_variables) with (s := s) (t := t) as (Sigma' & tau' & T' & H' & O'); eauto.
    1: unfold s, t; now rewrite !linearize_terms_subst, linearize_terms_equiv.
    clear T2 H sigma Delta.
    edestruct (downcast_constants) with (s := s) (t := t)
      as (Sigma'' & tau'' & T'' & H'' & O'' & C''); eauto; clear T' H' tau'.
    edestruct (normalise_subst) as (tau''' & R & H & T); eauto.
    edestruct ordertyping_weak_ordertyping with (s := s) (t := t) (sigma := tau''').
    - intros. eapply ordertyping_from_basetyping.
      + intros ?; erewrite consts_subset_steps; eauto.
        intros H2 % C''. cbn [Consts flat_map] in H2.
        simplify in H2. unfold s, t in H2.
        rewrite !linearize_consts in H2.
        destruct H2; eapply typing_Consts.
        eapply left_ordertyping; eauto. eauto.
        eapply right_ordertyping; eauto. eauto.
      + eauto.
      + domin H0; eauto.
      + simplify in H1. unfold s, t in H1; rewrite !linearize_vars in H1.
        destruct H1 as [H1|H1]; eapply Vars_listordertyping in H1.
        2, 4: eauto using left_ordertyping, right_ordertyping.
        all: destruct H1 as [? [H1 H2]]; rewrite H0 in H1;
          injection H1 as ->; eauto.
      + simplify; rewrite O', O''; cbn; eauto.
    - rewrite !subst_pointwise_equiv with (sigma := tau''') (tau := tau''); eauto.
    - destruct H0 as [tau]. exists x. exists tau. destruct H0; split; eauto.
      unfold s, t in H1; now rewrite <-linearize_terms_equiv, <-!linearize_terms_subst.
  Qed.



  End DowncastLemmas.






  Program Instance unification_monotone {n} (D: orduni n X): orduni (S n) X :=
    {  Gamma₀ := Gamma₀; s₀ := s₀ ; t₀ := t₀; A₀ := A₀; }.


  Lemma unification_monotone_forward n (I: orduni n X):
    OU n X I -> OU (S n) X (unification_monotone I).
  Proof.
    intros (Delta & sigma & T & H). exists Delta; exists sigma. intuition.
    eapply ordertypingSubst_monotone; eauto.
  Qed.

  Lemma unification_monotone_backward n (I: orduni n X):
    1 <= n -> OU (S n) X (unification_monotone I) -> OU n X I.
  Proof.
    intros Leq (Delta & sigma & T & H).
    unfold OU. eapply unification_downcast; eauto.
    intros ???; eapply ordertyping_soundness; eauto.
  Qed.

  Program Instance unification_conservative {n} (D: orduni n X): uni X :=
    {  Gammaᵤ := Gamma₀; sᵤ := s₀ ; tᵤ := t₀; Aᵤ := A₀; }.
  Next Obligation.
    eapply ordertyping_soundness; eauto.
  Qed.
  Next Obligation.
    eapply ordertyping_soundness; eauto.
  Qed.

  Lemma unification_conservative_forward n (I: orduni n X):
    OU n X I -> U X (unification_conservative I).
  Proof.
    intros (Delta & sigma & T & H). exists Delta; exists sigma. intuition.
    eapply ordertypingSubst_soundness; eauto.
  Qed.

  Lemma unification_conservative_backward n (I: orduni n X):
    1 <= n -> U X (unification_conservative I) -> OU n X I.
  Proof.
    intros Leq (Delta & sigma & T & H).
    unfold OU. eapply unification_downcast; eauto.
  Qed.



  Program Instance SU_monotone {n} (I: ordsysuni X n): ordsysuni X (S n) :=
    {  Gamma₀' := @Gamma₀' _ _ I; E₀' := @E₀' _ _ I ; L₀' := @L₀' _ _ I; }.
  Next Obligation.
    eapply eqs_ordertyping_step, @H₀'.
  Qed.


  Lemma SU_monotone_forward n (I: ordsysuni X n):
    SOU X n I -> SOU X (S n) (SU_monotone I).
  Proof.
    intros (Delta & sigma & T & H). exists Delta; exists sigma. intuition.
    eapply ordertypingSubst_monotone; eauto.
  Qed.

  Lemma SU_monotone_backward n (I: ordsysuni X n):
    1 <= n -> SOU X (S n) (SU_monotone I) -> SOU X n I.
  Proof.
    intros Leq (Delta & sigma & T & H).
    unfold OU.
    edestruct unification_downcast_eqs as (Sigma & tau & H1); eauto using equiv_pointwise_eqs, @H₀'.
    intros ???; eapply ordertyping_soundness; eauto.
    exists Sigma, tau; intuition; eauto using equiv_eqs_pointwise.
  Qed.


  Program Instance SU_conservative {n} (I: ordsysuni X n): sysuni X :=
    {  Gammaᵤ' := @Gamma₀' _ _ I; Eᵤ' := @E₀' _ _ I ; Lᵤ' := @L₀' _ _ I; }.
  Next Obligation.
    eapply eqs_ordertyping_soundness, H₀'.
  Qed.


  Lemma SU_conservative_forward n (I: ordsysuni X n):
    SOU X n I -> SU X (SU_conservative I).
  Proof.
    intros (Delta & sigma & T & H). exists Delta; exists sigma. intuition.
    eapply ordertypingSubst_soundness; eauto.
  Qed.

  Lemma SU_conservative_backward n (I: ordsysuni X n):
    1 <= n -> SU X (SU_conservative I) -> SOU X n I.
  Proof.
    intros Leq (Delta & sigma & T & H).
    edestruct unification_downcast_eqs as (Sigma & tau & H1); eauto using equiv_pointwise_eqs, @H₀'.
    exists Sigma, tau; intuition; eauto using equiv_eqs_pointwise.
  Qed.

  Theorem unification_step n: 1 <= n -> OU n X ⪯ OU (S n) X.
  Proof.
    intros H; exists unification_monotone; split;
      eauto using unification_monotone_forward, unification_monotone_backward.
  Qed.

  Theorem unification_steps n m: 1 <= n <= m -> OU n X ⪯ OU m X.
  Proof.
    intros [H1 H2]; induction H2; eauto using unification_step, le_trans.
  Qed.

  Theorem unification_conserve n: 1 <= n -> OU n X ⪯ U X.
  Proof.
    intros H; exists unification_conservative; split;
      eauto using unification_conservative_forward, unification_conservative_backward.
  Qed.

  Theorem systemunification_step n: 1 <= n -> @SOU X n ⪯ @SOU X (S n).
  Proof.
    intros H; exists SU_monotone; split;
      eauto using SU_monotone_forward, SU_monotone_backward.
  Qed.

  Theorem systemunification_steps n m: 1 <= n <= m -> @SOU X n ⪯ @SOU X m.
  Proof.
    intros [H1 H2]; induction H2; eauto using systemunification_step, le_trans.
  Qed.

  Theorem systemunification_conserve n: 1 <= n -> @SOU X n ⪯ @SU X.
  Proof.
    intros H; exists SU_conservative; split;
      eauto using SU_conservative_forward, SU_conservative_backward.
  Qed.



End Conservativity.


(** ** Consequences *)
From Undecidability.HOU Require Import third_order.pcp third_order.simplified third_order.huet.

Corollary MPCP_U X: MPCP ⪯ U X.
Proof.
  eapply reduction_transitive. eapply MPCP_U3.
  eapply unification_conserve; eauto.
Qed.


Corollary PCP_U X: PCP ⪯ U X.
Proof.
  eapply reduction_transitive. eapply PCP_U3.
  eapply unification_conserve; eauto.
Qed.
