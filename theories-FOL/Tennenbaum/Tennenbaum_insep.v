From FOL Require Import FullSyntax Arithmetics Theories.
From Undecidability.Shared Require Import ListAutomation.
From FOL.Tennenbaum Require Import MoreDecidabilityFacts Church Coding NumberUtils Formulas SyntheticInType Peano CantorPairing.

(* Require Import FOL Peano Tarski Deduction CantorPairing NumberTheory Synthetic DecidabilityFacts Formulas Coding Church. *)
Require Import Lia.
Import Vector.VectorNotations.

Notation "x 'el' A" := (List.In x A) (at level 70).
Notation "A '<<=' B" := (List.incl A B) (at level 70).
Notation "x ∣ y" := (exists k, x * k = y) (at level 50).


Section Model.

  Context {Δ1 : Delta1}.

  Variable D : Type.
  Variable I : interp D.
  Local Definition I' : interp D := extensional_model I.
  Existing Instance I | 100.
  Existing Instance I' | 0.
  Notation "⊨ phi" := (forall rho, rho ⊨ phi) (at level 21).
  Variable axioms : forall ax, PA ax -> ⊨ ax.

  Notation "N⊨ phi" := (forall rho, @sat _ _ nat interp_nat _ rho phi) (at level 40).
  Notation "x 'i=' y"  := (@i_atom PA_funcs_signature PA_preds_signature D I Eq ([x ; y])) (at level 40).
  Notation "'iσ' x" := (@i_func PA_funcs_signature PA_preds_signature D I Succ ([x])) (at level 37).
  Notation "x 'i⊕' y" := (@i_func PA_funcs_signature PA_preds_signature D I Plus ([x ; y])) (at level 39).
  Notation "x 'i⊗' y" := (@i_func PA_funcs_signature PA_preds_signature D I Mult ([x ; y])) (at level 38).
  Notation "'i0'" := (i_func (Σ_funcs:=PA_funcs_signature) (f:=Zero) []) (at level 2) : PA_Notation.
  Notation "x 'i⧀' y" := (exists d : D, y = iσ (x i⊕ d) ) (at level 40).

  (* We also assume the existence of a formula which represents the prime number function *)
  Variable ψ : form.
  Variable Hψ : bounded 2 ψ /\ (forall x, Q ⊢I ∀ ψ[up (num x)..] ↔ $0 == num (Irred x) ).


  Definition div e d := exists k : D, e i⊗ k = d.
  Definition div_num n (d : D) := exists e, inu n i⊗ e = d.
  Definition Div_nat (d : D) := fun n => div_num n d.
  Definition div_pi n a :=  (inu n .: (fun _ => a)) ⊨ (∃ (ψ ∧ ∃ $1 ⊗ $0 == $3)).

  Variable surj_form_ : { Φ : nat -> form & surj Φ }.
  Variable enumerable_Q_prv : forall Φ : nat -> form, enumerable (fun n => Q ⊢I (Φ n)).
  
  Definition Φ := projT1 surj_form_.
  Definition surj_form := projT2 (surj_form_).
  Definition A n := Q ⊢I ¬(Φ n)[(num n)..].
  Definition B n := Q ⊢I (Φ n)[(num n)..].


  Lemma Disjoint_AB : forall n, ~(A n /\ B n).
  Proof.
    unfold A, B. intros n [A_n B_n].
    apply Q_consistent.
    eapply IE; eauto.
  Qed.

  (** Recursively inseparable predicates.  *)

  Definition Insep' :=
    exists A B : nat -> Prop,
      enumerable A /\ enumerable B /\ 
      (forall n, ~ (A n /\ B n) ) /\ 
      (forall D, Dec D -> 
        (forall n, A n -> D n) ->
        (forall n, ~ (B n /\ D n)) -> False).

  Definition Insep :=
    exists α β,
      bounded 3 α /\ inhabited(delta1 α) /\ bounded 3 β /\ inhabited(delta1 β) /\ 
      (forall n, ~ Q ⊢I ((∃∃α) ∧ (∃∃β))[(num n)..] ) /\ 
      (forall G, Dec G -> (forall n, Q ⊢I (∃∃α)[(num n)..] -> G n) -> 
        (forall n, ~ (Q ⊢I (∃∃β)[(num n)..] /\ G n)) -> False).

  Lemma Insep_ :
    RT_strong -> Insep'.
  Proof.
    intros rt.
    exists A, B. repeat split; auto.
    1,2 : apply enumerable_Q_prv.
    { apply Disjoint_AB. }
    intros G Dec_G.
    destruct (rt G Dec_G) as [γ [? [? []]]],
      (surj_form (∃ γ)) as [c Hc].
    rewrite <-Hc in *.
    unfold A, B in *; fold Φ in *.
    intros ? ?%(fun h => h c).
    enough (~ G c); auto.
  Qed.

  Lemma CT_Inseparable : 
    CT_Q -> Insep.
  Proof.
    intros ct.
    destruct (Insep_ (CT_RTs ct)) as (A & B & HA & HB & disj & H).
    destruct ((CT_RTw ct) A HA) as [α (Ha0 & [Ha1] & Hα)],
            ((CT_RTw ct) B HB) as [β (Hb0 & [Hb1] & Hβ)].
    exists α, β. do 4 (split; auto).  
    repeat split; auto; unfold weak_repr in *.
    - intros n h%soundness. apply (disj n).
      rewrite Hα, Hβ.
      split; apply sigma1_ternary_complete; auto.
      all: intros rho; specialize (h _ interp_nat rho);
            apply h; apply Q_std_axioms.
    - setoid_rewrite <-Hα.
      setoid_rewrite <-Hβ.
      apply H.
  Qed.


  Lemma WInsep_ :
    WRT_strong -> Insep'.
  Proof.
    intros wrt.
    exists A, B. repeat split; auto.
    1,2 : apply enumerable_Q_prv.
    { apply Disjoint_AB. }
    intros G Dec_G.
    intros H.
    apply (DN_remove (wrt G Dec_G)).
    intros [γ [? [? []]]].
    destruct (surj_form (∃ γ)) as [c Hc].
    rewrite <-Hc in *.
    unfold A, B in *; fold Φ in *.
    intros ?%(fun h => h c).
    enough (~ G c); auto.
  Qed.


  Lemma WCT_Inseparable :
    WCT_Q -> ~~ Insep.
  Proof.
    intros wct.
    destruct (WInsep_ (WCT_WRTs wct)) as (A & B & HA & HB & disj & H).
    apply (DN_chaining ((WCT_WRTw wct) B HB)), (DN_chaining ((WCT_WRTw wct) A HA)), DN.
    intros [α (Ha0 & [Ha1] & Hα)] [β (Hb0 & [Hb1] & Hβ)].
    exists α, β. do 4 (split; auto).
    repeat split; unfold weak_repr in *.
    - intros n h%soundness. apply (disj n).
      rewrite Hα, Hβ.
      split; apply sigma1_ternary_complete; auto.
      all: intros rho; specialize (h _ interp_nat rho);
            apply h; apply Q_std_axioms.
    - setoid_rewrite <-Hα.
      setoid_rewrite <-Hβ.
      apply H.
  Qed.



  Lemma delta1_ternary_definite phi :
    delta1 phi -> bounded 3 phi -> ⊨ ∀∀∀ phi ∨ ¬ phi.
  Proof.
    intros d0 b3.
    intros rho. cbn. intros ???.
    specialize (delta1_HA d0) as d0'.
    unshelve refine (let H := tsoundness d0' _  in _).
    3: apply H. intros ??.
    now apply axioms.
  Qed.

  Lemma LEM_bounded_exist_ternary' phi : 
    (⊨ ∀∀∀ phi ∨ ¬ phi) -> bounded 3 phi -> ⊨ ∀∀∀ (∃ $0 ⧀ $3 ∧ phi) ∨ ¬ (∃ $0 ⧀ $3 ∧ phi).
  Proof.
    intros def b3.
    pose (Phi := ∀∀ (∃ $0 ⧀ $3 ∧ phi) ∨ ¬ (∃ $0 ⧀ $3 ∧ phi)).
    assert (H : forall d rho, (d.:rho) ⊨ Phi).
    apply induction. 
    - apply axioms.
    - repeat solve_bounds;
      eapply bounded_up; apply b3 + lia.
    - intros rho y. cbn. right.
      now intros (? & ?%nolessthen_zero & ?).
    - intros n IHN rho y x. cbn. cbn in IHN.
      destruct (IHN rho y x) as [IH|IH]; fold sat in *; cbn in IH.
      + left. destruct IH as [d Hd]. exists d. split.
        ++ destruct Hd as [[k ->] _]. exists (iσ k). 
          now rewrite add_rec_r.
        ++ eapply bound_ext. apply b3.
          2 : apply Hd.
          intros [|[|[]]] ?; (eauto + solve_bounds); lia.
      + destruct (def (fun _ => i0) y x n) as [HN|HN]; fold sat in *.
        ++ left. exists n. split.
          exists i0. now rewrite add_zero_r.
          eapply bound_ext. apply b3.
          2 : apply HN.
          intros [|[|[]]] ?; (eauto + solve_bounds); lia.
        ++ right. intros H. apply IH.
          destruct H as (k & Hk1%lt_S & Hk2 ).
          exists k. split.
          destruct Hk1 as [| ->]. assumption.
          exfalso. apply HN.
          eapply bound_ext. apply b3.
          2 : apply Hk2.
          intros [|[|[]]] ?; (eauto + solve_bounds); lia.
          eapply bound_ext. apply b3.
          2 : apply Hk2.
          intros [|[|[]]] ?; (eauto + solve_bounds); lia.
          apply axioms.
      - intros rho y. apply H.
  Qed.


  Lemma LEM_bounded_exist_ternary {phi} sigma : 
    delta1 phi -> bounded 3 phi -> forall b x, (x .: b .: sigma) ⊨ (∃∃ $0 ⧀ $3 ∧ $1 ⧀ $3 ∧ phi) \/ ~ (x .: b .: sigma) ⊨ (∃∃ $0 ⧀ $3 ∧ $1 ⧀ $3 ∧ phi).
  Proof.
    intros d0 b3 b y.
    unshelve refine (let D' := @LEM_bounded_exist_ternary' (∃ $0 ⧀ $3 ∧ phi) _ _ in _); auto.
    - apply LEM_bounded_exist_ternary'; auto.
      now apply delta1_ternary_definite.
    - repeat solve_bounds. eapply bounded_up; eauto.
    - specialize (D' sigma b b y); fold sat in *.
      destruct D' as [H|nH].
      + left. cbn in H. destruct H as [x1 [H1 [x2 [H2 H]]]].
        exists x1, x2. cbn. repeat split; try tauto.
        eapply bound_ext. 3 : apply H. eauto.
        intros [|[|[]]] ?; (eauto + solve_bounds); lia.
      + right; cbn. intros (x1 & x2 & H). apply nH; fold sat; cbn.
        exists x1. split; try tauto.
        exists x2. split; try tauto.
        eapply bound_ext. 3 : apply H. eauto.
        intros [|[|[]]] ?; (eauto + solve_bounds); lia.
  Qed.


  (** Potential existence of undecidable predicates. *)

  Lemma nonDecDiv :
    Insep -> Stable std -> nonStd D -> ~ ~ exists d : D, ~ Dec (fun n => div_pi n d).
  Proof.
    intros (α & β & Ha1 & [Ha0] & Hb1 & [Hb0] & Disj & Insepa) Stab [d Hd].
    pose (phi := (∀ $0 ⧀ $1 → ∀ $0 ⧀ $2 → ∀ $0 ⧀ $3 → ∀ $0 ⧀ $4 → ∀ $0 ⧀ $5 → ¬ (α[$3..][$1..] ∧ β[$5..][$3..]) ) ).
    enough (forall n rho, ((inu n).:rho) ⊨ phi ) as Hx.
    unshelve epose proof (Overspill_DN _ _ _ _ Hx) as H. all: eauto.
    - unfold Coding.unary. repeat solve_bounds.
      eapply subst_bound with (N:=4).
      eapply subst_bound with (N:=4). eapply bounded_up; eauto. 
      intros [|[|[|[|[]]]]] ?; cbn; lia + solve_bounds.
      intros [|[|[|[|[]]]]] ?; cbn; lia + solve_bounds.
      eapply subst_bound with (N:=6).
      eapply subst_bound with (N:=6). eapply bounded_up; eauto. 
      intros [|[|[|[|[|[]]]]]] ?; cbn; lia + solve_bounds.
      intros [|[|[|[|[|[]]]]]] ?; cbn; lia + solve_bounds.
    - apply nonStd_notStd. now exists d.
    - refine (DN_chaining (@Coding_nonstd_binary_Definite _ _ _ _ _ _ _ (∃∃ $0 ⧀ $3 ∧ $1 ⧀ $3 ∧ α) _ _) _); eauto.
    {apply nonStd_notStd. now exists d. }
    { unfold Coding.binary. repeat solve_bounds.
      eapply bounded_up; eauto; lia. }
    { intros b u.
      specialize (LEM_bounded_exist_ternary (fun _ => i0) Ha0 Ha1 b (inu u)) as [h|h].
      - left. intros ?. eapply bound_ext with (N := 2).
        3 : apply h.
        repeat solve_bounds. eapply bounded_up; eauto.
        intros [|[]]; try reflexivity; lia.
      - right. intros nh. apply h.
        eapply bound_ext with (N := 2).
        3 : apply nh.
        repeat solve_bounds. eapply bounded_up; eauto.
        intros [|[]]; try reflexivity; lia.
    }
    apply (DN_chaining H).
    apply DN. clear H.
    intros [e [? He]] [c Hc]%(fun h => h e).
    exists c. intros Dec_div_c.
    eapply (Insepa _ Dec_div_c).
    + intros n A_n. unfold Div_nat.
      specialize (Hc n (fun _ => e)) as [Hc _].
      cbn in Hc. destruct Hc as [ d' [H1 H2] ].
      * assert (N⊨ (∃∃α)[(num n)..]) as A_n'.
        { intros rho. eapply soundness.
          - apply A_n.
          - apply Q_std_axioms.
        }
        apply sigma1_ternary_complete' in A_n'; auto.
        destruct A_n' as (a & b & Hab).
        exists (inu a), (inu b). repeat split; unfold I'; rewrite <- inu_I; [apply num_lt_nonStd; auto|apply num_lt_nonStd; auto| ].
        apply soundness in Hab.
        specialize (Hab D I' (fun _ => i0)). rewrite !sat_comp in Hab.
        eapply bound_ext. apply Ha1. 2: apply Hab.
        intros [|[|[]]] ?; cbn; try setoid_rewrite num_subst; try setoid_rewrite eval_num; try easy; try lia.
        1: try setoid_rewrite num_subst; try setoid_rewrite eval_num; easy.
        intros ??. apply axioms. now apply PA_compatible_Qeq_PAeq.
      * exists d'. split.
        eapply bound_ext. apply Hψ. 2: apply H1.
        intros [|[]]; try reflexivity; try lia.
        cbn. apply H2.
    + intros n [B_n C_n].
      assert (N⊨ (∃∃β)[(num n)..]) as B_n'.
      { intros rho. eapply soundness. 
        - apply B_n.
        - apply Q_std_axioms.
      }
      apply sigma1_ternary_complete' in B_n'; auto.
      destruct B_n' as (a & b & Hab).
      apply soundness in Hab.
      assert ((fun _ => e) ⊨ (∃∃ $0 ⧀ $2 ∧ $1 ⧀ $2 ∧ β[up (up (num n)..)] )) as Heβ.
      { cbn. exists (inu a), (inu b). repeat split; unfold I'; rewrite <- inu_I; [apply num_lt_nonStd; auto|apply num_lt_nonStd; auto| ].
        specialize (Hab D I' (fun _ => i0)). rewrite !sat_comp in Hab.
        rewrite sat_comp.
        eapply bound_ext. apply Hb1. 2: apply Hab.
        intros [|[|[]]] ?; cbn; try setoid_rewrite num_subst; try setoid_rewrite eval_num; try easy; try lia.
        1: try setoid_rewrite num_subst; try setoid_rewrite eval_num; easy.
        intros ??. apply axioms. now apply PA_compatible_Qeq_PAeq. }
      specialize (Hc n (fun _ => e)) as [_ Hc]. cbn in Hc.
      destruct Hc as (k1 & k2 & [Hk2 Hk1] & Hk12); fold sat in *.
      * destruct C_n as [d' Hd']. exists d'. split.
        eapply bound_ext. apply Hψ. 2 : apply Hd'.
        intros [|[]] ?; cbn; eauto + solve_bounds; lia.
        apply Hd'.
      * cbn in Heβ, Hk12, Hk1, Hk2. cbn in Heβ. destruct Heβ as (k3 & k4 & [Hk4 Hk3] & Hk34).
        rewrite sat_comp in Hk34. cbn in He.
        eapply He; fold sat; cbn.
        apply Hk4.
        apply Hk3.
        apply Hk2.
        apply Hk1.
        apply num_lt_nonStd with (n:=n); auto.
        rewrite !sat_comp.
        split.
        **  eapply bound_ext. 
            apply Ha1. 2: apply Hk12.
            intros [|[|[]]] ?; try reflexivity; try lia.
        **  eapply bound_ext. 
            apply Hb1. 2: apply Hk34.
            intros [|[|[]]] ?; cbn; try reflexivity; try lia.
            try setoid_rewrite num_subst; try setoid_rewrite eval_num; try easy; try lia.
            try setoid_rewrite num_subst; try setoid_rewrite eval_num; try easy; try lia.
        Unshelve. exact (fun _ => i0).
    - intros n rho. cbn.
      intros d4 H4 d3 H3 d2 H2 d1 H1 d0 H0 [H31 H53].
      epose proof (lessthen_num H4) as H4'; auto.
      epose proof (lessthen_num H3) as H3'; auto.
      epose proof (lessthen_num H2) as H2'; auto.
      epose proof (lessthen_num H1) as H1'; auto.
      epose proof (lessthen_num H0) as H0'; auto.
      clear H4 H3 H2 H1 H0.
      destruct H4' as (k4 & H4 & ->).
      destruct H3' as (k3 & H3 & ->).
      destruct H2' as (k2 & H2 & ->).
      destruct H1' as (k1 & H1 & ->).
      destruct H0' as (k0 & H0 & ->).
      apply (Disj k0).
      change (Q ⊢I ((∃∃ α)[(num k0)..] ∧ (∃∃ β)[(num k0)..])).
      apply CI.
      + apply sigma1_ternary_complete; auto.
        intros sigma. unfold I' in H31. rewrite <- !inu_I in H31. rewrite <-switch_num in H31.
        exists k1, k2.
        assert ((inu k1 .: inu k2 .: inu k3 .: inu k4 .: inu n .: rho) ⊨ α[up (up (num k0)..)][(num k2)..][(num k1)..]).
        eapply bound_ext with (N:=0).
        eapply subst_bound with (N:=1).
        eapply subst_bound with (N:=2).
        eapply subst_bound with (N:=3); auto.
        intros [|[|[|[]]]] ?; cbn; lia + solve_bounds.
        rewrite ?num_subst. apply closed_num.
        intros [|[|[]]] ?; cbn; lia + solve_bounds.
        apply closed_num.
        intros [|[]] ?; cbn; lia + solve_bounds.
        apply closed_num.
        lia.
        rewrite !sat_comp. rewrite !sat_comp in H31.
        eapply bound_ext. apply Ha1. 2 : apply H31.
        intros [|[|[]]] ?; cbn; try setoid_rewrite num_subst; try setoid_rewrite eval_num; try easy; try lia.
        1: try setoid_rewrite num_subst; try setoid_rewrite eval_num; easy.
        eapply delta1_absolutness' in H.
        rewrite !switch_nat_num in H.
        apply H.
        * eapply subst_bound with (N:=1).
          eapply subst_bound with (N:=2).
          eapply subst_bound; eauto.
          intros[|[|[]]] ?; cbn; lia + solve_bounds.
          rewrite !num_subst. apply closed_num.
          intros[|[]] ?; cbn; lia + solve_bounds. apply closed_num.
          intros[] ?; cbn; lia + solve_bounds. apply closed_num.
        * rewrite !subst_comp. now apply delta1_subst.
        * apply axioms.
        * intros ??. now apply PA_std_axioms.
      + apply sigma1_ternary_complete; auto.
        intros sigma. unfold I' in H53. rewrite <- !inu_I in H53. rewrite <-switch_num in H53.
        exists k3, k4.
        assert ((inu k1 .: inu k2 .: inu k3 .: inu k4 .: inu n .: rho) ⊨ β[up (up (num k0)..)][(num k4)..][(num k3)..]).
        eapply bound_ext with (N:=0).
        eapply subst_bound with (N:=1).
        eapply subst_bound with (N:=2).
        eapply subst_bound with (N:=3); auto.
        intros [|[|[|[]]]] ?; cbn; lia + solve_bounds.
        rewrite ?num_subst. apply closed_num.
        intros [|[|[]]] ?; cbn; lia + solve_bounds.
        apply closed_num.
        intros [|[]] ?; cbn; lia + solve_bounds.
        apply closed_num.
        lia.
        rewrite !sat_comp. rewrite !sat_comp in H53.
        eapply bound_ext. apply Hb1. 2 : apply H53.
        intros [|[|[]]] ?; cbn; lia + rewrite ?num_subst, ?eval_num; try reflexivity; try lia.
        1-3: try setoid_rewrite num_subst; try setoid_rewrite eval_num; easy.
        eapply delta1_absolutness' in H.
        rewrite !switch_nat_num in H.
        apply H.
        * eapply subst_bound with (N:=1).
          eapply subst_bound with (N:=2).
          eapply subst_bound; eauto.
          intros[|[|[]]] ?; cbn; lia + solve_bounds.
          rewrite !num_subst. apply closed_num.
          intros[|[]] ?; cbn; lia + solve_bounds. apply closed_num.
          intros[] ?; cbn; lia + solve_bounds. apply closed_num.
        * rewrite !subst_comp. now apply delta1_subst.
        * apply axioms.
        * intros ??. now apply PA_std_axioms.
    Unshelve. all: auto.
  Qed.

End Model.