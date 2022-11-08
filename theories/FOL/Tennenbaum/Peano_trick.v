From Undecidability.FOL Require Import FullSyntax.
From Undecidability.FOL.Arithmetics Require Import Signature PA DeductionFacts.
From Undecidability.FOL.Syntax Require Import Theories.
Require Import List Lia.
Import Vector.VectorNotations.
Require Import Setoid Morphisms.

Global Opaque Q.

Definition sless x y := (∃ y`[↑] == σ (x`[↑] ⊕ $0)).
Notation "x '⧀' y" := (sless x y)  (at level 40) : PA_Notation.

Fact unfold_sless x y :
  sless x y = ∃ y`[↑] == σ (x`[↑] ⊕ $0).
Proof. reflexivity. Qed.

Fact sless_subst x y s :
  (sless x y)[s] = sless (x`[s]) (y`[s]).
Proof. cbn. now rewrite !up_term. Qed.

Instance extensional_model D (I : interp D) : interp D.
Proof.
  split.
  - apply I.
  - intros [] v. exact (Vector.hd v = Vector.hd (Vector.tl v)).
Defined.


(** ** PA Models *)

Section Arithmetic.

  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  Notation "⊨ ϕ" := (forall ρ, ρ ⊨ ϕ) (at level 21).

  Variable D : Type.
  Variable I : @interp PA_funcs_signature _ D.

  Instance I' : interp D := extensional_model I.  

  Context {axioms : forall ax, PAeq ax -> ⊨ ax}.


  Notation "x 'i=' y"  := (@i_atom PA_funcs_signature PA_preds_signature D I' Eq ([x ; y])) (at level 80).
  Notation "'iσ' x" := (@i_func PA_funcs_signature PA_preds_signature D I Succ ([x])) (at level 60).
  Notation "x 'i⊕' y" := (@i_func PA_funcs_signature PA_preds_signature D I Plus ([x ; y])) (at level 62).
  Notation "x 'i⊗' y" := (@i_func PA_funcs_signature PA_preds_signature D I Mult ([x ; y])) (at level 61).
  Notation "'i0'" := (i_func (Σ_funcs:=PA_funcs_signature) (f:=Zero) []) (at level 2) : PA_Notation.

  Definition iless x y := exists d : D, y i= iσ (x i⊕ d).
  Notation "x 'i⧀' y" := (iless x y) (at level 80) : PA_Notation.

  Section inu.

    Fixpoint inu n := 
      match n with
      | 0 => i0
      | S x => iσ (inu x)
      end.
    
    Fact eval_num sigma n :
      eval sigma (num n) = inu n.
    Proof.
      induction n.
      - reflexivity.
      - cbn. now rewrite IHn.
    Qed.

    Lemma num_subst n ρ :
      (num n)`[ρ] = num n.
    Proof.
      induction n.
      - reflexivity.
      - intros. cbn. now rewrite IHn.
    Qed.

    Lemma switch_num α ρ n :
      ((inu n).:ρ) ⊨ α <-> ρ ⊨ α[(num n)..].
    Proof.
      split; intros H.
      - apply sat_single. now rewrite eval_num.
      - erewrite <-eval_num. apply sat_single, H.
    Qed.

    Lemma switch_up_num α ρ x d :
      (d.:((inu x).:ρ)) ⊨ α <-> (d.:ρ) ⊨ (α [up (num x)..]).
    Proof.
      rewrite sat_comp. apply sat_ext.
      intros [|[]]; try reflexivity.
      cbn. now rewrite num_subst, eval_num.
    Qed.
  End inu.

  Section Axioms.

    (* Provide all axioms in a more useful form *)

    Lemma iEq_refl x :
      x i= x.
    Proof.
      reflexivity.
    Qed.

    Lemma iEq_sym x y :
      x i= y -> y i= x.
    Proof.
      cbn. congruence.
    Qed.

    Lemma iEq_trans x y z :
      x i= y -> y i= z -> x i= z.
    Proof.
      cbn.
      now intros -> ->.
    Qed.

    Lemma iEq_succ x y :
      x i= y -> iσ x i= iσ y.
    Proof.
      cbn.
      now intros ->.
    Qed.

    Lemma iEq_add x y u v :
      x i= u -> y i= v -> x i⊕ y i= u i⊕ v.
    Proof.
      cbn.
      now intros -> ->.
    Qed.

    Lemma iEq_mult x y u v :
      x i= u -> y i= v -> x i⊗ y i= u i⊗ v.
    Proof.
      cbn.
      now intros -> ->.
    Qed.

    Lemma zero_succ (x : D) :
      i0 = iσ x -> False.
    Proof.
      cbn.
      assert (⊨ ax_zero_succ) as H.
      apply axioms; constructor 2.
      apply (H (fun _ => i0)).
    Qed.

    Lemma succ_inj x y : 
      iσ x = iσ y -> x = y.
    Proof.
      cbn.
      assert (⊨ ax_succ_inj ) as H.
      apply axioms; constructor 3.
      apply (H (fun _ => i0)).
    Qed.

    Lemma add_zero x :
      i0 i⊕ x = x.
    Proof.
      cbn.
      assert (⊨ ax_add_zero) as H.
      apply axioms; constructor. firstorder.
      apply (H (fun _ => i0)).
    Qed.

    Lemma add_rec x y :
      (iσ x) i⊕ y = iσ (x i⊕ y). 
    Proof.
      cbn.
      assert (⊨ ax_add_rec) as H.
      apply axioms; constructor. firstorder.
      apply (H (fun _ => i0)).
    Qed.

    Lemma mult_zero x :
      i0 i⊗ x = i0.
    Proof.
      cbn.
      assert (⊨ ax_mult_zero) as H.
      apply axioms; constructor. firstorder.
      apply (H (fun _ => i0)).
    Qed.

    Lemma mult_rec x y :
      (iσ x) i⊗ y = y i⊕ (x i⊗ y).
    Proof.
      cbn.
      assert (⊨ ax_mult_rec) as H.
      apply axioms; constructor. firstorder.
      apply (H (fun _ => i0)).
    Qed.

    Section Induction.
        
      Notation "ϕ [[ d ]] " := (forall ρ, (d.:ρ) ⊨ ϕ) (at level 19).

      Variable ϕ : form.
      Variable pred : bounded 1 ϕ.
      
      Lemma induction_0 : ϕ[[i0]] -> ⊨ ϕ[zero..].
      Proof.
        intros H0 ρ.
        apply sat_single. apply H0.
      Qed.

      Lemma induction_S :
        (forall n, ϕ[[n]] -> ϕ[[iσ n]]) -> ⊨ (∀ ϕ → ϕ[σ $0 .: S >> var]).
      Proof.
        intros IH ρ d Hd.
        eapply sat_comp, sat_ext.
        instantiate (1 := ((iσ d).:ρ)).
        intros []; now cbn.
        apply IH. intros ?.
        eapply bound_ext. apply pred. 2 : apply Hd.
        intros []; intros.
        reflexivity. lia.
      Qed.

      Theorem induction : 
        ϕ[[i0]] -> (forall n, ϕ[[n]] -> ϕ[[iσ n]] ) -> forall n, ϕ[[n]].
      Proof.
        assert (⊨ ax_induction ϕ) as H.
        apply axioms. constructor 4.
        intros ??? ρ.
        specialize (H ρ). 
        apply H.
        now apply induction_0.
        now apply induction_S.
      Qed.

    End Induction.
  End Axioms.


  Lemma succ_inj' x y : 
    iσ x = iσ y <-> x = y.
  Proof.
    split.
    - apply succ_inj.
    - now intros ->.
  Qed.

  Lemma inu_inj x y :
    inu x = inu y <-> x = y.
  Proof.
    split.
    induction x in y |-*; destruct y; auto; cbn.
    - now intros ?%zero_succ.
    - now intros H % symmetry % zero_succ.
    - now intros <-%succ_inj%IHx.
    - now intros ->.
  Qed.

  Lemma inu_add_hom x y :
    inu (x + y) = (inu x) i⊕ (inu y).
  Proof.
    induction x; cbn.
    - now rewrite add_zero.
    - setoid_rewrite add_rec. now rewrite IHx.
  Qed.

  Lemma inu_mult_hom x y :
    inu (x * y) = inu x i⊗ inu y.
  Proof.
    induction x; cbn.
    - now setoid_rewrite mult_zero.
    - setoid_rewrite inu_add_hom. rewrite IHx. now setoid_rewrite mult_rec.
  Qed.


  Lemma add_zero_r :
    forall x, x i⊕ i0 = x.
  Proof.
    pose (ϕ := $0 ⊕ zero == $0).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ?. cbn.
      apply add_zero.
    - intros x IH ρ.
      specialize (IH (fun _ => i0)); cbn in *.
      cbn in *.
      now rewrite add_rec, IH.
    - intros x. apply (H x (fun _ => i0)).
  Qed.

  Lemma mult_zero_r :
    forall x, x i⊗ i0 = i0.
  Proof.
    pose (ϕ := $0 ⊗ zero == zero).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ?. cbn. 
      apply mult_zero.
    - intros x IH ρ.
      specialize (IH (fun _ => i0)); cbn in *.
      now rewrite mult_rec, IH, add_zero.
    - intros x. apply (H x (fun _ => i0)).
  Qed.

  Lemma add_rec_r x y : 
    x i⊕ (iσ y) = iσ (x i⊕ y). 
  Proof.
    pose (ϕ := ∀ $1 ⊕ (σ $0) == σ ($1 ⊕ $0) ).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ? z. cbn.
      now rewrite !add_zero.
    - intros a IH ρ b.
      specialize (IH (fun _ => i0) b); cbn in *.
      now rewrite !add_rec, IH.
    - apply (H x (fun _ => i0) y).
  Qed.

  Lemma add_comm x y :
    x i⊕ y = y i⊕ x.
  Proof.
    pose (ϕ := ∀ $0 ⊕ $1 == $1 ⊕ $0).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ? a. cbn.
      now rewrite add_zero, add_zero_r.
    - intros a IH ρ b.
      specialize (IH (fun _ => i0) b); cbn in *.
      now rewrite add_rec, add_rec_r, IH.
    - apply (H y (fun _ => i0) x).
  Qed.

  Lemma add_asso x y z : 
    (x i⊕ y) i⊕ z = x i⊕ (y i⊕ z).
  Proof.
    pose (ϕ := ∀∀ ($2 ⊕ $1) ⊕ $0 == $2 ⊕ ($1 ⊕ $0) ).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ? b c; cbn.
      now rewrite !add_zero.
    - intros a IH ρ b c.
      specialize (IH (fun _ => i0) b c); cbn in *.
      now rewrite !add_rec, IH.
    - apply (H x (fun _ => i0) y z).
  Qed.

  Lemma mult_rec_r x y :
    x i⊗ (iσ y) = x i⊕ (x i⊗ y). 
  Proof.
    pose (phi := ∀ $1 ⊗ (σ $0) == $1 ⊕ ($1 ⊗ $0) ).
      assert (forall n rho, (n.:rho) ⊨ phi).
      apply induction. repeat solve_bounds.
      - intros ??. cbn. now rewrite !mult_zero, add_zero.
      - intros u IH rho v. cbn.
        specialize (IH (fun _ => i0) v); cbn in *.
        rewrite !mult_rec, IH, <- !add_asso.
        rewrite add_rec, <- add_rec_r. now rewrite (add_comm v).
      - now specialize (H x (fun _ => i0) y); cbn in *.
  Qed.

  Lemma mult_comm x y : 
    x i⊗ y = y i⊗ x.
  Proof.
    pose (ϕ := ∀ $0 ⊗ $1 == $1 ⊗ $0).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ? b; cbn.
      apply extensional.
      now rewrite mult_zero, mult_zero_r.
    - intros a IH ρ b.
      specialize (IH (fun _ => i0) b); cbn in *.
      rewrite extensional in *.
      now rewrite mult_rec, mult_rec_r, IH.
    - apply extensional, (H y (fun _ => i0) x).
  Qed.

  Lemma distributive x y z : 
    (x i⊕ y) i⊗ z = (x i⊗ z) i⊕ (y i⊗ z).
  Proof.
    pose (ϕ := ∀∀ ($1 ⊕ $0) ⊗ $2 == ($1 ⊗ $2) ⊕ ($0 ⊗ $2) ).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ? b c; cbn.
      apply extensional.
      now rewrite !mult_zero_r, add_zero.
    - intros a IH ρ b c.
      specialize (IH (fun _ => i0) b c); cbn in *.
      rewrite extensional in *.
      rewrite mult_rec_r, IH.
      rewrite <- add_asso, (add_comm b c), (add_asso c b).
      rewrite <- mult_rec_r.
      rewrite add_comm, <-add_asso, (add_comm _ c).
      rewrite <- mult_rec_r.
      now rewrite add_comm.
    - apply extensional, (H z (fun _ => i0) x y).
  Qed.

  Lemma mult_asso : 
    forall x y z, (x i⊗ y) i⊗ z = x i⊗ (y i⊗ z).
  Proof.
    pose (ϕ := ∀∀ ($2 ⊗ $1) ⊗ $0 == $2 ⊗ ($1 ⊗ $0) ).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ? y z; cbn.
      apply extensional.
      now rewrite !mult_zero.
    - intros x IH ρ y z.
      specialize (IH (fun _ => i0) y z); cbn in *.
      rewrite extensional in *.
      now rewrite !mult_rec, <-IH, distributive.
    - intros ???. apply extensional, (H x (fun _ => i0)).
  Qed.

  Lemma nolessthen_zero d : ~ (d i⧀ i0).
  Proof. intros [? []%extensional%zero_succ]. Qed.

  Lemma zero_or_succ :
    forall x, x = i0 \/ exists y, x = iσ y.
  Proof.
    pose (ϕ := $0 == zero ∨ ∃ $1 == σ $0).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ρ; cbn. now left; apply extensional.
    - intros x IH ρ.
      right. exists x; cbn. now apply extensional.
    - intros x.
      setoid_rewrite <-extensional.
      apply (H x (fun _ => i0)).
  Qed.

  Lemma eq_dec :
    forall x y : D, x = y \/ ~ (x = y).
  Proof.
    pose (ϕ := ∀ $1 == $0 ∨ ($1 == $0 → ⊥)).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ρ y; cbn.
      destruct (zero_or_succ y) as [|[z ->]].
      + now left; apply extensional.
      + right. rewrite extensional.
        apply zero_succ.
    - intros x IH ρ y; cbn.
      rewrite extensional.
      destruct (zero_or_succ y) as [-> | [z ->]].
      + right. intros e. eapply zero_succ.
        now rewrite e.
      + destruct (IH (fun _ => i0) z); cbn in H.
        * left. rewrite extensional in H; now rewrite H.
        * right. intros ?%succ_inj%extensional. auto.
    - intros x y. rewrite <-extensional.
      apply (H x (fun _ => i0) y).
  Qed.

  Lemma sum_is_zero :
    forall x y, x i⊕ y = i0 -> x = i0 /\ y = i0.
  Proof.
    intros x y H.
    destruct (zero_or_succ x) as [? |[x' Ex]], (zero_or_succ y) as [? |[y' Ey]]; split; auto.
    - exfalso. rewrite Ey, add_rec_r in H.
      eapply zero_succ. now rewrite H.
    - exfalso. rewrite Ex, add_rec in H.
      eapply zero_succ. now rewrite H.
    - exfalso. rewrite Ey, add_rec_r in H.
      eapply zero_succ. now rewrite H.
    - exfalso. rewrite Ex, add_rec in H.
      eapply zero_succ. now rewrite H.
  Qed.


  Lemma lt_SS x y : 
    (iσ x) i⧀ (iσ y) <-> x i⧀ y.
  Proof.
    split; intros [k Hk]; exists k.
    - apply extensional, succ_inj in Hk. 
      now rewrite extensional, <-add_rec.
    - rewrite extensional in *.
      now rewrite Hk, add_rec.
  Qed.

  Lemma trichotomy x y :
    x i⧀ y \/ x = y \/ y i⧀ x.
  Proof.
    pose (ϕ := ∀ ($1 ⧀ $0) ∨ ($1 == $0 ∨ $0 ⧀ $1)).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ρ d; cbn.
      setoid_rewrite extensional. 
      destruct (zero_or_succ d) as [-> | [k Ek] ].
      + now right; left.
      + left. exists k. now rewrite add_zero.
    - intros n IH ρ d.
      destruct (zero_or_succ d) as [? | [k Hk] ].
      + right; right. exists n; cbn.
        apply extensional.
        now rewrite H, add_zero.
      + specialize (IH (fun _ => i0) k); cbn in *.
        change ((iσ n) i⧀ d \/ iσ n i= d \/ d i⧀ (iσ n)).
        rewrite Hk, !lt_SS. 
        destruct IH as [IH|[IH|IH]]; auto.
        rewrite extensional in *.
        rewrite IH. intuition.
    - rewrite <-extensional.
      apply (H x (fun _ => i0) y).
  Qed.

  Lemma add_eq :
    forall x y z, x i⊕ z = y i⊕ z -> x = y.
  Proof.
    pose (ϕ := ∀∀ $0 ⊕ $2 == $1 ⊕ $2 → $0 == $1 ).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ???; cbn. now rewrite !add_zero_r.
    - intros z IH ρ y x; cbn in *.
      intros H. apply extensional.
      rewrite !add_rec_r, <-!add_rec in H.
      apply succ_inj. apply extensional, IH; auto.
    - intros x y z. rewrite <-!extensional.
      apply (H z (fun _ => i0) y x).
  Qed.

  Lemma lt_neq x y : 
    x i⧀ y -> x = y -> False.
  Proof.
    intros [k Hk] e. revert Hk.
    rewrite extensional.
    rewrite e, <-add_rec_r.
    rewrite <-(add_zero_r y) at 1.
    rewrite !(add_comm y).
    intros H%add_eq. revert H.
    apply zero_succ.
  Qed.

  Definition ileq x y := exists d : D, y i= x i⊕ d.
  Notation "x 'i≤' y" := (ileq x y)  (at level 80).

  Lemma lt_le_equiv1 x y : 
    x i⧀ iσ y <-> x i≤ y.
  Proof.
    split; intros [k Hk].
    - exists k. 
      rewrite extensional in *.
      now apply succ_inj in Hk.
    - exists k. now apply iEq_succ.
  Qed.


  Lemma lt_S d e : 
    d i⧀ (iσ e) <-> d i⧀ e \/ d = e.
  Proof.
    pose (Φ := ∀ $0 ⧀ σ $1 ↔ $0 ⧀ $1 ∨ $0 == $1).
    assert (H: forall d ρ, (d .: ρ)⊨ Φ).
    apply induction.
    - solve_bounds.
    - intros ρ x; cbn; setoid_rewrite extensional. 
      destruct (zero_or_succ x) as [E | [x' E]]; cbn; split.
      + intros _. now right.
      + intros _. exists i0.
        now rewrite E, add_zero.
      + setoid_rewrite <-extensional.
        change (x i⧀ iσ i0 -> x i⧀ i0 \/ x i= i0).
        rewrite E, lt_SS.
        now intros ?%nolessthen_zero.
      + setoid_rewrite <-extensional.
        intros [?%nolessthen_zero | e']. tauto.
        rewrite extensional in *.
        rewrite e' in E. now apply zero_succ in E.
    - intros y IH ρ x; cbn.
      destruct (zero_or_succ x) as [E | [x' E]].
      + split.
        * intros _. left. exists y.
          now rewrite extensional, E, add_zero.
        * intros _. exists (iσ y).
          now rewrite extensional, E, add_zero.
      + change ((x i⧀ iσ iσ y) <-> x i⧀ iσ y \/ x i= iσ y).
        rewrite E, !lt_SS. rewrite extensional, succ_inj'.
        specialize (IH ρ x'). 
        rewrite <-extensional. apply IH.
    - specialize (H e (fun _ => d) d). 
      rewrite <-extensional. apply H.
  Qed.

  Lemma lt_le_trans {x z} y : 
    x i⧀ y -> y i≤ z -> x i⧀ z.
  Proof.
    intros [k1 H1] [k2 H2]. exists (k1 i⊕ k2). 
    rewrite extensional in *. rewrite H2, H1.
    now rewrite add_rec, add_asso.
  Qed.

  Lemma le_le_trans {x z} y :
    x i≤ y -> y i≤ z -> x i≤ z.
  Proof.
    intros [k1 H1] [k2 H2]. exists (k1 i⊕ k2). 
    rewrite extensional in *. rewrite H2, H1.
    now rewrite add_asso.
  Qed.

  Lemma add_lt_mono x y t : 
    x i⧀ y -> x i⊕ t i⧀ y i⊕ t.
  Proof.
    intros [k Hk]. exists k. 
    rewrite extensional in *. rewrite Hk.
    now rewrite add_rec, !add_asso, (add_comm k t).
  Qed.

  Lemma add_le_mono x y t : 
    x i≤ y -> x i⊕ t i≤ y i⊕ t.
  Proof.
    intros [k Hk]. exists k. 
    rewrite extensional in *. rewrite Hk.
    now rewrite !add_asso, (add_comm k t).
  Qed.

  Lemma mult_le_mono x y t : 
    x i≤ y -> x i⊗ t i≤ y i⊗ t.
  Proof.
    intros [k Hk]. exists (k i⊗ t). 
    rewrite extensional in *. rewrite Hk.
    now rewrite distributive. 
  Qed.



  Section Euclid.

      (** *** Euclidean Lemma *)

      Lemma iEuclid :
        forall x q, exists d r, x i= d i⊗ q i⊕ r /\ (i0 i⧀ q -> r i⧀ q).
      Proof.
        intros x q.
        destruct (zero_or_succ q) as [E | [q_ Eq_]].
        - exists i0, x. split.
          + rewrite mult_zero, add_zero. 
            apply iEq_refl.
          + rewrite E. now intros ?%nolessthen_zero.
        - pose (ϕ := ∀∃∃ $3 == $1 ⊗ (σ $2) ⊕ $0 ∧ (zero ⧀ (σ $2) → $0 ⧀ (σ $2) ) ).
          assert (forall n ρ, (n.:ρ) ⊨ ϕ).
          apply induction. unfold sless in *. cbn. cbn in *. repeat solve_bounds.
          + intros ρ d. exists i0, i0; cbn. split.
            * now rewrite extensional, mult_zero, add_zero.
            * tauto.
          + intros x' IH ρ q'. cbn.
            destruct (IH ρ q') as [d' [r' [H ]]]. cbn in *.
            destruct (eq_dec r' q') as [e1|e2].
            * exists (iσ d'), i0; cbn. split; [|tauto].
              rewrite extensional in *.
              rewrite add_zero_r, H.
              now rewrite e1, <-add_rec_r, mult_rec, add_comm.
            * exists d', (iσ r'); cbn. split.
              { rewrite extensional in *.
                now rewrite H, <-add_rec_r. }
              intros _. apply lt_SS.
              assert (r' i≤ q') as G.
              { rewrite <-lt_le_equiv1.
                apply H0. exists q'. 
                rewrite extensional.
                now rewrite add_zero. }
              destruct (trichotomy r' q') as [h|[h|h]]; intuition.
              exfalso. 
              apply (@lt_neq q' q'); [|reflexivity]. eapply lt_le_trans; eauto.
          + destruct (H x (fun _ => i0) q_) as [d [r [H1 H2]]]. cbn in H1, H2.
            exists d, r. split; rewrite Eq_; auto.
      Qed.

      Lemma iFac_unique1 d q1 r1 q2 r2 : 
        r1 i⧀ d ->
        r1 i⊕ q1 i⊗ d = r2 i⊕ q2 i⊗ d -> 
        q1 i⧀ q2 -> False.
      Proof.
        intros H1 E H. revert E.
        apply lt_neq.
        apply lt_le_trans with (d i⊕ q1 i⊗ d).
        - now apply add_lt_mono.
        - rewrite <-mult_rec.
          apply le_le_trans with (q2 i⊗ d).
          + apply mult_le_mono.
            destruct H as [k Hk].
            exists k. now rewrite add_rec.
          + rewrite <-(add_zero (q2 i⊗ d)) at 1.
            apply add_le_mono.
            exists r2. 
            now rewrite extensional, add_zero.
      Qed.


      (** Uniqueness for the Euclidean Lemma *)
      
      Lemma iFac_unique q d1 r1 d2 r2 : 
            r1 i⧀ q -> r2 i⧀ q ->
            r1 i⊕ d1 i⊗ q = r2 i⊕ d2 i⊗ q -> 
            d1 = d2 /\ r1 = r2.
      Proof.
        intros H1 H2 E1.
        assert (d1 = d2) as E2.
        - destruct (trichotomy d1 d2) as [|[|]]; auto; exfalso.
          + eapply iFac_unique1.
            2: apply E1. all: tauto.
          + eapply iFac_unique1.
            2: symmetry; apply E1. all: auto.
        - rewrite E2 in E1.
          now apply add_eq in E1.
      Qed.


    End Euclid. 



    Lemma lessthen_num : 
      forall n d, d i⧀ inu n -> exists k, k < n /\ d = inu k.
    Proof.
      induction n ; intros d H.
      - now apply nolessthen_zero in H.
      - destruct (zero_or_succ d) as [E | [e E]].
        1 : exists 0; split; auto; lia.
        cbn in H. rewrite E, lt_SS in H.
        apply IHn in H.
        destruct H as [k [? E']].
        exists (S k); split; try lia. 
        cbn; now rewrite <-E'.
    Qed.


    Lemma iEuclid' :
      forall x y, 0 < y -> exists a b, b < y /\ x = a i⊗ inu y i⊕ inu b.
      Proof.
        intros x y.
        destruct y as [|y]. lia.
        destruct (iEuclid x (inu (S y))) as (a & b & H).
        intros Hy.
        enough (Hlt : forall x y, x < y -> inu x i⧀ inu y).
        - apply Hlt, H, lessthen_num in Hy.
          destruct Hy as [r [Hr E]].
          exists a, r. split.
          + apply Hr.
          + rewrite <-E. apply extensional, H.
        - intros n m Hnm.
          exists (inu (m - S n)); cbn.
          rewrite <-inu_add_hom, extensional.
          replace (m) with (S n + (m - S n)) at 1 by lia.
          reflexivity.
      Qed.

End Arithmetic.


(** *** Standard Model of PA *)

Section StandartModel.

  Definition interp_nat : interp nat.
  Proof.
    split.
    - destruct f; intros v.
      + exact 0.
      + exact (S (Vector.hd v) ).
      + exact (Vector.hd v + Vector.hd (Vector.tl v) ).
      + exact (Vector.hd v * Vector.hd (Vector.tl v) ).
    - destruct P; intros v.
      exact (Vector.hd v = Vector.hd (Vector.tl v)).
  Defined.

  (* We now show that there is a model in which all of PA's axioms hold. *)
  Lemma PA_std_axioms :
    forall rho ax, PA ax -> sat interp_nat rho ax. 
  Proof.
    intros rho ax [a H | | | ].
    repeat (destruct H as [<-| H]); cbn ; try congruence.
    - firstorder.
    - cbn; lia.
    - cbn; intros ??; lia.
    - intros H1 IH. intros d. induction d.
      + apply sat_single in H1. apply H1.
      + apply IH in IHd. 
        eapply sat_comp, sat_ext in IHd.
        apply IHd. intros []; now cbn.
  Qed.

  Lemma Q_std_axioms :
    forall rho ax, In ax Q -> @sat _ _ nat interp_nat _ rho ax. 
  Proof.
    intros rho ax H.
    repeat (destruct H as [<-| H]); cbn ; try congruence.
    - intros []; auto. right. exists n; auto. 
    - destruct H.
  Qed.

  Fact inu_nat_id : forall n, @inu nat interp_nat n = n.
  Proof.
    induction n; cbn; congruence.
  Qed.

End StandartModel.


Definition std {D I} d := exists n, @inu D I n = d.
Definition stdModel D {I} := forall d, exists n, (@inu D I) n = d.
Definition nonStd D {I} := exists e, ~ @std D I e.
Definition notStd D {I} := ~ @stdModel D I.
