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


(** ** PA Models *)

Section Arithmetic.

  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  Notation "⊨ ϕ" := (forall ρ, ρ ⊨ ϕ) (at level 21).

  Variable D : Type.
  Variable I : @interp PA_funcs_signature _ D.
  Context {axioms : forall ax, PAeq ax -> ⊨ ax}.

  Check @i_func.

  Definition iEq x y := @i_atom PA_funcs_signature PA_preds_signature D I Eq ([x ; y]).
  Definition iSucc x := @i_func PA_funcs_signature PA_preds_signature D I Succ ([x]).
  Definition iPlus x y := @i_func PA_funcs_signature PA_preds_signature D I Plus ([x ; y]).
  Definition iMult x y := @i_func PA_funcs_signature PA_preds_signature D I Mult ([x ; y]).

  Notation "x 'i=' y" := (iEq x y) (at level 80) : PA_Notation.
  Notation "'iσ' x" := (iSucc x) (at level 70) : PA_Notation.
  Notation "x 'i⊕' y" := (iPlus x y) (at level 72) : PA_Notation.
  Notation "x 'i⊗' y" := (iMult x y) (at level 71) : PA_Notation.
  Notation "'i0'" := (i_func (Σ_funcs:=PA_funcs_signature) (f:=Zero) []) (at level 2) : PA_Notation.


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
      assert (⊨ ax_refl) as H.
      apply axioms; constructor; firstorder.
      apply (H (fun _ => i0)).
    Qed.

    Lemma iEq_sym x y :
      x i= y -> y i= x.
    Proof.
      assert (⊨ ax_sym) as H.
      apply axioms; constructor; firstorder.
      apply (H (fun _ => i0)).
    Qed.

    Lemma iEq_trans x y z :
      x i= y -> y i= z -> x i= z.
    Proof.
      assert (⊨ ax_trans) as H.
      apply axioms; constructor; firstorder.
      apply (H (fun _ => i0)).
    Qed.

    Lemma iEq_succ x y :
      x i= y -> iσ x i= iσ y.
    Proof.
      assert (⊨ ax_succ_congr).
      apply axioms; constructor; firstorder.
      apply (H (fun _ => i0)).
    Qed.

    Lemma iEq_add x y u v :
      x i= u -> y i= v -> x i⊕ y i= u i⊕ v.
    Proof.
      assert (⊨ ax_add_congr).
      apply axioms; constructor; firstorder.
      apply (H (fun _ => i0)).
    Qed.

    Lemma iEq_mult x y u v :
      x i= u -> y i= v -> x i⊗ y i= u i⊗ v.
    Proof.
      assert (⊨ ax_mult_congr).
      apply axioms; constructor; firstorder.
      apply (H (fun _ => i0)).
    Qed.

    Lemma zero_succ (x : D) :
      i0 i= iσ x -> False.
    Proof.
      assert (⊨ ax_zero_succ) as H.
      apply axioms; constructor 2.
      apply (H (fun _ => i0)).
    Qed.

    Lemma succ_inj x y : 
      iσ x i= iσ y -> x i= y.
    Proof.
      assert (⊨ ax_succ_inj ) as H.
      apply axioms; constructor 3.
      apply (H (fun _ => i0)).
    Qed.

    Lemma add_zero x :
      i0 i⊕ x i= x.
    Proof.
      assert (⊨ ax_add_zero) as H.
      apply axioms; constructor. firstorder.
      apply (H (fun _ => i0)).
    Qed.

    Lemma add_rec x y :
      (iσ x) i⊕ y i= iσ (x i⊕ y). 
    Proof.
      assert (⊨ ax_add_rec) as H.
      apply axioms; constructor. firstorder.
      apply (H (fun _ => i0)).
    Qed.

    Lemma mult_zero x :
      i0 i⊗ x i= i0.
    Proof.
      assert (⊨ ax_mult_zero) as H.
      apply axioms; constructor. firstorder.
      apply (H (fun _ => i0)).
    Qed.

    Lemma mult_rec x y :
      (iσ x) i⊗ y i= y i⊕ (x i⊗ y).
    Proof.
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

  (*  Register iEq as an equivalence relation and artihmetical operations
      as morphism respecting this equivalence, to enable easy rewriting. 
    *)
  Instance equiv_iEq:
    Equivalence (iEq).
  Proof.
    split.
    - intros ?  ; now apply iEq_refl.
    - intros ?? ; now apply iEq_sym.
    - intros ???; now apply iEq_trans.
  Defined.

  Instance proper_succ :
    Proper (iEq ==> iEq) iSucc.
  Proof.
    intros ??; now apply iEq_succ.
  Defined.

  Instance proper_add :
    Proper (iEq ==> iEq ==> iEq) iPlus.
  Proof.
    intros ?????; now apply iEq_add.
  Defined.

  Instance proper_mult :
    Proper (iEq ==> iEq ==> iEq) iMult.
  Proof.
    intros ?????; now apply iEq_mult.
  Defined.

  Lemma inu_inj x y :
    inu x i= inu y <-> x = y.
  Proof.
    split.
    induction x in y |-*; destruct y; auto; cbn.
    - now intros ?%zero_succ.
    - now intros H % iEq_sym % zero_succ.
    - now intros <-%succ_inj%IHx.
    - intros ->. reflexivity.
  Qed.

  Lemma inu_add_hom x y :
    inu (x + y) i= (inu x) i⊕ (inu y).
  Proof.
    induction x; cbn.
    - now rewrite add_zero.
    - rewrite add_rec. now rewrite IHx.
  Qed.

  Lemma inu_mult_hom x y :
    inu (x * y) i= inu x i⊗ inu y.
  Proof.
    induction x; cbn.
    - now rewrite mult_zero.
    - now rewrite inu_add_hom, IHx, mult_rec.
  Qed.


  Local Ltac Fold :=
    cbn; repeat
    match goal with
    | H : context [ @i_atom _ _ D I Eq ([?x ; ?y]) ] |- _
      => change (@i_atom _ _ D I Eq ([x ; y])) with (iEq x y) in H
    | |- context [ @i_atom _ _ D I Eq ([?x ; ?y]) ]
      => change (@i_atom _ _ D I Eq ([x ; y])) with (iEq x y)

    | H : context [ @i_func _ _ D I Succ ([?x]) ] |- _ 
      => change (@i_func _ _ D I Succ ([x])) with (iSucc x) in H
    | |- context [ @i_func _ _ D I Succ ([?x]) ]
      => change (@i_func _ _ D I Succ ([x])) with (iSucc x)
    
    | H : context [ @i_func _ _ D I Plus ([?x ; ?y]) ] |- _
      => change (@i_func _ _ D I Plus ([x ; y])) with (iPlus x y) in H
    | |- context [ @i_func _ _ D I Plus ([?x ; ?y]) ] 
      => change (@i_func _ _ D I Plus ([x ; y])) with (iPlus x y)
    
    | H : context [ @i_func _ _ D I Mult ([?x ; ?y]) ] |- _
      => change (@i_func _ _ D I Mult ([x ; y])) with (iMult x y) in H
    | |- context [ @i_func _ _ D I Mult ([?x ; ?y]) ]
      => change (@i_func _ _ D I Mult ([x ; y])) with (iMult x y)
    end.


  Lemma add_zero_r :
    forall x, x i⊕ i0 i= x.
  Proof.
    pose (ϕ := $0 ⊕ zero == $0).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ?. cbn. Fold.
      apply add_zero.
    - intros x IH ρ.
      specialize (IH (fun _ => i0)); cbn in *.
      Fold. now rewrite add_rec, IH.
    - intros x. apply (H x (fun _ => i0)).
  Qed.

  Lemma mult_zero_r :
    forall x, x i⊗ i0 i= i0.
  Proof.
    pose (ϕ := $0 ⊗ zero == zero).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ?. cbn. apply mult_zero.
    - intros x IH ρ.
      specialize (IH (fun _ => i0)); cbn in *.
      Fold. now rewrite mult_rec, IH, add_zero.
    - intros x. apply (H x (fun _ => i0)).
  Qed.

  Lemma add_rec_r x y : 
    x i⊕ (iσ y) i= iσ (x i⊕ y). 
  Proof.
    pose (ϕ := ∀ $1 ⊕ (σ $0) == σ ($1 ⊕ $0) ).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ? z. Fold.
      now rewrite !add_zero.
    - intros a IH ρ b.
      specialize (IH (fun _ => i0) b); cbn in *.
      Fold. now rewrite !add_rec, IH.
    - apply (H x (fun _ => i0) y).
  Qed.

  Lemma add_comm x y :
    x i⊕ y i= y i⊕ x.
  Proof.
    pose (ϕ := ∀ $0 ⊕ $1 == $1 ⊕ $0).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ? a. Fold.
      now rewrite add_zero, add_zero_r.
    - intros a IH ρ b.
      specialize (IH (fun _ => i0) b); cbn in *.
      Fold. now rewrite add_rec, add_rec_r, IH.
    - apply (H y (fun _ => i0) x).
  Qed.

  Lemma add_asso x y z : 
    (x i⊕ y) i⊕ z i= x i⊕ (y i⊕ z).
  Proof.
    pose (ϕ := ∀∀ ($2 ⊕ $1) ⊕ $0 == $2 ⊕ ($1 ⊕ $0) ).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ? b c. Fold.
      now rewrite !add_zero.
    - intros a IH ρ b c.
      specialize (IH (fun _ => i0) b c); cbn in *.
      Fold. now rewrite !add_rec, IH.
    - apply (H x (fun _ => i0) y z).
  Qed.

  Lemma mult_rec_r x y :
    x i⊗ (iσ y) i= x i⊕ (x i⊗ y). 
  Proof.
    pose (ϕ := ∀ $1 ⊗ (σ $0) == $1 ⊕ ($1 ⊗ $0) ).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ? b. Fold.
      now rewrite !mult_zero, add_zero.
    - intros a IH ρ b. cbn.
      specialize (IH (fun _ => i0) b); cbn in *.
      Fold.
      rewrite !mult_rec, IH, <- !add_asso.
      rewrite add_rec, <- add_rec_r. 
      now rewrite (add_comm b).
    - apply (H x (fun _ => i0) y).
  Qed.

  Lemma mult_comm x y : 
    x i⊗ y i= y i⊗ x.
  Proof.
    pose (ϕ := ∀ $0 ⊗ $1 == $1 ⊗ $0).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ? b; Fold.
      now rewrite mult_zero, mult_zero_r.
    - intros a IH ρ b.
      specialize (IH (fun _ => i0) b); cbn in *.
      Fold. now rewrite mult_rec, mult_rec_r, IH.
    - apply (H y (fun _ => i0) x).
  Qed.

  Lemma distributive x y z : 
    (x i⊕ y) i⊗ z i= (x i⊗ z) i⊕ (y i⊗ z).
  Proof.
    pose (ϕ := ∀∀ ($1 ⊕ $0) ⊗ $2 == ($1 ⊗ $2) ⊕ ($0 ⊗ $2) ).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ? b c; Fold.
      now rewrite !mult_zero_r, add_zero.
    - intros a IH ρ b c.
      specialize (IH (fun _ => i0) b c); cbn in *.
      Fold.
      rewrite mult_rec_r, IH.
      rewrite <- add_asso, (add_comm b c), (add_asso c b).
      rewrite <- mult_rec_r.
      rewrite add_comm, <-add_asso, (add_comm _ c).
      rewrite <- mult_rec_r.
      now rewrite add_comm.
    - apply (H z (fun _ => i0) x y).
  Qed.

  Lemma mult_asso : 
    forall x y z, (x i⊗ y) i⊗ z i= x i⊗ (y i⊗ z).
  Proof.
    pose (ϕ := ∀∀ ($2 ⊗ $1) ⊗ $0 == $2 ⊗ ($1 ⊗ $0) ).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ? y z; Fold.
      now rewrite !mult_zero.
    - intros x IH ρ y z.
      specialize (IH (fun _ => i0) y z); cbn in *.
      Fold. now rewrite !mult_rec, <-IH, distributive.
    - intros x. apply (H x (fun _ => i0)).
  Qed.

  Notation "x 'i⧀' y" := (exists d : D, y i= iσ (x i⊕ d) ) (at level 40).

  Lemma nolessthen_zero d : ~ d i⧀ i0.
  Proof. intros [? []%zero_succ]. Qed.

  Lemma zero_or_succ :
    forall x, x i= i0 \/ exists y, x i= iσ y.
  Proof.
    pose (ϕ := $0 == zero ∨ ∃ $1 == σ $0).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ρ; Fold. now left.
    - intros x IH ρ.
      right. exists x; now Fold.
    - intros x. apply (H x (fun _ => i0)).
  Qed.

  Lemma eq_dec :
    forall x y : D, x i= y \/ ~ (x i= y).
  Proof.
    pose (ϕ := ∀ $1 == $0 ∨ ($1 == $0 → ⊥)).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ρ y. Fold.
      destruct (zero_or_succ y) as [|[z ->]].
      + now left.
      + right. apply zero_succ.
    - intros x IH ρ y. Fold.
      destruct (zero_or_succ y) as [-> | [z ->]].
      + right. intros e. eapply zero_succ.
        now rewrite e.
      + destruct (IH (fun _ => i0) z); cbn in H.
        * left. Fold. now rewrite H.
        * right. intros ?%succ_inj. auto.
    - intros x y. apply (H x (fun _ => i0) y).
  Qed.

  Lemma sum_is_zero : 
    forall x y, x i⊕ y i= i0 -> x i= i0 /\ y i= i0.
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

  
  Lemma lt_SS x y : (iσ x) i⧀ (iσ y) <-> x i⧀ y.
  Proof.
    split; intros [k Hk]; exists k.
    - apply succ_inj in Hk. now rewrite <-add_rec.
    - now rewrite Hk, add_rec. 
  Qed.

  Lemma trichotomy x y : x i⧀ y \/ x = y \/ y i⧀ x.
  Proof.
    pose (ϕ := ∀ ($1 ⧀ $0) ∨ ($1 == $0 ∨ $0 ⧀ $1)).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ρ d; Fold. 
      destruct (zero_or_succ d) as [-> | [k Ek] ].
      + now right; left.
      + left. exists k; Fold. now rewrite add_zero.
    - intros n IH ρ d. Fold.
      destruct (zero_or_succ d) as [? | [k Hk] ].
      + right; right. exists n; Fold.
        now rewrite H, add_zero.
      + specialize (IH (fun _ => i0) k); cbn in *.
        Fold.
        rewrite !lt_SS. intuition congruence. 
    - now specialize (H x (fun _ => i0) y); cbn in H.
  Qed.



  Lemma add_eq x y t : x i⊕ t = y i⊕ t -> x = y.
  Proof.
    pose (ϕ := ∀∀ $0 ⊕ $2 == $1 ⊕ $2 ~> $0 == $1  ).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ???. cbn. now rewrite !add_zero_r.
    - intros T IH ρ Y X; cbn in *.
      rewrite !add_rec_r, <-!add_rec.
      now intros ?%IH%succ_inj.
    - now specialize (H t (fun _ => i0) y x); cbn in *.
  Qed.


  Lemma lt_neq x y : x i⧀ y -> x = y -> False.
  Proof.
    intros [k Hk] ->. revert Hk.
    rewrite <-add_rec_r, <-(add_zero_r y) at 1.
    rewrite !(add_comm y).
    intros H%add_eq. revert H.
    apply zero_succ.
  Qed.


  Notation "x 'i≤' y" := (exists d : D, y = x i⊕ d)  (at level 40).

  Lemma lt_le_equiv1 x y : x i⧀ iσ y <-> x i≤ y.
  Proof.
    split; intros [k Hk].
    - exists k. now apply succ_inj in Hk.
    - exists k. congruence.
  Qed.



  Lemma lt_S d e : d i⧀ (iσ e) <-> d i⧀ e \/ d = e.
  Proof.
    pose (Φ := ∀ $0 ⧀ σ $1 <~> $0 ⧀ $1 ∨ $0 == $1).
    assert (H: forall d ρ, (d .: ρ)⊨ Φ).
    apply induction.
    repeat solve_bounds; cbn in H.
    1,2 : apply vec_cons_inv in H; destruct H as [-> |]; solve_bounds.
    - intros ρ x. cbn; destruct (zero_or_succ x) as [-> | [x' ->]]; cbn; split.
      + intros _. now right.
      + intros _. exists i0. now rewrite add_zero.
      + rewrite lt_SS. now intros ?%nolessthen_zero.
      + intros [?%nolessthen_zero | E]. tauto.
        symmetry in E. now apply zero_succ in E.
    - intros y IH ρ x; cbn; destruct (zero_or_succ x) as [-> | [x' ->]].
      + split.
      ++ intros _. left. exists y. now rewrite add_zero.
      ++ intros _. exists (iσ y). now rewrite add_zero.
      + rewrite !lt_SS, !succ_inj'.
        specialize (IH ρ x'). apply IH.
    - specialize (H e (fun _ => d) d). apply H.
  Qed.

  Lemma lt_le_trans {x z} y : x i⧀ y -> y i≤ z -> x i⧀ z.
  Proof.
    intros [k1 H1] [k2 H2]. exists (k1 i⊕ k2). rewrite H2, H1.
    now rewrite add_rec, add_asso.
  Qed.

  Lemma le_le_trans {x z} y : x i≤ y -> y i≤ z -> x i≤ z.
  Proof.
    intros [k1 H1] [k2 H2]. exists (k1 i⊕ k2). rewrite H2, H1.
    now rewrite add_asso.
  Qed.

  Lemma add_lt_mono x y t : x i⧀ y -> x i⊕ t i⧀ y i⊕ t.
  Proof.
    intros [k Hk]. exists k. rewrite Hk.
    now rewrite add_rec, !add_asso, (add_comm k t).
  Qed.

  Lemma add_le_mono x y t : x i≤ y -> x i⊕ t i≤ y i⊕ t.
  Proof.
    intros [k Hk]. exists k. rewrite Hk.
    now rewrite !add_asso, (add_comm k t).
  Qed.

  Lemma mult_le_mono x y t : x i≤ y -> x i⊗ t i≤ y i⊗ t.
  Proof.
    intros [k Hk]. exists (k i⊗ t). rewrite Hk.
    now rewrite distributive. 
  Qed.



  Section Euclid.

      (** *** Euclidean Lemma *)

      Lemma iEuclid : 
        forall x q, exists d r, x = d i⊗ q i⊕ r /\ (i0 i⧀ q -> r i⧀ q).
      Proof.
        intros x q.
        destruct (zero_or_succ q) as [-> | [q_ ->]].
        - exists i0, x. split.
          + rewrite mult_zero, add_zero. reflexivity.
          + now intros ?%nolessthen_zero.
        - pose (ϕ := ∀∃∃ $3 == $1 ⊗ (σ $2) ⊕ $0 ∧ (zero ⧀ (σ $2) ~> $0 ⧀ (σ $2) ) ).
          assert (forall n ρ, (n.:ρ) ⊨ ϕ).
          apply induction. unfold sless in *. cbn. cbn in *. repeat solve_bounds.
          + intros ρ d. cbn. exists i0, i0. fold i0. split.
            * now rewrite mult_zero, add_zero.
            * tauto.
          + intros x' IH ρ q'. cbn.
            destruct (IH ρ q') as [d' [r' [H ]]]. cbn in *.
            destruct (eq_dec r' q') as [<- | F].
            * exists (iσ d'), i0. split.
              rewrite add_zero_r, H.
              now rewrite <-add_rec_r, mult_rec, add_comm.
              tauto.
            * exists d', (iσ r'). split.
              now rewrite H, <-add_rec_r.
              intros _. rewrite lt_SS.
              assert (r' i≤ q') as G.
              { rewrite <-lt_le_equiv1.
                apply H0. exists q'. now rewrite add_zero. }
              destruct (trichotomy r' q') as [h |[h|h] ]; intuition.
              exfalso. specialize (lt_le_trans _ h G).
              intros. now apply (lt_neq q' q').
          + destruct (H x (fun _ => i0) q_) as [d [r [H1 H2]]]. cbn in H1, H2.
            exists d, r. split; auto.
      Qed.

      Lemma iFac_unique1 d q1 r1 q2 r2 : r1 i⧀ d ->
            r1 i⊕ q1 i⊗ d = r2 i⊕ q2 i⊗ d -> q1 i⧀ q2 -> False.
      Proof.
        intros H1 E H. revert E. apply lt_neq.
        apply lt_le_trans with (d i⊕ q1 i⊗ d).
        - now apply add_lt_mono.
        - rewrite <- !mult_rec.
          apply le_le_trans with (q2 i⊗ d).
          + apply mult_le_mono.
            destruct H as [k ->].
            exists k. now rewrite add_rec.
          + pattern (q2 i⊗ d) at 2.
            rewrite <-(add_zero (q2 i⊗ d)).
            apply add_le_mono.
            exists r2. now rewrite add_zero.
      Qed.


      (** Uniqueness for the Euclidean Lemma *)
      
      Lemma iFac_unique q d1 r1 d2 r2 : r1 i⧀ q -> r2 i⧀ q ->
            r1 i⊕ d1 i⊗ q = r2 i⊕ d2 i⊗ q -> d1 = d2 /\ r1 = r2.
      Proof.
        intros H1 H2 E.
        assert (d1 = d2) as ->.
        - destruct (trichotomy d1 d2) as [ H | [ | H ]]; auto.
          + exfalso. eapply iFac_unique1. 2: apply E. all: tauto.
          + exfalso. eapply iFac_unique1. symmetry in E.
            3: apply H. apply H2. eauto.
        - repeat split. now apply add_eq in E.
      Qed.


    End Euclid. 



    Lemma lessthen_num : forall n d, d i⧀ inu n -> exists k, k < n /\ d = inu k.
    Proof.
      induction n ; intros d H.
      - now apply nolessthen_zero in H.
      - destruct (zero_or_succ d) as [-> | [e ->]].
        exists 0; split; auto; lia.
        cbn in H; apply ->lt_SS in H.
        apply IHn in H.
        destruct H as [k []].
        exists (S k); split. lia. cbn; congruence.
    Qed.


    Lemma iEuclid' : forall x y, 0 < y -> exists a b, b < y /\ x = a i⊗ inu y i⊕ inu b.
      Proof.
        intros x y.
        destruct y as [|y]. lia.
        destruct (iEuclid x (inu (S y))) as (a & b & H).
        intros Hy.
        enough (Hlt : forall x y, x < y -> inu x i⧀ inu y).
        apply Hlt, H, lessthen_num in Hy.
        destruct Hy as [r [Hr ->]].
        exists a, r. split.
        apply Hr. apply H.
        intros n m [k <-]%lt_nat_equiv.
        exists (inu k); cbn. now rewrite inu_add_hom.
      Qed.

  End PA_Model.


End Models.