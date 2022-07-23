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

  Definition iEq x y := i_atom (P:=Eq) ([x ; y]).
  Definition iSucc x := i_func (f:=Succ) ([x]).
  Definition iPlus x y := i_func (f:=Plus) ([x ; y]).
  Definition iMult x y := i_func (f:=Mult) ([x ; y]).

  Notation "x 'i=' y" := (iEq x y) (at level 40) : PA_Notation.
  Notation "'i0'" := (i_func (Σ_funcs:=PA_funcs_signature) (f:=Zero) []) (at level 2) : PA_Notation.
  Notation "'iσ' x" := (iSucc x) (at level 37) : PA_Notation.
  Notation "x 'i⊕' y" := (iPlus x y) (at level 39) : PA_Notation.
  Notation "x 'i⊗' y" := (iMult x y) (at level 39) : PA_Notation.


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
    Equivalence iEq.
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

  Lemma add_zero_r :
    forall x, x i⊕ i0 i= x.
  Proof.
    pose (ϕ := $0 ⊕ zero == $0). 
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ?. cbn. apply add_zero.
    - intros x IH ρ.
      specialize (IH (fun _ => i0)). cbn.
      change (iσ x i⊕ i0 i= iσ x).
      change (x i⊕ i0 i= x) in IH.
      now rewrite add_rec, IH.
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
      change (iσ x i⊗ i0 i= i0).
      change (x i⊗ i0 i= i0) in IH.
      now rewrite mult_rec, IH, add_zero.
    - intros x. apply (H x (fun _ => i0)).
  Qed.

  Lemma add_rec_r x y : 
    x i⊕ (iσ y) i= iσ (x i⊕ y). 
  Proof.
    pose (ϕ := ∀ $1 ⊕ (σ $0) == σ ($1 ⊕ $0) ).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ? z.
      change (i0 i⊕ iσ z i= iσ (i0 i⊕ z)).
      now rewrite !add_zero.
    - intros a IH ρ b.
      specialize (IH (fun _ => i0) b); cbn in *.
      change (iσ a i⊕ iσ b i= iσ (iσ a i⊕ b)).
      change (a i⊕ iσ b i= iσ (a i⊕ b)) in IH.
      now rewrite !add_rec, IH.
    - apply (H x (fun _ => i0) y).
  Qed.


  Lemma add_comm x y :
    x i⊕ y i= y i⊕ x.
  Proof.
    pose (ϕ := ∀ $0 ⊕ $1 == $1 ⊕ $0).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ? a; cbn.
      change (a i⊕ i0 i= i0 i⊕ a).
      now rewrite add_zero, add_zero_r.
    - intros a IH ρ b.
      specialize (IH (fun _ => i0) b); cbn in *.
      change (b i⊕ iσ a i= iσ a i⊕ b).
      change (b i⊕ a i= a i⊕ b) in IH.
      now rewrite add_rec, add_rec_r, IH.
    - apply (H y (fun _ => i0) x).
  Qed.

  Lemma add_asso x y z : 
    (x i⊕ y) i⊕ z i= x i⊕ (y i⊕ z).
  Proof.
    pose (ϕ := ∀∀ ($2 ⊕ $1) ⊕ $0 == $2 ⊕ ($1 ⊕ $0) ).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ? b c. cbn. 
      change ((i0 i⊕ b) i⊕ c i= i0 i⊕ (b i⊕ c)).
      now rewrite !add_zero.
    - intros a IH ρ b c.
      specialize (IH (fun _ => i0) b c); cbn in *.
      change ((iσ a i⊕ b) i⊕ c i= iσ a i⊕ (b i⊕ c)).
      change ((a i⊕ b) i⊕ c i= a i⊕ (b i⊕ c)) in IH.
      now rewrite !add_rec, IH.
    - apply (H x (fun _ => i0) y z).
  Qed.

  Lemma mult_rec_r x y :
    x i⊗ (iσ y) i= x i⊕ (x i⊗ y). 
  Proof.
    pose (ϕ := ∀ $1 ⊗ (σ $0) == $1 ⊕ ($1 ⊗ $0) ).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ? b. cbn. 
    change (i0 i⊗ (iσ b) i= i0 i⊕ (i0 i⊗ b)).
      now rewrite !mult_zero, add_zero.
    - intros a IH ρ b. cbn.
      specialize (IH (fun _ => i0) b); cbn in *.
      change (a i⊗ (iσ b) i= a i⊕ (a i⊗ b)) in IH.
      change (iσ a i⊗ (iσ b) i= (iσ a) i⊕ (iσ a i⊗ b)).
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
    - intros ? b; cbn. 
      change (b i⊗ i0 i= i0 i⊗ b).
      now rewrite mult_zero, mult_zero_r.
    - intros a IH ρ b.
      specialize (IH (fun _ => i0) b); cbn in *.
      change (b i⊗ a i= a i⊗ b) in IH.
      change (b i⊗ iσ a i= iσ a i⊗ b).
      now rewrite mult_rec, mult_rec_r, IH.
    - apply (H y (fun _ => i0) x).
  Qed.

  Lemma distributive x y z : 
    (x i⊕ y) i⊗ z i= (x i⊗ z) i⊕ (y i⊗ z).
  Proof.
    pose (ϕ := ∀∀ ($1 ⊕ $0) ⊗ $2 == ($1 ⊗ $2) ⊕ ($0 ⊗ $2) ).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ? b c; cbn.
      change ((b i⊕ c) i⊗ i0 i= (b i⊗ i0) i⊕ (c i⊗ i0)).
      now rewrite !mult_zero_r, add_zero.
    - intros a IH ρ b c.
      specialize (IH (fun _ => i0) b c); cbn in *.
      change ((b i⊕ c) i⊗ a i= (b i⊗ a) i⊕ (c i⊗ a)) in IH.
      change ((b i⊕ c) i⊗ iσ a i= (b i⊗ iσ a) i⊕ (c i⊗ iσ a)).
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
    - intros ? y z; cbn.
      change ((i0 i⊗ y) i⊗ z i= i0 i⊗ (y i⊗ z)).
      now rewrite !mult_zero.
    - intros x IH ρ y z.
      specialize (IH (fun _ => i0) y z); cbn in *.
      change ((x i⊗ y) i⊗ z i= x i⊗ (y i⊗ z)) in IH.
      change ((iσ x i⊗ y) i⊗ z i= iσ x i⊗ (y i⊗ z)).
      now rewrite !mult_rec, <-IH, distributive.
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
    - intros ρ; cbn. left.
      change (i0 i= i0).
      reflexivity.
    - intros x IH ρ.
      right. exists x; cbn.
      change (iσ x i= iσ x).
      reflexivity.
    - intros x. apply (H x (fun _ => i0)).
  Qed.

  Lemma eq_dec :
    forall x y : D, x i= y \/ ~ x i= y.
  Proof.
    pose (ϕ := ∀ $1 == $0 ∨ ($1 == $0 → ⊥)).
    assert (forall n ρ, (n.:ρ) ⊨ ϕ).
    apply induction. repeat solve_bounds.
    - intros ρ y. cbn.
      change (i0 i= y \/ (i0 i= y -> False)).
      destruct (zero_or_succ y) as [|[z ->]].
      + now left.
      + right. apply zero_succ.
    - intros x IH ρ y.
      change (iσ x i= y \/ (iσ x i= y -> False)).
      destruct (zero_or_succ y) as [-> | [z ->]].
      + right. intros e. eapply zero_succ.
        rewrite e. reflexivity.
      + destruct (IH (fun _ => i0) z); cbn in H.
        left. change (x i= z) in H. now rewrite H.
        right. intros ?%succ_inj. auto.
    - intros x y. apply (H x (fun _ => i0) y).
  Qed.

  Lemma sum_is_zero : 
    forall x y, x i⊕ y = i0 -> x = i0 /\ y = i0.
  Proof.
    intros H.
    destruct (zero_or_succ x) as [-> |[? ->]], (zero_or_succ y) as [-> |[? ->]]; auto.
    - repeat split. now rewrite add_zero in H.
    - repeat split. rewrite add_rec in H. symmetry in H.
      now apply zero_succ in H.
    - split; rewrite add_rec in H; symmetry in H; now apply zero_succ in H.
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
    - intros ρ d; cbn. destruct (zero_or_succ d) as [-> | [k ->] ].
      + now right; left.
      + left. exists k. now rewrite add_zero.
    - intros n IH ρ d. cbn. destruct (zero_or_succ d) as [-> | [k ->] ].
      + right; right. exists n. now rewrite add_zero.
      + specialize (IH (fun _ => i0) k); cbn in IH.
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



Section ND.

  Variable p : peirce.

  Fixpoint iter {X: Type} f n (x : X) :=
    match n with
      0 => x
    | S m => f (iter f m x)
    end.

  Fact iter_switch {X} f n x : f (@iter X f n x) = iter f n (f x).
  Proof. induction n; cbn; now try rewrite IHn. Qed.


  Lemma subst_up_var k x σ :
    x < k -> (var x)`[iter up k σ] = var x.
  Proof.
    induction k in x, σ |-*.
    - now intros ?%PeanoNat.Nat.nlt_0_r.
    - intros H.
      destruct (Compare_dec.lt_eq_lt_dec x k) as [[| <-]|].
      + cbn [iter]. rewrite iter_switch. now apply IHk.
      + destruct x. reflexivity.
        change (iter _ _ _) with (up (iter up (S x) σ)).
        change (var (S x)) with ((var x)`[↑]).
        rewrite up_term, IHk. reflexivity. constructor.
      + lia.
  Qed.


  Lemma subst_bounded_term t σ k : 
    bounded_t k t -> t`[iter up k σ] = t.
  Proof.
    induction 1.
    - now apply subst_up_var.
    - cbn. f_equal.
      rewrite <-(Vector.map_id _ _ v) at 2.
      apply Vector.map_ext_in. auto.
  Qed.


  Lemma subst_closed_term t σ :
    bounded_t 0 t -> t`[σ] = t.
  Proof.
    intros H0.
    refine (_ (subst_bounded_term t σ 0 H0)).
    now cbn.
  Qed.


  Lemma subst_bounded k ϕ σ : 
    bounded k ϕ -> ϕ[iter up k σ] = ϕ.
  Proof.
    induction 1 in σ |-*; cbn.
    - f_equal.
      rewrite <-(Vector.map_id _ _ v) at 2.
      apply Vector.map_ext_in.
      intros t Ht. apply subst_bounded_term. auto.
    - now rewrite IHbounded1, IHbounded2.
    - f_equal; now apply subst_bounded_term.
    - f_equal.
      change (up _) with (iter up (S n) σ).
      apply IHbounded.
    - reflexivity.
  Qed.


  Definition exist_times n (ϕ : form) := iter (fun psi => ∃ psi) n ϕ.


  Lemma up_decompose σ ϕ : 
    ϕ[up (S >> σ)][(σ 0)..] = ϕ[σ].
  Proof.
    rewrite subst_comp. apply subst_ext.
    intros [].
    - reflexivity.
    - apply subst_term_shift.
  Qed.


  Lemma subst_exist_prv {σ N Gamma} ϕ :
    Gamma ⊢ ϕ[σ] -> bounded N ϕ -> Gamma ⊢ exist_times N ϕ. 
  Proof.
    induction N in ϕ, σ |-*; intros; cbn.
    - erewrite <-(subst_bounded 0); eassumption.
    - rewrite iter_switch. eapply (IHN (S >> σ)).
      cbn. eapply (ExI (σ 0)).
      now rewrite up_decompose.
      now apply bounded_S_exists.
  Qed.


  Lemma subst_forall_prv ϕ {N Gamma} :
    Gamma ⊢ (forall_times N ϕ) -> bounded N ϕ -> forall σ, Gamma ⊢ ϕ[σ].
  Proof.
    induction N in ϕ |-*; intros ?? σ; cbn in *.
    - change σ with (iter up 0 σ).
      now rewrite (subst_bounded 0).
    - specialize (IHN (∀ ϕ) ).
      rewrite <-up_decompose.
      apply AllE. apply IHN.
      unfold forall_times. now rewrite <-iter_switch.
      now apply bounded_S_forall.
  Qed.

End ND.


Section Q_prv.

  Variable p : peirce.

  Variable Gamma : list form.
  Variable G : incl Q Gamma.

  Derive Signature for Vector.t.
  
  Lemma vec_nil_eq X (v : vec X 0) :
    v = Vector.nil X.
  Proof.
    depelim v. reflexivity.
  Qed.

  Lemma vec_inv1 X (v : vec X 1) :
    v = [ Vector.hd v ].
  Proof.
    repeat depelim v. cbn. reflexivity.
  Qed.

  Lemma vec_inv2 X (v : vec X 2) :
    v = [ Vector.hd v ; Vector.hd (Vector.tl v) ].
  Proof.
    repeat depelim v. cbn. reflexivity.
  Qed.

  Lemma map_hd X Y n (f : X -> Y) (v : vec X (S n)) :
    Vector.hd (Vector.map f v) = f (Vector.hd v).
  Proof.
    depelim v. reflexivity.
  Qed.

  Lemma map_tl X Y n (f : X -> Y) (v : vec X (S n)) :
    Vector.tl (Vector.map f v) = Vector.map f (Vector.tl v).
  Proof.
    depelim v. reflexivity.
  Qed.

  Lemma vec_in_hd X n (v : vec X (S n)) :
    vec_in (Vector.hd v) v.
  Proof.
    depelim v. constructor.
  Qed.

  Lemma vec_in_hd_tl X n (v : vec X (S (S n))) :
    vec_in (Vector.hd (Vector.tl v)) v.
  Proof.
    depelim v. constructor. depelim v. constructor.
  Qed.

  Lemma in_hd X n (v : vec X (S n)) :
    Vector.In (Vector.hd v) v.
  Proof.
    depelim v. constructor.
  Qed.

  Lemma in_hd_tl X n (v : vec X (S (S n))) :
    Vector.In (Vector.hd (Vector.tl v)) v.
  Proof.
    depelim v. constructor. depelim v. constructor.
  Qed.


  (** Closed terms are numerals. *)

  Lemma closed_term_is_num s : 
    bounded_t 0 s -> { n & Gamma ⊢ s == num n }.
  Proof.
    pattern s; revert s. apply term_rect.
    - intros ? H. exists 0. inversion H; lia.
    - intros [] v N H; cbn in v.
      + exists 0. rewrite (vec_nil_eq _ v).
        now apply reflexivity.
      + rewrite (vec_inv1 _ v).
        destruct (N (Vector.hd v)) as [n Hn].
        apply vec_in_hd.
        inversion H. subst.
        apply Eqdep_dec.inj_pair2_eq_dec in H2 as ->.
        apply H1. apply in_hd. decide equality.
        exists (S n); cbn. now apply eq_succ.
      + rewrite (vec_inv2 _ v).
        remember (Vector.hd v) as x eqn:Hx.
        remember (Vector.hd (Vector.tl v)) as y eqn:Hy.
        destruct (N x) as [n Hn].
        rewrite Hx. apply vec_in_hd.
        inversion H. subst.
        apply Eqdep_dec.inj_pair2_eq_dec in H2 as ->.
        apply H1. apply in_hd. decide equality.
        destruct (N y) as [m Hm].
        rewrite Hy. apply vec_in_hd_tl.
        inversion H. subst.
        apply Eqdep_dec.inj_pair2_eq_dec in H2 as ->.
        apply H1. apply in_hd_tl. decide equality.
        exists (n + m).
        eapply transitivity.
        3 : apply num_add_homomorϕsm.
        all: try assumption.
        now apply eq_add.
      + rewrite (vec_inv2 _ v).
        remember (Vector.hd v) as x eqn:Hx.
        remember (Vector.hd (Vector.tl v)) as y eqn:Hy.
        destruct (N x) as [n Hn].
        rewrite Hx. apply vec_in_hd.
        inversion H. subst.
        apply Eqdep_dec.inj_pair2_eq_dec in H2 as ->.
        apply H1. apply in_hd. decide equality.
        destruct (N y) as [m Hm].
        rewrite Hy. apply vec_in_hd_tl.
        inversion H. subst.
        apply Eqdep_dec.inj_pair2_eq_dec in H2 as ->.
        apply H1. apply in_hd_tl. decide equality.
        exists (n * m).
        eapply transitivity.
        3 : apply num_mult_homomorϕsm.
        all: try assumption.
        now apply eq_mult.
  Qed.


  Fact num_eq x y : 
    x = y -> Gamma ⊢ num x == num y.
  Proof.
    intros ->. now apply reflexivity.
  Qed.

  Lemma num_neq x : 
    forall y, x <> y -> Gamma ⊢ ¬ num x == num y.
  Proof.
    induction x as [| x IHx].
    - intros [] neq.
      + congruence.
      + now apply Zero_succ.
    - intros [|y] neq.
      + apply II. eapply IE with (ϕ := num 0 == num (S x)).
        eapply Weak with Gamma. now apply Zero_succ.
        firstorder.
        apply symmetry; [now right; apply G|].
        apply Ctx. now left.
      + apply II. eapply IE with (ϕ := num x == num y).
        { eapply Weak with Gamma. apply IHx. 
          - lia. 
          - now right. }
        apply Succ_inj. 
        ++ now right; apply G.
        ++ apply Ctx. now left.
  Qed. 


  Lemma num_eq_dec x y : 
    { Gamma ⊢ num x == num y } + { Gamma ⊢ ¬ num x == num y }.
  Proof.
    destruct (dec_eq_nat x y); [left|right].
    - now apply num_eq.
    - now apply num_neq.
  Qed.  


  (** Provability of equality for closed terms is decidable. *)
  
  Lemma term_eq_dec s t : 
    bounded_t 0 s -> bounded_t 0 t -> { Gamma ⊢ s == t } + { Gamma ⊢ ¬ s == t }.
  Proof.
    intros Hs Ht.
    destruct (closed_term_is_num s Hs) as [n Hn], (closed_term_is_num t Ht) as [m Hm].
    destruct (num_eq_dec n m) as [H|H].
    - left. eapply transitivity; eauto 1.
      eapply transitivity; eauto 1.
      apply symmetry; assumption.
    - right.
      apply II. eapply IE.
      apply Weak with Gamma; try apply H; firstorder.
      eapply transitivity. shelve.
      2 : eapply Weak with Gamma; try apply Hm.
      eapply transitivity. shelve.
      eapply Weak with Gamma. apply symmetry in Hn. apply Hn.
      assumption. shelve.
      apply Ctx. Unshelve.
      + now left.
      + now right.
      + right. now apply G.
      + right. now apply G.
      + now right.
  Qed.


  Lemma num_lt x y :
    x < y -> Gamma ⊢ num x ⧀ num y.
  Proof.
    intros [k Hk]%lt_nat_equiv.
    apply ExI with (t := num k). cbn.
    rewrite !num_subst, <-Hk. cbn.
    apply eq_succ. easy.
    apply symmetry, num_add_homomorϕsm; easy.
  Qed.

  Lemma not_lt_zero_prv' :
  Q ⊢ ∀ ¬ $0 ⧀ num 0.
  Proof.
    apply AllI, II. eapply ExE.
    - apply Ctx. now left.
    - cbn. eapply IE.
      + pose (s := $1 ⊕ $0).
        apply Zero_succ with (x := s).
        right; now right.
      + apply Ctx. now left.
  Qed.

  Lemma not_lt_zero_prv t :
    Q ⊢ ¬ t ⧀ num 0.
  Proof.
    change (Q ⊢ (¬ $0 ⧀ num 0)[t..]).
    apply AllE, not_lt_zero_prv'.
  Qed.

  Lemma Faster3 :
    forall A, Q <<= A ++ map (subst_form ↑) Q.
  Proof.
    intros A; induction A; cbn.
    - firstorder.
    - right. now apply IHA.
  Qed.

  Lemma num_nlt x :
    forall y, ~ (x < y) -> Q ⊢ ¬ num x ⧀ num y.
  Proof.
    induction x as [| x IHx].
    - intros [] ineq.
      + apply not_lt_zero_prv.
      + lia.
    - intros [|y] ineq.
      + apply not_lt_zero_prv.
      + assert (~ x < y) as H % IHx by lia.
        apply II. eapply IE.
        { eapply Weak; [apply H | now right]. }
        eapply ExE.
        * apply Ctx. now left.
        * apply ExI with (t := $0).
          cbn. rewrite !num_subst.
          eapply transitivity. right; now right.
          2 : {apply Add_rec. right; now right. }
          apply Succ_inj. right; now right.
          apply Ctx. now left.
  Qed. 
  
  
  Lemma num_lt_dec x y :
    { Gamma ⊢ num x ⧀ num y } + { Gamma ⊢ ¬ num x ⧀ num y }.
  Proof.
    destruct (lt_dec x y); [left|right].
    - now apply num_lt.
    - apply Weak with Q; [now apply num_nlt | assumption].
  Qed.


  Lemma term_lt_dec s t :
    map (subst_form ↑) Gamma = Gamma -> bounded_t 0 s -> bounded_t 0 t -> { Gamma ⊢ s ⧀ t } + { Gamma ⊢ ¬ s ⧀ t }.
  Proof.
    intros HG Hs Ht.
    destruct (closed_term_is_num s Hs) as [n Hn], (closed_term_is_num t Ht) as [m Hm].
    destruct (num_lt_dec n m) as [H|H].
    - left. eapply ExE. apply H.
      apply ExI with (t0:=$0).
      rewrite !num_subst, HG. cbn.
      repeat rewrite (subst_closed_term t), (subst_closed_term s); auto. 
      eapply transitivity.
      2 : { eapply Weak. apply Hm. now right. }
      now right; apply G.
      apply symmetry. now right; apply G.
      pose (j := σ (num n ⊕ $0)).
      eapply transitivity with (y:= j); unfold j. now right; apply G.
      apply eq_succ. now right; apply G.
      apply eq_add. now right; apply G.
      eapply Weak. apply Hn. now right.
      apply reflexivity. now right; apply G.
      apply symmetry. now right; apply G.
      apply Ctx; now left.
    - right. apply II. eapply IE.
      eapply Weak. apply H. now right.
      eapply ExE. apply Ctx; now left.
      apply ExI with (t0:=$0).
      cbn. rewrite !num_subst.
      repeat rewrite (subst_closed_term t), (subst_closed_term s), HG; auto.
      apply symmetry in Hm; auto.
      apply symmetry in Hn; auto.
      eapply transitivity.
      2 : { eapply Weak. apply Hm. right; now right. }
      now right; right; apply G.
      apply symmetry. now right; right; apply G.
      pose (j := σ (s ⊕ $0)).
      eapply transitivity with (y:= j); unfold j. 
      now right; right; apply G.
      apply eq_succ. now right; right; apply G.
      apply eq_add. now right; right; apply G.
      eapply Weak. apply Hn. now right; right.
      apply reflexivity. now right; right; apply G.
      apply symmetry. now right; right; apply G.
      apply Ctx; now left.
  Qed.


End Q_prv.


Definition std {D I} d := exists n, @inu D I n = d.
Definition stdModel D {I} := forall d, exists n, (@inu D I) n = d.
Definition nonStd D {I} := exists e, ~ @std D I e.
Definition notStd D {I} := ~ @stdModel D I.

Fact nonStd_notStd {D I} :
  @nonStd D I -> ~ stdModel D.
Proof.
  intros [e He] H; apply He, H.
Qed.

Notation "⊨ ϕ" := (forall ρ, ρ ⊨ ϕ) (at level 21).

Section stdModel.

  Variable D : Type.
  Variable I : interp D.
  Variable axioms : forall ax, PA ax -> ⊨ ax.

  Definition nat_hom (f : nat -> D) := 
    f 0 = @inu D I 0
    /\ forall n, f (S n) = iσ (f n).
  Definition stdModel' := exists f, nat_hom f /\ bij f.

  Lemma hom_agree_inu f :
    nat_hom f -> forall x, f x = inu x.
  Proof.
    intros [H0 H] x. induction x as [| x IH].
    - assumption.
    - cbn. now rewrite H, IH.
  Qed.

  Lemma stdModel_eqiv :
    stdModel' <-> @stdModel D I.
  Proof.
    split.
    - intros (f & Hf & [inj surj]) e.
      destruct (surj e) as [n <-].
      exists n. now rewrite (hom_agree_inu _ Hf).
    - intros H. exists inu. repeat split.
      + intros ???. now eapply inu_inj.
      + apply H.
  Qed.

End stdModel.
