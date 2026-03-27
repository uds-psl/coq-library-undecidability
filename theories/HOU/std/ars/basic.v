(*
Parts of this file are copied and modified from the Coq Demos of the lecture Semantics at UdS:
http://www.ps.uni-saarland.de/courses/sem-ws17/confluence.v
 *)

Set Implicit Arguments.
From Stdlib Require Import Morphisms Finite.
From Undecidability.HOU Require Import std.tactics.

Section ClosureRelations.
  Variables (X: Type).
  Implicit Types (R S: X -> X -> Prop) (x y z : X).

  Notation "R <<= S" := (subrelation R S) (at level 70).
  Notation "R === S" := (R <<= S /\ S <<= R) (at level 70).

  Definition functional R :=
    forall x y z, R x y -> R x z -> y = z.


  Inductive star R : X -> X -> Prop :=
  | starRefl x     : star R x x
  | starStep x x' y : R x x' -> star R x' y -> star R x y.

  Inductive sym R: X -> X -> Prop :=
  | symId x y: R x y -> sym R x y 
  | symInv x y: R y x -> sym R x y.

  Hint Constructors star : core.

  Definition Normal R x := forall y, ~ R x y.
  Definition evaluates R s t := star R s t /\ Normal R t.
  Definition equiv R := star (sym R).

  Fact Normal_star_stops R x:
    Normal R x -> forall y, star R x y -> x = y.
  Proof.
    destruct 2; firstorder.
  Qed.

  Lemma star_trans R x y z :
    star R x y -> star R y z -> star R x z.
  Proof.
    induction 1; eauto.
  Qed.

  #[local] Instance star_preorder R: PreOrder (star R).
  Proof.
    constructor; hnf; eauto using star_trans.
  Qed.

  #[local] Instance star_exp R:
    R <<= star R.
  Proof.
    unfold subrelation; eauto.
  Qed.



  #[local] Instance star_mono R S :
    R <<= S -> star R <<= star S.
  Proof.
    intros H x y.
    induction 1; eauto.
  Qed.

  #[local] Instance eval_subrel R:
    (evaluates R) <<= (star R).
  Proof. intros x y []. assumption. Qed. 

  Fact star_idem R :
    star (star R) === star R.
  Proof.
    split.
    - induction 1; eauto using star_trans, star_exp.
    - apply star_mono, star_exp.
  Qed.

  Lemma sym_symmetric R x y:
    sym R x y -> sym R y x.
  Proof.
    intros []; eauto using sym.
  Qed.

  #[local] Instance sym_Symmetric R:
    Symmetric (sym R).
  Proof.
    firstorder using sym_symmetric.
  Qed.

  Lemma refl_star R x y:
    x = y -> star R x y.
  Proof.
    intros ->; eauto.
  Qed.

  Lemma refl_equiv R x:
    equiv R x x.
  Proof.
    constructor.
  Qed.

  Lemma equiv_trans R x y z:
    equiv R x y -> equiv R y z -> equiv R x z.
  Proof. eapply star_trans. Qed. 

  Lemma equiv_symm R x y:
    equiv R x y -> equiv R y x.
  Proof.
    induction 1.
    constructor; eauto.
    eapply star_trans; eauto. 
    econstructor 2; eauto using refl_equiv, sym_symmetric. 
  Qed.


  #[local] Instance equiv_star R:
    star R <<= equiv R.
  Proof.
    induction 1; unfold equiv in *; eauto using sym, star.
  Qed.

  #[local] Instance equiv_rel R:
    R <<= equiv R.
  Proof.
    transitivity (star R); typeclasses eauto. 
  Qed.

  Lemma equiv_reduce R x x' y y' :
    star R x x' -> star R y y' -> equiv R x y -> equiv R x' y'.
  Proof.
    intros. eapply equiv_trans.
    eapply equiv_symm, equiv_star, H. 
    now eapply equiv_trans, equiv_star, H0.
  Qed.


  Lemma eq_equiv R (x y: X):
    x = y -> equiv R x y.
  Proof. intros ->;eapply refl_equiv. Qed.


  #[local] Instance equiv_equivalence R:
    Equivalence (equiv R).
  Proof.
    constructor; firstorder using refl_equiv, equiv_trans, equiv_symm.
  Qed.

  Lemma equiv_join R x y z:
    star R x z -> star R y z -> equiv R x y.
  Proof.
    intros. transitivity z.
    rewrite H; reflexivity. symmetry.
    rewrite H0; reflexivity.
  Qed.

  Lemma subrel_unfold R S (H: R <<= S) x y: R x y -> S x y.
  Proof. eapply H. Qed.

End ClosureRelations.

#[export] Hint Extern 4 => eapply subrel_unfold; [ typeclasses eauto |] : core. 

#[export] Hint Constructors star : core.
#[export] Hint Resolve star_trans star_exp equiv_join : core.

Module ArsInstances.
#[export] Existing Instance star_preorder.
#[export] Existing Instance star_exp.
#[export] Existing Instance star_mono.
#[export] Existing Instance eval_subrel.
#[export] Existing Instance equiv_star.
#[export] Existing Instance equiv_rel.
#[export] Existing Instance equiv_equivalence.
End ArsInstances.
