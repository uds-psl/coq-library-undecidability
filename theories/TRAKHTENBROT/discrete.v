(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Nat Lia Relations.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos fin_quotient vec.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops fo_terms fo_logic.

Set Implicit Arguments.

Local Definition forall_equiv X := @fol_quant_sem_ext X fol_fa.
Local Definition exists_equiv X := @fol_quant_sem_ext X fol_ex.

Local Notation " e '#>' x " := (vec_pos e x).
Local Notation " e [ v / x ] " := (vec_change e x v).

Section gfp.

  Variable (M : Type). 

  Implicit Type (R T : M -> M -> Prop).

  Notation "R ⊆ T" := (forall x y, R x y -> T x y).

  Notation "R 'o' T" := (fun x z => exists y, R x y /\ T y z) (at level 60).

  Let incl_trans R S T : R ⊆ S -> S ⊆ T -> R ⊆ T.
  Proof. firstorder. Qed.

  Let comp_mono R R' T T' : R ⊆ R' -> T ⊆ T' -> R o T ⊆ R' o T'.
  Proof. firstorder. Qed. 

  Variable (F : (M -> M -> Prop) -> M -> M -> Prop)
           (HF0 : forall R T, R ⊆ T -> F R ⊆ F T).

  Let sym R := fun x y => R y x.

  Let i := iter F (fun _ _ => True).

  Let iS n : i (S n) = F (i n).
  Proof. apply iter_S. Qed.

  Let i0 : i 0 = fun _ _ => True.
  Proof. auto. Qed.

  Let i_S n : i (S n) ⊆ i n.
  Proof.
    unfold i.
    induction n as [ | n IHn ].
    + simpl; auto.
    + intros x y.
      rewrite iter_S with (n := n).
      rewrite iter_S.
      apply HF0, IHn.
  Qed.

  Let i_decr n m : n <= m -> i m ⊆ i n.
  Proof. induction 1; auto. Qed.

  Definition gfp x y := forall n, i n x y.

  Notation I := (@eq M).

  Hypothesis HF1 : I ⊆ F I.

  Let i_refl n : I ⊆ i n.
  Proof.
    induction n as [ | n IHn ].
    + rewrite i0; auto.
    + rewrite iS.
      apply incl_trans with (1 := HF1), HF0, IHn.
  Qed.
  
  Let gfp_refl : I ⊆ gfp.
  Proof.
    intros x y [] n.
    apply i_refl; auto.
  Qed.

  Hypothesis HF2 : forall R, sym (F R) ⊆ F (sym R).

  Let i_sym n : sym (i n) ⊆ i n.
  Proof.
    induction n as [ | n IHn ].
    + intros x y; unfold i; simpl; auto.
    + rewrite iS.
      apply incl_trans with (2 := HF0 _ IHn), HF2.
  Qed.

  Let gfp_sym : sym gfp ⊆ gfp.
  Proof.
    intros x y H n.
    apply i_sym, H.
  Qed.

  Hypothesis HF3 : forall R, F R o F R ⊆ F (R o R).

  Let i_trans n : i n o i n ⊆ i n.
  Proof.
    induction n as [ | n IHn ].
    + rewrite i0; auto.
    + rewrite iS.
      apply incl_trans with (1 := @HF3 _), HF0, IHn.
  Qed.

  Let gfp_trans : gfp o gfp ⊆ gfp.
  Proof.
    intros x y H n.
    apply i_trans.
    revert H; apply comp_mono; auto.
  Qed.

  Fact gfp_equiv : equiv _ gfp.
  Proof.
    msplit 2.
    + intro; apply gfp_refl; auto.
    + intros x y z H1 H2; apply gfp_trans; exists y; auto.
    + intros x y; apply gfp_sym.
  Qed.

  Let gfp_fix1 : F gfp ⊆ gfp.
  Proof.
    intros x y H n.
    apply i_S; rewrite iS.
    revert H; apply HF0; auto.
  Qed.

  (** This is omega continuity *)

  Variable HF4 : forall (s : nat -> M -> M -> Prop), 
                        (forall n m, n <= m -> s m ⊆ s n) 
                     -> (fun x y => forall n, F (s n) x y) ⊆ F (fun x y => forall n, s n x y).

  Let gfp_fix0 : gfp ⊆ F gfp.
  Proof.
    intros x y H.
    apply HF4; auto.
    intro; rewrite <- iS; apply H.
  Qed.

  Fact gfp_fix x y : F gfp x y <-> gfp x y.
  Proof. split; auto. Qed.

  (** This is for decidability *)

  Let dec R := forall x y, { R x y } + { ~ R x y }.

  Variable HF5 : forall R, dec R -> dec (F R).

  Let i_dec n : dec (i n).
  Proof.
    induction n as [ | n IHn ].
    + rewrite i0; left; auto.
    + rewrite iS; apply HF5; auto.
  Qed.

  (** For the decidability of gfp, we need the finiteness
      so that gfp = i n for a sufficiently large n *)

End gfp.

Section discrete_quotient.

  Variables (Σ : fo_signature) 
            (M : fo_model Σ)  
            (fin : finite_t M) 
            (dec : fo_model_dec M)
            (φ : nat -> M).

  Implicit Type (R T : M -> M -> Prop).

  (** Construction of the greatest fixpoint of the following operator *)

  Let fom_op R x y :=
       (forall s (v : vec M (ar_syms Σ s)) p, R (fom_syms M s (v[x/p])) (fom_syms M s (v[y/p]))) 
    /\ (forall s (v : vec M (ar_rels Σ s)) p, fom_rels M s (v[x/p]) <-> fom_rels M s (v[y/p])).

  Let fom_op_mono R T : (forall x y, R x y -> T x y) -> (forall x y, fom_op R x y -> fom_op T x y).
  Proof.
    intros H x y (H1 & H2); split; intros; auto.
  Qed. 

  Let fom_op_id x y : x = y -> fom_op (@eq _) x y.
  Proof. intros []; split; auto; tauto. Qed.

  Let fom_op_sym R x y : fom_op R y x -> fom_op (fun x y => R y x) x y.
  Proof.
    intros (H1 & H2); split; intros; auto.
    symmetry; auto.
  Qed.

  Let fom_op_trans R x z : (exists y, fom_op R x y /\ fom_op R y z)
                        -> fom_op (fun x z => exists y, R x y /\ R y z) x z.
  Proof.
    intros (y & H1 & H2); split; intros s v p.
    + exists (fom_syms M s (v[y/p])); split.
      * apply H1.
      * apply H2.
    + transitivity (fom_rels M s (v[y/p])).
      * apply H1.
      * apply H2.
  Qed.

  Reserved Notation "x ≃ y" (at level 70, no associativity).

  Definition fom_eq := gfp fom_op.

  Infix "≃" := fom_eq.

  Let fom_eq_equiv : equiv _ fom_eq.
  Proof. apply gfp_equiv; auto. Qed.

  (** This involves the w-continuity of fom_op *)

  Let fom_eq_fix x y : fom_op fom_eq x y <-> fom_eq x y.
  Proof. 
    apply gfp_fix; auto; clear x y.
    intros f Hf x y H; split; intros s v p.
    + intros n.
      generalize (H n); intros (H1 & H2).
      apply H1.
    + apply (H 0).
  Qed.

  (** We build the greatest bisimulation which is an equivalence 
      and a fixpoint for the above operator *) 

  Fact fom_eq_refl x : x ≃ x.
  Proof. apply (proj1 fom_eq_equiv). Qed.

  Fact fom_eq_sym x y : x ≃ y -> y ≃ x.
  Proof. apply fom_eq_equiv. Qed.

  Fact fom_eq_trans x y z : x ≃ y -> y ≃ z -> x ≃ z.
  Proof. apply fom_eq_equiv. Qed.

  Fact fom_eq_syms x y s v p : x ≃ y -> fom_syms M s (v[x/p]) ≃ fom_syms M s (v[y/p]).
  Proof. intros; apply fom_eq_fix; auto. Qed. 
    
  Fact fom_eq_rels x y s v p : x ≃ y -> fom_rels M s (v[x/p]) <-> fom_rels M s (v[y/p]).
  Proof. intros; apply fom_eq_fix; auto. Qed. 

  Fact fom_eq_dec x y : { x ≃ y } + { ~ x ≃ y }.
  Proof. Admitted.

End discrete_quotient.

