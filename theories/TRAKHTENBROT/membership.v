(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Nat Lia Max Wellfounded Coq.Setoids.Setoid.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops fo_terms fo_logic.

Set Implicit Arguments.

Section membership.

  (** We develop a theory of finitary and computable and 
      extensional membership. We build pair, ordered pairs
      and ordered triples and show their properties *)

  Variable (X : Type) (mem : X -> X -> Prop).

  Infix "∈" := mem.
  Notation "x ∉ y" := (~ x ∈ y).

  Definition mb_incl x y := forall a, a ∈ x -> a ∈ y.
  Definition mb_equiv x y := forall a, a ∈ x <-> a ∈ y.

  Infix "⊆" := mb_incl.
  Infix "≈" := mb_equiv. 
  Notation "x ≉ y" := (~ x ≈ y).

  (** Hypothesis on the model *)

  Variable (Rdec : forall x y, { x ∈ y } + { x ∉ y }) (Xfin : finite_t X).

  Let lX : list X := proj1_sig Xfin.
  Let HX : forall x, In x lX := proj2_sig Xfin.

  Fact mb_incl_refl x : x ⊆ x.
  Proof. red; auto. Qed.

  Fact mb_incl_trans x y z : x ⊆ y -> y ⊆ z -> x ⊆ z.
  Proof. unfold mb_incl; auto. Qed.

  Fact mb_incl_choose x y : { z | z ∈ x /\ z ∉ y } + { x ⊆ y }.
  Proof.
    set (P z := z ∈ x /\ z ∉ y).
    set (Q z := z ∈ x -> z ∈ y).
    destruct list_dec with (P := P) (Q := Q) (l := lX)
      as [ (z & _ & H2 & H3) | H ]; unfold P, Q in *; clear P Q.
    + intros z; destruct (Rdec z x); destruct (Rdec z y); tauto.
    + left; exists z; auto.
    + right; intros z; apply H; auto.
  Qed.  

  Fact mb_incl_dec x y : { x ⊆ y } + { ~ x ⊆ y }.
  Proof.
    destruct (mb_incl_choose x y) as [ (?&?&?) |]; auto.
  Qed.

  Fact mb_equiv_eq x y : x ≈ y <-> x ⊆ y /\ y ⊆ x.
  Proof. firstorder. Qed.
  
  Fact mb_equiv_dec x y : { x ≈ y } + { x ≉ y }.
  Proof.
    destruct (mb_incl_dec x y); [ destruct (mb_incl_dec y x) | ].
    1: left; apply mb_equiv_eq; auto. 
    all: right; rewrite mb_equiv_eq; tauto.
  Qed.

  Hint Resolve mb_equiv_dec.

  Fact mb_equiv_refl_True x : x ≈ x <-> True.    Proof. unfold mb_equiv; tauto. Qed.
  Fact mb_equiv_refl x : x ≈ x.                  Proof. unfold mb_equiv; tauto. Qed.

  Fact mb_equiv_sym x y : x ≈ y -> y ≈ x.
  Proof. do 2 rewrite mb_equiv_eq; tauto. Qed.

  Fact mb_equiv_trans x y z : x ≈ y -> y ≈ z -> x ≈ z.
  Proof. repeat rewrite mb_equiv_eq; unfold mb_incl; intros [] []; split; auto. Qed.

  Add Parametric Relation: (X) (mb_equiv)
      reflexivity proved by mb_equiv_refl
      symmetry proved by mb_equiv_sym
      transitivity proved by mb_equiv_trans
    as mb_equiv_equivalence.

  Hint Resolve mb_equiv_refl mb_equiv_sym.

  (* A first FOL axiom: sets are characterized by their elements *)

  Definition mb_member_ext := forall x y z, x ≈ y -> x ∈ z -> y ∈ z.

  Variable (mb_axiom_ext : mb_member_ext).

  Fact mb_equiv_mem x y : x ≈ y -> forall z, x ∈ z <-> y ∈ z.
  Proof. split; apply mb_axiom_ext; auto. Qed.
  
   Add Parametric Morphism: (mem) with signature 
     (mb_equiv) ==> (mb_equiv) ==> (iff) as mb_mem_congruence.
  Proof.
    intros x y H1 a b H2; red in H1, H2; split;
     rewrite <- H2; apply mb_axiom_ext; auto.
  Qed.

  Add Parametric Morphism: (fun x y => x ⊆ y) with signature 
     (mb_equiv) ==> (mb_equiv) ==> (iff) as mb_incl_congruence.
  Proof.
    intros x y H1 a b H2; split; intros H z.
    + rewrite <- H1, <- H2; auto.
    + rewrite H1, H2; auto.
  Qed.

  Definition mb_is_pair p x y := forall a, a ∈ p <-> a ≈ x \/ a ≈ y.

  Fact mb_is_pair_comm p x y : mb_is_pair p x y -> mb_is_pair p y x.
  Proof. unfold mb_is_pair; apply forall_equiv; intro; tauto. Qed.

  Add Parametric Morphism: (mb_is_pair) with signature 
     (mb_equiv) ==> (mb_equiv) ==> (mb_equiv) ==> (iff) as mb_is_pair_congruence.
  Proof.
    intros p q H1 x x' H2 y y' H3.
    apply forall_equiv; intros a.
    rewrite H1, H2, H3; tauto.
  Qed.

  Fact mb_is_pair_fun p q x y : mb_is_pair p x y -> mb_is_pair q x y -> p ≈ q.
  Proof. intros H1 H2; red in H1, H2; intro; rewrite H1, H2; tauto. Qed.

  (** Many cases here, automation helps !! *)

  Fact mb_is_pair_inj p x y x' y' : mb_is_pair p x y 
                                 -> mb_is_pair p x' y' 
                                 -> x ≈ x' /\ y ≈ y'
                                 \/ x ≈ y' /\ y ≈ x'.
  Proof.
    unfold mb_is_pair; intros H1 H2.
    generalize (proj1 (H2 x)) (proj1 (H2 y)); rewrite H1, H1, mb_equiv_refl_True, mb_equiv_refl_True.
    generalize (proj1 (H1 x')) (proj1 (H1 y')); rewrite H2, H2, mb_equiv_refl_True, mb_equiv_refl_True.
    intros [] [] [] []; auto.
  Qed.

  Fact mb_is_pair_inj' p x y : mb_is_pair p x x 
                            -> mb_is_pair p y y
                            -> x ≈ y.
  Proof.
    intros H1 H2; generalize (mb_is_pair_inj H1 H2); tauto.
  Qed.

  Fact mb_is_pair_dec p x y : { mb_is_pair p x y } + { ~ mb_is_pair p x y }.
  Proof. 
    unfold mb_is_pair.
    apply (fol_quant_sem_dec fol_fa); auto; intros u.
    apply fol_equiv_dec; auto.
    apply (fol_bin_sem_dec fol_disj); auto.
  Qed.

  Hint Resolve mb_is_pair_dec.

  (** Ordered pairs (x,y) := {{x},{x,y}}, Von Neuman encoding *)

  Definition mb_is_opair p x y := exists a b, mb_is_pair a x x /\ mb_is_pair b x y /\ mb_is_pair p a b.

  Add Parametric Morphism: (mb_is_opair) with signature 
     (mb_equiv) ==> (mb_equiv) ==> (mb_equiv) ==> (iff) as mb_is_opair_congruence.
  Proof.
    intros p q H1 x x' H2 y y' H3.
    apply exists_equiv; intros a.
    apply exists_equiv; intros b.
    rewrite H1, H2, H3; tauto.
  Qed.

  Fact mb_is_opair_fun p q x y : mb_is_opair p x y -> mb_is_opair q x y -> p ≈ q.
  Proof.
    intros (a & b & H1 & H2 & H3) (u & v & G1 & G2 & G3).
    generalize (mb_is_pair_fun H1 G1) (mb_is_pair_fun H2 G2); intros E1 E2.
    rewrite E1, E2 in H3.
    revert H3 G3; apply mb_is_pair_fun.
  Qed.

  Fact mb_is_opair_inj p x y x' y' : mb_is_opair p x y 
                                  -> mb_is_opair p x' y' 
                                  -> x ≈ x' /\ y ≈ y'.
  Proof.
    intros (a & b & H1 & H2 & H3) (u & v & G1 & G2 & G3).
    generalize (mb_is_pair_inj H3 G3); intros [ (E1 & E2) | (E1 & E2) ].
    + rewrite E1 in H1; rewrite E2 in H2.
      generalize (mb_is_pair_inj' H1 G1); intros E; split; auto.
      rewrite E in H2.
      generalize (mb_is_pair_inj H2 G2); intros [ | (E3 & E4) ]; try tauto.
      rewrite E4; auto.
    + rewrite E1 in H1; rewrite E2 in H2.
      generalize (mb_is_pair_inj H2 G1) (mb_is_pair_inj H1 G2).
      intros [ (E3 & E4) | (E3 & E4) ] [ (E5 & E6) | (E5 & E6) ];
        rewrite E4, <- E5; auto.
  Qed.

  Fact mb_is_opair_dec p x y : { mb_is_opair p x y } + { ~ mb_is_opair p x y }.
  Proof.
    unfold mb_is_opair.
    do 2 (apply (fol_quant_sem_dec fol_ex); auto; intro).
    repeat (apply (fol_bin_sem_dec fol_conj); auto).
  Qed.

  Hint Resolve mb_is_opair_dec.

  (** Ordered triples (x,y,z) := ((x,y),z) *)

  Definition mb_is_otriple t x y z := exists p, mb_is_opair p x y /\ mb_is_opair t p z.
 
  Add Parametric Morphism: (mb_is_otriple) with signature 
     (mb_equiv) ==> (mb_equiv) ==> (mb_equiv) ==> (mb_equiv) ==> (iff) as mb_is_otriple_congruence.
  Proof.
    intros p q H1 x x' H2 y y' H3 z z' H4.
    unfold mb_is_otriple.
    apply exists_equiv; intros t.
    rewrite H1, H2, H3, H4; tauto.
  Qed.

  Fact mb_is_otriple_fun p q x y z : mb_is_otriple p x y z -> mb_is_otriple q x y z -> p ≈ q.
  Proof.
    intros (t1 & H1 & H2) (t2 & H3 & H4).
    generalize (mb_is_opair_fun H1 H3); intros E.
    rewrite E in H2.
    apply (mb_is_opair_fun H2 H4).
  Qed.

  Fact mb_is_otriple_inj t x y z x' y' z' : 
             mb_is_otriple t x y z 
          -> mb_is_otriple t x' y' z' 
          -> x ≈ x' /\ y ≈ y' /\ z ≈ z'.
  Proof.
    intros (p & H1 & H2) (q & H3 & H4).
    destruct (mb_is_opair_inj H2 H4) as (H5 & H6).
    rewrite H5 in H1.
    generalize (mb_is_opair_inj H1 H3); tauto.
  Qed.

  Fact mb_is_otriple_dec p x y z : { mb_is_otriple p x y z } + { ~ mb_is_otriple p x y z }.
  Proof.
    apply (fol_quant_sem_dec fol_ex); auto; intro.
    repeat (apply (fol_bin_sem_dec fol_conj); auto).
  Qed.

  Hint Resolve mb_is_otriple_dec.

  Definition mb_has_pairs (l : X) :=
     forall x y, x ∈ l -> y ∈ l -> exists p, mb_is_pair p x y.

  Definition mb_has_otriples (l : X) :=
    forall x y z, x ∈ l -> y ∈ l -> z ∈ l -> exists t, mb_is_otriple t x y z.

  Definition mb_is_otriple_in r x y z :=
    exists t, mb_is_otriple t x y z /\ t ∈ r.

  Fact mb_is_otriple_in_dec r x y z : { mb_is_otriple_in r x y z } + { ~ mb_is_otriple_in r x y z }.
  Proof.
    apply (fol_quant_sem_dec fol_ex); auto; intro.
    repeat (apply (fol_bin_sem_dec fol_conj); auto).
  Qed.

End membership.

Section FOL_encoding.

  (** First order encoding here *)

  (** Maybe we can redo the whole devel here with fo_definable.v *)

  Notation Σ2 := (Σrel 2).
  Variable (Y : Type) (M2 : fo_model Σ2 Y).

  Let mem a b := fom_rels M2 tt (a##b##ø).
  Infix "∈m" := mem (at level 59, no associativity).

  Definition Σ2_mem x y := fol_atom Σ2 tt (£x##£y##ø).
  Infix "∈" := Σ2_mem.

  Definition Σ2_non_empty l := ∃ 0 ∈ (1+l). 
  Definition Σ2_incl x y := ∀ 0 ∈ (S x) ⤑ 0 ∈ (S y).
  Definition Σ2_equiv x y := ∀ 0 ∈ (S x) ↔ 0 ∈ (S y).

  Infix "⊆" := Σ2_incl.
  Infix "≈" := Σ2_equiv.

  Definition Σ2_extensional := ∀∀∀ 2 ≈ 1 ⤑ 2 ∈ 0 ⤑ 1 ∈ 0.

  Definition Σ2_is_pair p x y := ∀ 0 ∈ (S p) ↔ 0 ≈ S x ⟇ 0 ≈ S y.

  Definition Σ2_is_opair p x y := 
         ∃∃   Σ2_is_pair 1    (2+x) (2+x)
            ⟑ Σ2_is_pair 0    (2+x) (2+y)
            ⟑ Σ2_is_pair (2+p) 1     0.

  Definition Σ2_is_otriple p x y z := 
          ∃   Σ2_is_opair 0     (S x) (S y)
            ⟑ Σ2_is_opair (S p)  0    (S z).

  Definition Σ2_is_otriple_in r x y z := 
          ∃   Σ2_is_otriple 0 (S x) (S y) (S z) 
            ⟑ 0 ∈ (S r).

  Definition Σ2_has_otriples l :=
        ∀∀∀   2 ∈ (3+l) 
                      ⤑ 1 ∈ (3+l) 
                      ⤑ 0 ∈ (3+l) 
                      ⤑ ∃ Σ2_is_otriple 0 3 2 1.

  Definition Σ2_list_in l lv := fol_lconj (map (fun x => x ∈ l) lv).

  Fact Σ2_is_otriple_in_vars r x y z : incl (fol_vars (Σ2_is_otriple_in r x y z)) (r::x::y::z::nil).
  Proof. intros a; simpl; tauto. Qed.

  Section semantics.

    Variables (ψ : nat -> Y).

    Notation "⟪ A ⟫" := (fol_sem M2 ψ A).

    Fact Σ2_non_empty_spec l : ⟪Σ2_non_empty l⟫ = exists x, x ∈m ψ l.
    Proof. reflexivity. Qed.

    Fact Σ2_incl_spec x y : ⟪Σ2_incl x y⟫ = mb_incl mem (ψ x) (ψ y).
    Proof. reflexivity. Qed.

    Fact Σ2_equiv_spec x y : ⟪Σ2_equiv x y⟫ = mb_equiv mem (ψ x) (ψ y).
    Proof. reflexivity. Qed. 

    Fact Σ2_extensional_spec : ⟪Σ2_extensional⟫ = mb_member_ext mem.
    Proof. reflexivity. Qed.

    Fact Σ2_is_pair_spec p x y : ⟪Σ2_is_pair p x y⟫ = mb_is_pair mem (ψ p) (ψ x) (ψ y).
    Proof. reflexivity. Qed.

    Fact Σ2_is_otriple_spec p x y z : ⟪Σ2_is_otriple p x y z⟫ = mb_is_otriple mem (ψ p) (ψ x) (ψ y) (ψ z).
    Proof. reflexivity. Qed.

    Fact Σ2_is_otriple_in_spec r x y z : ⟪Σ2_is_otriple_in r x y z⟫ = mb_is_otriple_in mem (ψ r) (ψ x) (ψ y) (ψ z).
    Proof. reflexivity. Qed.

    Fact Σ2_has_otriples_spec l : ⟪Σ2_has_otriples l⟫ = mb_has_otriples mem (ψ l).
    Proof. reflexivity. Qed.

    Fact Σ2_list_in_spec l lv : ⟪Σ2_list_in l lv⟫ <-> forall x, In x lv -> ψ x ∈m ψ l.
    Proof.
      unfold Σ2_list_in; rewrite fol_sem_big_conj.
      split.
      + intros H x Hx.
        apply (H (_ ∈ _)), in_map_iff.
        exists x; auto.
      + intros H f; rewrite in_map_iff.
        intros (x & <- & ?); apply H; auto.
    Qed.

  End semantics.

  Notation "⟪ A ⟫" := (fun ψ => fol_sem M2 ψ A).

  Fact Σ2_is_otriple_in_equiv r x y z φ ψ :
               ⟪Σ2_is_otriple_in 3 2 1 0⟫ φ↑r↑x↑y↑z
           <-> ⟪Σ2_is_otriple_in 3 2 1 0⟫ ψ↑r↑x↑y↑z.
  Proof. cbv beta; do 2 rewrite Σ2_is_otriple_in_spec; simpl; tauto. Qed.

End FOL_encoding. 
