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
  Require Import utils_tac utils_list.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops.

Set Implicit Arguments.

Local Definition forall_equiv X := @fol_quant_sem_ext X fol_fa.
Local Definition exists_equiv X := @fol_quant_sem_ext X fol_ex.

Section membership.

  Variable (X : Type) (R : X -> X -> Prop).

  Infix "∈" := R.
  Notation "x ∉ y" := (~ x ∈ y).

  Definition m2_incl x y := forall a, a ∈ x -> a ∈ y.
  Definition m2_equiv x y := forall a, a ∈ x <-> a ∈ y.

  Infix "⊆" := m2_incl.
  Infix "≈" := m2_equiv. 
  Notation "x ≉ y" := (~ x ≈ y).

  (** Hypothesis on the model *)

  Variable (Rdec : forall x y, { x ∈ y } + { x ∉ y })
           (lX : list X) (HX : forall x, In x lX).

  Fact m2_incl_refl x : x ⊆ x.
  Proof. red; auto. Qed.

  Fact m2_incl_trans x y z : x ⊆ y -> y ⊆ z -> x ⊆ z.
  Proof. unfold m2_incl; auto. Qed.

  Fact m2_incl_choose x y : { z | z ∈ x /\ z ∉ y } + { x ⊆ y }.
  Proof.
    set (P z := z ∈ x /\ z ∉ y).
    set (Q z := z ∈ x -> z ∈ y).
    destruct list_dec with (P := P) (Q := Q) (l := lX)
      as [ (z & _ & H2 & H3) | H ]; unfold P, Q in *; clear P Q.
    + intros z; destruct (Rdec z x); destruct (Rdec z y); tauto.
    + left; exists z; auto.
    + right; intros z; apply H; auto.
  Qed.  

  Fact m2_incl_dec x y : { x ⊆ y } + { ~ x ⊆ y }.
  Proof.
    destruct (m2_incl_choose x y) as [ (?&?&?) |]; auto.
  Qed.

  Fact m2_equiv_eq x y : x ≈ y <-> x ⊆ y /\ y ⊆ x.
  Proof. firstorder. Qed.
  
  Fact m2_equiv_dec x y : { x ≈ y } + { x ≉ y }.
  Proof.
    destruct (m2_incl_dec x y); [ destruct (m2_incl_dec y x) | ].
    1: left; apply m2_equiv_eq; auto. 
    all: right; rewrite m2_equiv_eq; tauto.
  Qed.

  Fact m2_equiv_refl_True x : x ≈ x <-> True.
  Proof. unfold m2_equiv; tauto. Qed.

  Fact m2_equiv_refl x : x ≈ x.
  Proof. unfold m2_equiv; tauto. Qed.

  Fact m2_equiv_sym x y : x ≈ y -> y ≈ x.
  Proof. do 2 rewrite m2_equiv_eq; tauto. Qed.

  Fact m2_equiv_trans x y z : x ≈ y -> y ≈ z -> x ≈ z.
  Proof. repeat rewrite m2_equiv_eq; unfold m2_incl; intros [] []; split; auto. Qed.

  Add Parametric Relation: (X) (m2_equiv)
      reflexivity proved by m2_equiv_refl
      symmetry proved by m2_equiv_sym
      transitivity proved by m2_equiv_trans
    as m2_equiv_rst.

  Hint Resolve m2_equiv_refl m2_equiv_sym.

  (* A first FOL axiom: sets are characterized by their elements *)

  Definition m2_member_ext := forall x y z, x ≈ y -> x ∈ z -> y ∈ z.

  Variable (m2_ax_ext : m2_member_ext).

  Fact m2_equiv_mem x y : x ≈ y -> forall z, x ∈ z <-> y ∈ z.
  Proof. split; apply m2_ax_ext; auto. Qed.
  
   Add Parametric Morphism: (R) with signature 
     (m2_equiv) ==> (m2_equiv) ==> (iff) as mem_congr.
  Proof.
    intros x y H1 a b H2; red in H1, H2; split;
     rewrite <- H2; apply m2_ax_ext; auto.
  Qed.

  Add Parametric Morphism: (fun x y => x ⊆ y) with signature 
     (m2_equiv) ==> (m2_equiv) ==> (iff) as is_incl_congr.
  Proof.
    intros x y H1 a b H2; split; intros H z.
    + rewrite <- H1, <- H2; auto.
    + rewrite H1, H2; auto.
  Qed.

  Definition m2_is_pair p x y := forall a, a ∈ p <-> a ≈ x \/ a ≈ y.

  Definition m2_is_triple t x y z := forall a, a ∈ t <-> a ≈ x \/ a ≈ y \/ a ≈ z.

  Fact m2_is_pair_comm p x y : m2_is_pair p x y -> m2_is_pair p y x.
  Proof. unfold m2_is_pair; apply forall_equiv; intro; tauto. Qed.

  Add Parametric Morphism: (m2_is_pair) with signature 
     (m2_equiv) ==> (m2_equiv) ==> (m2_equiv) ==> (iff) as is_pair_congr.
  Proof.
    intros p q H1 x x' H2 y y' H3.
    apply forall_equiv; intros a.
    rewrite H1, H2, H3; tauto.
  Qed.

  Add Parametric Morphism: (m2_is_triple) with signature 
     (m2_equiv) ==> (m2_equiv) ==> (m2_equiv) ==> (m2_equiv) ==> (iff) as is_triple_congr.
  Proof.
    intros p q H1 x x' H2 y y' H3 z z' H4.
    apply forall_equiv; intros a.
    rewrite H1, H2, H3, H4; tauto.
  Qed.

  Fact m2_is_pair_fun p q x y : m2_is_pair p x y -> m2_is_pair q x y -> p ≈ q.
  Proof.
    intros H1 H2; red in H1, H2; intro; 
    rewrite H1, H2; tauto.
  Qed.

  Fact m2_is_triple_fun r t x y z : m2_is_triple r x y z 
                                 -> m2_is_triple t x y z 
                                 -> r ≈ t.
  Proof.
    intros H1 H2; red in H1, H2; intro;
    rewrite H1, H2; tauto.
  Qed.

  Fact m2_is_pair_inj p x y x' y' : m2_is_pair p x y 
                                 -> m2_is_pair p x' y' 
                                 -> x ≈ x' /\ y ≈ y'
                                 \/ x ≈ y' /\ y ≈ x'.
  Proof.
    unfold m2_is_pair; intros H1 H2.
    generalize (proj1 (H2 x)) (proj1 (H2 y)); rewrite H1, H1, m2_equiv_refl_True, m2_equiv_refl_True.
    generalize (proj1 (H1 x')) (proj1 (H1 y')); rewrite H2, H2, m2_equiv_refl_True, m2_equiv_refl_True.
    intros [] [] [] []; auto.
  Qed.

  Fact m2_is_pair_inj' p x y : m2_is_pair p x x 
                            -> m2_is_pair p y y
                            -> x ≈ y.
  Proof.
    intros H1 H2; generalize (m2_is_pair_inj H1 H2); tauto.
  Qed.

  (** Replace the big disj with permutation up-to equivalence *)

  (**

  Ltac collect_equiv :=
   repeat match goal with 
     | H : _ ≈ _ |- _ => revert H
   end.

  Ltac symetry :=
    repeat match goal with
      | |- (?x ≈ ?y) -> _ => let H := fresh in intro H; generalize (equiv_sym H); intro
    end. 

  Ltac eliminate :=
    repeat match goal with
      | |- True -> _ => intros _
      | |- (?x ≈ ?x) -> _ => intros _
      | |- (?x ≈ ?y) -> _ => let H := fresh in intro H; rewrite H; clear H
    end. 

  Fact id_rew x : x ≈ x <-> True.
  Proof. split; auto. Qed.

  Fact True_or_rewl (A : Prop) : A \/ True <-> True.
  Proof. tauto. Qed.

  Fact True_or_rewr (A : Prop) : True \/ A <-> True.
  Proof. tauto. Qed.

  Fact True_and_rewl (A : Prop) : A /\ True <-> A.
  Proof. tauto. Qed.

  Fact True_and_rewr (A : Prop) : True /\ A <-> A.
  Proof. tauto. Qed.

  Ltac rsimpl := 
    repeat rewrite id_rew; 
    repeat (rewrite True_or_rewl  || rewrite True_or_rewr || 
            rewrite True_and_rewl || rewrite True_and_rewr).

  Ltac myintro :=
    match goal with
      | |- True -> _ => intros _ 
      | |- ?a \/ ?b \/ ?c -> _ => let H := fresh in intros [ H | [ H | H ]]; rewrite H
    end.

  The idea of encoding a triple as {{x},{x,y},{x,y,z}} seems to generates
  too many cases to show bijections

  Fact is_triple_inj p x y z x' y' z' : 
              is_triple p x y z  
           -> is_triple p x' y' z'
           -> x ≈ y' /\ y ≈ x' /\ z ≈ z'
           \/ x ≈ x' /\ y ≈ z' /\ z ≈ y'
           \/ x ≈ z' /\ y ≈ y' /\ z ≈ x'

           \/ x ≈ x' /\ y ≈ y' /\ z ≈ z'
           \/ x ≈ y' /\ y ≈ z' /\ z ≈ x'
           \/ x ≈ z' /\ y ≈ x' /\ z ≈ y'

           \/ x ≈ x' /\ x ≈ y' /\ y ≈ z' /\ z ≈ z'
           \/ x ≈ x' /\ x ≈ z' /\ y ≈ y' /\ z ≈ y'
           \/ x ≈ y' /\ x ≈ z' /\ y ≈ x' /\ z ≈ x'
           \/ x ≈ x' /\ z ≈ x' /\ y ≈ y' /\ y ≈ z'.
  Proof.
    unfold is_triple; intros H1 H2.
    generalize (proj1 (H2 x)) (proj1 (H2 y)) (proj1 (H2 z)); rewrite H1, H1, H1, equiv_refl_True, equiv_refl_True, equiv_refl_True.
    generalize (proj1 (H1 x')) (proj1 (H1 y')) (proj1 (H1 z')); rewrite H2, H2, H2, equiv_refl_True, equiv_refl_True, equiv_refl_True.
    clear H1 H2.
    repeat match goal with 
     |- (_ -> ?t) -> _ => let H := fresh in let G := fresh in intros H; assert (G : t); [ apply H; auto | ]; clear H
    end.
    repeat match goal with H: _ \/ _ \/ _ |- _ => revert H end.
    repeat (myintro; rsimpl; auto).
    myintro.
    
    do 6 (intros [|[]]; auto; collect_equiv; eliminate; repeat rewrite id_rew; try tauto). [|[]] [|[]] [|[]] [|[]] [|[]]; auto; collect_equiv.
    eliminate.
    eliminate.
    find_trans.
     match goal with
      | H : ?x ≈ ?y |- context[?x ≈ ?y] => rewrite (@id_rew x y); auto
     end.
  Qed.
*)


  Definition m2_is_opair p x y := exists a b, m2_is_pair a x x /\ m2_is_pair b x y /\ m2_is_pair p a b.

  Add Parametric Morphism: (m2_is_opair) with signature 
     (m2_equiv) ==> (m2_equiv) ==> (m2_equiv) ==> (iff) as m2_is_opair_congr.
  Proof.
    intros p q H1 x x' H2 y y' H3.
    apply exists_equiv; intros a.
    apply exists_equiv; intros b.
    rewrite H1, H2, H3; tauto.
  Qed.

  Fact m2_is_opair_fun p q x y : m2_is_opair p x y -> m2_is_opair q x y -> p ≈ q.
  Proof.
    intros (a & b & H1 & H2 & H3) (u & v & G1 & G2 & G3).
    generalize (m2_is_pair_fun H1 G1) (m2_is_pair_fun H2 G2); intros E1 E2.
    rewrite E1, E2 in H3.
    revert H3 G3; apply m2_is_pair_fun.
  Qed.

  Fact m2_is_opair_inj p x y x' y' : m2_is_opair p x y 
                                  -> m2_is_opair p x' y' 
                                  -> x ≈ x' /\ y ≈ y'.
  Proof.
    intros (a & b & H1 & H2 & H3) (u & v & G1 & G2 & G3).
    generalize (m2_is_pair_inj H3 G3); intros [ (E1 & E2) | (E1 & E2) ].
    + rewrite E1 in H1; rewrite E2 in H2.
      generalize (m2_is_pair_inj' H1 G1); intros E; split; auto.
      rewrite E in H2.
      generalize (m2_is_pair_inj H2 G2); intros [ | (E3 & E4) ]; try tauto.
      rewrite E4; auto.
    + rewrite E1 in H1; rewrite E2 in H2.
      generalize (m2_is_pair_inj H2 G1) (m2_is_pair_inj H1 G2).
      intros [ (E3 & E4) | (E3 & E4) ] [ (E5 & E6) | (E5 & E6) ];
        rewrite E4, <- E5; auto.
  Qed.

  Definition m2_is_otriple t x y z := exists p, m2_is_opair p x y /\ m2_is_opair t p z.
 
  Add Parametric Morphism: (m2_is_otriple) with signature 
     (m2_equiv) ==> (m2_equiv) ==> (m2_equiv) ==> (m2_equiv) ==> (iff) as m2_is_otriple_congr.
  Proof.
    intros p q H1 x x' H2 y y' H3 z z' H4.
    unfold m2_is_otriple.
    apply exists_equiv; intros t.
    rewrite H1, H2, H3, H4; tauto.
  Qed.

  Fact m2_is_otriple_fun p q x y z : m2_is_otriple p x y z -> m2_is_otriple q x y z -> p ≈ q.
  Proof.
    intros (t1 & H1 & H2) (t2 & H3 & H4).
    generalize (m2_is_opair_fun H1 H3); intros E.
    rewrite E in H2.
    apply (m2_is_opair_fun H2 H4).
  Qed.

  Fact m2_is_otriple_inj t x y z x' y' z' : 
             m2_is_otriple t x y z 
          -> m2_is_otriple t x' y' z' 
          -> x ≈ x' /\ y ≈ y' /\ z ≈ z'.
  Proof.
    intros (p & H1 & H2) (q & H3 & H4).
    destruct (m2_is_opair_inj H2 H4) as (H5 & H6).
    rewrite H5 in H1.
    generalize (m2_is_opair_inj H1 H3); tauto.
  Qed.

  Definition m2_has_pairs (l : X) :=
     forall x y, x ∈ l -> y ∈ l -> exists p, m2_is_pair p x y.

  Definition m2_has_otriples (l : X) :=
    forall x y z, x ∈ l -> y ∈ l -> z ∈ l -> exists t, m2_is_otriple t x y z.

  Definition m2_is_otriple_in r x y z :=
    exists t, m2_is_otriple t x y z /\ t ∈ r.

  Definition m2_powset (l m : X) := forall x, x ∈ m <-> x ⊆ l.

  Add Parametric Morphism: (m2_powset) with signature 
     (m2_equiv) ==> (m2_equiv) ==> (iff) as m2_is_powset_congr.
  Proof.
    intros x y H1 a b H2; unfold m2_powset.
    apply forall_equiv; intro.
    rewrite H1, H2; tauto.
  Qed.

  (** First order axioms *)

  Variable (empty : exists x, forall y, y ∉ x).
 
  Variable (l0 l1 l2 l3 : X).     (** a layered model of level 4 *)
  Variable (pset1 : m2_powset l0 l1)
           (pset2 : m2_powset l1 l2)
           (pset3 : m2_powset l2 l3)
           (hp0 : m2_has_pairs l0)   (** pairs at every level below 3 *)
           (hp1 : m2_has_pairs l1)
           (hp2 : m2_has_pairs l2).

  Fact m2_is_pair_layer p x y l pl : x ∈ l -> y ∈ l -> m2_is_pair p x y -> m2_powset l pl -> p ∈ pl.
  Proof.
    intros H1 H2 H3 H4; apply H4; red in H3.
    intros k; rewrite H3; intros [ H | H ]; rewrite H; auto.
  Qed.

  Fact m2_is_opair_l2 p x y : x ∈ l0 -> y ∈ l0 -> m2_is_opair p x y -> p ∈ l2.
  Proof.
    intros H1 H2 (a & b & H3 & H4 & H5).
    apply m2_is_pair_layer with (4 := pset1) in H3; auto.
    apply m2_is_pair_layer with (4 := pset1) in H4; auto.
    apply m2_is_pair_layer with (4 := pset2) in H5; auto.
  Qed.
   
  Variable (r : X) (Hr : r ∈ l3). (** r encodes a binary relation *)

  Definition m2_P x y := x ∈ l0 /\ y ∈ l0 /\ exists c, c ∈ r /\ m2_is_opair c x y. 

  (** We want to show that (encode A) satisfied in this model
           -> A true in the model where P as defined above 
                is the binary relation *)

End membership. 
