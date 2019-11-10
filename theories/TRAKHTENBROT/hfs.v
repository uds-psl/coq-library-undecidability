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
  Require Import utils_list.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import wf_finite wf_chains.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops.

Set Implicit Arguments.

Local Definition forall_equiv X := @fol_quant_sem_ext X fol_fa.
Local Definition exists_equiv X := @fol_quant_sem_ext X fol_ex.

Section axioms.

  Reserved Notation "⟬ s , t ⟭" (at level 1, format "⟬ s , t ⟭").
  Reserved Notation "x ∪ y" (at level 61, left associativity).

  Reserved Notation "x ≈ y" (at level 70, no associativity).
  Reserved Notation "x ≉ y" (at level 70, no associativity).
  Reserved Notation "x ∈ y" (at level 70, no associativity).
  Reserved Notation "x ∉ y" (at level 70, no associativity).
  Reserved Notation "x ⊆ y" (at level 70, no associativity).

  Variable (X : Type) (R : X -> X -> Prop).

  Infix "∈" := R.
  Notation "x ∉ y" := (~ x ∈ y).

  Definition incl x y := forall a, a ∈ x -> a ∈ y.
  Definition equiv x y := forall a, a ∈ x <-> a ∈ y.

  Infix "⊆" := incl.
  Infix "≈" := equiv. 
  Notation "x ≉ y" := (~ x ≈ y).

  (** Hypothesis on the model *)

  Variable (Rdec : forall x y, { x ∈ y } + { x ∉ y })
           (lX : list X) (HX : forall x, In x lX).

  Fact incl_refl x : x ⊆ x.
  Proof. red; auto. Qed.

  Fact incl_trans x y z : x ⊆ y -> y ⊆ z -> x ⊆ z.
  Proof. unfold incl; auto. Qed.

  Fact incl_choose x y : { z | z ∈ x /\ z ∉ y } + { x ⊆ y }.
  Proof.
    set (P z := z ∈ x /\ z ∉ y).
    set (Q z := z ∈ x -> z ∈ y).
    destruct list_dec with (P := P) (Q := Q) (l := lX)
      as [ (z & _ & H2 & H3) | H ]; unfold P, Q in *; clear P Q.
    + intros z; destruct (Rdec z x); destruct (Rdec z y); tauto.
    + left; exists z; auto.
    + right; intros z; apply H; auto.
  Qed.  

  Fact incl_dec x y : { x ⊆ y } + { ~ x ⊆ y }.
  Proof.
    destruct (incl_choose x y) as [ (?&?&?) |]; auto.
  Qed.

  Fact equiv_eq x y : x ≈ y <-> x ⊆ y /\ y ⊆ x.
  Proof. firstorder. Qed.
  
  Fact equiv_dec x y : { x ≈ y } + { x ≉ y }.
  Proof.
    destruct (incl_dec x y); [ destruct (incl_dec y x) | ].
    1: left; apply equiv_eq; auto. 
    all: right; rewrite equiv_eq; tauto.
  Qed.

  Fact equiv_refl_True x : x ≈ x <-> True.
  Proof. unfold equiv; tauto. Qed.

  Fact equiv_refl x : x ≈ x.
  Proof. unfold equiv; tauto. Qed.

  Fact equiv_sym x y : x ≈ y -> y ≈ x.
  Proof. do 2 rewrite equiv_eq; tauto. Qed.

  Fact equiv_trans x y z : x ≈ y -> y ≈ z -> x ≈ z.
  Proof. repeat rewrite equiv_eq; unfold incl; intros [] []; split; auto. Qed.

  Add Parametric Relation: (X) (equiv)
      reflexivity proved by equiv_refl
      symmetry proved by equiv_sym
      transitivity proved by equiv_trans
    as equiv_rst.

  Hint Resolve equiv_refl equiv_sym.

  (* A first FOL axiom: sets are characterized by their elements *)

  Variable (ax_equiv : forall x y z, x ≈ y -> x ∈ z -> y ∈ z).

  Fact equiv_mem x y : x ≈ y -> forall z, x ∈ z <-> y ∈ z.
  Proof. split; apply ax_equiv; auto. Qed.
  
   Add Parametric Morphism: (R) with signature 
     (equiv) ==> (equiv) ==> (iff) as mem_congr.
  Proof.
    intros x y H1 a b H2; red in H1, H2; split;
     rewrite <- H2; apply ax_equiv; auto.
  Qed.

  Add Parametric Morphism: (fun x y => x ⊆ y) with signature 
     (equiv) ==> (equiv) ==> (iff) as is_incl_congr.
  Proof.
    intros x y H1 a b H2; split; intros H z.
    + rewrite <- H1, <- H2; auto.
    + rewrite H1, H2; auto.
  Qed.

  Definition is_pair p x y := forall a, a ∈ p <-> a ≈ x \/ a ≈ y.

  Fact is_pair_comm p x y : is_pair p x y -> is_pair p y x.
  Proof. unfold is_pair; apply forall_equiv; intro; tauto. Qed.

  Add Parametric Morphism: (is_pair) with signature 
     (equiv) ==> (equiv) ==> (equiv) ==> (iff) as is_pair_congr.
  Proof.
    intros p q H1 x x' H2 y y' H3.
    unfold is_pair.
    apply forall_equiv; intros a.
    rewrite H1, H2, H3; tauto.
  Qed.

  Fact is_pair_fun p q x y : is_pair p x y -> is_pair q x y -> p ≈ q.
  Proof.
    intros H1 H2; red in H1, H2; intro; 
    rewrite H1, H2; tauto.
  Qed.

  Fact is_pair_inj p x y x' y' : is_pair p x y 
                              -> is_pair p x' y' 
                              -> x ≈ x' /\ y ≈ y'
                              \/ x ≈ y' /\ y ≈ x'.
  Proof.
    unfold is_pair; intros H1 H2.
    generalize (proj1 (H2 x)) (proj1 (H2 y)); rewrite H1, H1, equiv_refl_True, equiv_refl_True.
    generalize (proj1 (H1 x')) (proj1 (H1 y')); rewrite H2, H2, equiv_refl_True, equiv_refl_True.
    intros [] [] [] []; auto.
  Qed.

  Fact is_pair_inj' p x y : is_pair p x x 
                         -> is_pair p y y
                         -> x ≈ y.
  Proof.
    intros H1 H2; generalize (is_pair_inj H1 H2); tauto.
  Qed.

  Definition is_opair p x y := exists a b, is_pair a x x /\ is_pair b x y /\ is_pair p a b.

  Add Parametric Morphism: (is_opair) with signature 
     (equiv) ==> (equiv) ==> (equiv) ==> (iff) as is_opair_congr.
  Proof.
    intros p q H1 x x' H2 y y' H3.
    unfold is_opair.
    apply exists_equiv; intros a.
    apply exists_equiv; intros b.
    rewrite H1, H2, H3; tauto.
  Qed.

  Fact is_opair_fun p q x y : is_opair p x y -> is_opair q x y -> p ≈ q.
  Proof.
    intros (a & b & H1 & H2 & H3) (u & v & G1 & G2 & G3).
    generalize (is_pair_fun H1 G1) (is_pair_fun H2 G2); intros E1 E2.
    rewrite E1, E2 in H3.
    revert H3 G3; apply is_pair_fun.
  Qed.

  Fact is_opair_inj p x y x' y' : is_opair p x y 
                               -> is_opair p x' y' 
                               -> x ≈ x' /\ y ≈ y'.
  Proof.
    intros (a & b & H1 & H2 & H3) (u & v & G1 & G2 & G3).
    generalize (is_pair_inj H3 G3); intros [ (E1 & E2) | (E1 & E2) ].
    + rewrite E1 in H1; rewrite E2 in H2.
      generalize (is_pair_inj' H1 G1); intros E; split; auto.
      rewrite E in H2.
      generalize (is_pair_inj H2 G2); intros [ | (E3 & E4) ]; try tauto.
      rewrite E4; auto.
    + rewrite E1 in H1; rewrite E2 in H2.
      generalize (is_pair_inj H2 G1) (is_pair_inj H1 G2).
      intros [ (E3 & E4) | (E3 & E4) ] [ (E5 & E6) | (E5 & E6) ];
        rewrite E4, <- E5; auto.
  Qed.

  Definition has_pairs (l : X) :=
     forall x y, x ∈ l -> y ∈ l -> exists p, is_pair p x y.

  Definition powset (l m : X) := forall x, x ∈ m <-> x ⊆ l.

  Add Parametric Morphism: (powset) with signature 
     (equiv) ==> (equiv) ==> (iff) as is_powset_congr.
  Proof.
    intros x y H1 a b H2; unfold powset.
    apply forall_equiv; intro.
    rewrite H1, H2; tauto.
  Qed.

  (** First order axioms *)

  Variable (empty : exists x, forall y, y ∉ x).
 
  Variable (l0 l1 l2 l3 : X).     (** a layered model of level 4 *)
  Variable (pset1 : powset l0 l1)
           (pset2 : powset l1 l2)
           (pset3 : powset l2 l3)
           (hp0 : has_pairs l0)   (** pairs at every level below 3 *)
           (hp1 : has_pairs l1)
           (hp2 : has_pairs l2).

  Fact is_pair_layer p x y l pl : x ∈ l -> y ∈ l -> is_pair p x y -> powset l pl -> p ∈ pl.
  Proof.
    intros H1 H2 H3 H4; apply H4; red in H3.
    intros k; rewrite H3; intros [ H | H ]; rewrite H; auto.
  Qed.

  Fact is_opair_l2 p x y : x ∈ l0 -> y ∈ l0 -> is_opair p x y -> p ∈ l2.
  Proof.
    intros H1 H2 (a & b & H3 & H4 & H5).
    apply is_pair_layer with (4 := pset1) in H3; auto.
    apply is_pair_layer with (4 := pset1) in H4; auto.
    apply is_pair_layer with (4 := pset2) in H5; auto.
  Qed.
   
  Variable (r : X) (Hr : r ∈ l3). (** r encodes a binary relation *)

  Definition P x y := x ∈ l0 /\ y ∈ l0 /\ exists c, c ∈ r /\ is_opair c x y. 

  (** We want to show that (encode A) satisfied in this model
           -> A true in the model where P as defined above 
                is the binary relation *)

End axioms. 

Section btree.

  (* Unary ops *)

  Reserved Notation "⌞ x ⌟" (at level 0, format "⌞ x ⌟").
  Reserved Notation "↓ x"   (at level 1, format "↓ x").
  Reserved Notation "x †"   (at level 1, format "x †").

  Reserved Notation "⟬ s , t ⟭" (at level 1, format "⟬ s , t ⟭").

  (* Infix Binary ops *)
 
  Reserved Notation "x ∙ y"  (at level 2, right associativity, format "x ∙ y").
  Reserved Notation "x ⪧ y" (at level 2, right associativity, format "x ⪧ y").
  Reserved Notation "x → y" (at level 2, right associativity, format "x → y").

  Reserved Notation "x ∪ y" (at level 61, left associativity).

  (* Infix Binary rels *)

  Reserved Notation "x ≈ y" (at level 70, no associativity).
  Reserved Notation "x ≉ y" (at level 70, no associativity).
  Reserved Notation "x ≾ y" (at level 70, no associativity).
  Reserved Notation "x ∈ y" (at level 70, no associativity).
  Reserved Notation "x ∉ y" (at level 70, no associativity).
  Reserved Notation "x ⋷ y" (at level 70, no associativity).
  Reserved Notation "x ≺ y" (at level 70, no associativity).
  Reserved Notation "x ⊆ y" (at level 70, no associativity).

  (* ⌞ ⌟ ∅ ⪧ ≈ ≉ ∈ ∉ ⋷  ≾ ≺ ε ∙ ∊ *)

  Inductive bt : Set := bt_leaf | bt_node : bt -> bt -> bt.

  Notation "∅" := bt_leaf.

  Infix "∙" := bt_node.  (* replaced with a non symmetric notation *)
  Infix "⪧" := bt_node.

  (** Indeed x⪧t represent {x}∪t *)

  Section bt_rect'.

    (** When we inspect bt as lists, we can switch to this principle 

        In fact, btrees code HF-sets like this

            {x1,...,xn} = x1⪧...⪧xn⪧∅

        We could also use rose-trees but may be this would be more
        difficult ?
     *)

    Variables (P : bt -> Type) 
              (HP0 : P ∅)
              (HP1 : forall x t, P t -> P (x⪧t)).
  
    Theorem bt_rect' t : P t.
    Proof. induction t; auto. Qed.

  End bt_rect'.
   
  Fact bt_eq_dec (s t : bt) : { s = t } + { s <> t }.
  Proof. decide equality. Qed.

  Fixpoint bt_depth t :=
    match t with
      | ∅   => 0
      | r⪧s => max (S ⌞r⌟) ⌞s⌟
    end
  where "⌞ t ⌟" := (bt_depth t).

  Print bt_depth.

  Check (fun x => ⌞x⌟).

  (* ⌞ ⌟ ∅ ⪧ ≈ *)

  Inductive bt_equiv : bt -> bt -> Prop :=
    | in_bte_refl : forall s,             s ≈ s
    | in_bte_sym  : forall s t,           s ≈ t
                                       -> t ≈ s
    | in_bte_tran : forall r s t,         r ≈ s
                                       -> s ≈ t
                                       -> r ≈ t
    | in_bte_cntr : forall s t,       s⪧s⪧t ≈ s⪧t
    | in_bte_comm : forall s t u,     s⪧t⪧u ≈ t⪧s⪧u
    | in_bte_cngr : forall s s' t t',     s ≈ s'
                                       -> t ≈ t'
                                   ->   s⪧t ≈ s'⪧t'
  where "s ≈ t" := (bt_equiv s t).

  Notation "s ≉ t" := (~ s ≈ t).

  Notation bte_refl := in_bte_refl.
  Notation bte_trans := in_bte_tran.
 
  Hint Constructors bt_equiv.

  Fact bte_sym x y : x ≈ y <-> y ≈ x.
  Proof. split; auto. Qed.

  Fact bte_leaf_eq s t : s ≈ t -> (s = ∅ <-> t = ∅).
  Proof. induction 1; try tauto; split; discriminate. Qed.

  Fact bte_discr s t : s⪧t ≉ ∅.
  Proof. 
   intros H; apply bte_leaf_eq in H.
   generalize (proj2 H eq_refl); discriminate.
  Qed.

  Fact bte_inv_0 s : s ≈ ∅ <-> s = ∅.
  Proof.
    split.
    + intros H; destruct s; auto.
      apply bte_discr in H; tauto.
    + intros ->; auto.
  Qed.

  (* s belongs to t if adding s to t does not change t *)

  Notation "s ∈ t" := (s⪧t ≈ t).
  Notation "s ∉ t" := (~ s ∈ t).

  (* ⌞ ⌟ ∅ ⪧ ≈  ∈ ⋷  *)

  Section establishing_membership_inversion.

    (* A restricted definition of membership, not up to equivalence *)

    Inductive bt_restr_mem : bt -> bt -> Prop :=
      | in_btrm_0 : forall s t,            s ⋷ s⪧t
      | in_btrm_1 : forall s t u, s ⋷ u -> s ⋷ t⪧u
    where "s ⋷ t" := (bt_restr_mem s t).

    Hint Constructors bt_restr_mem.

    Fact btrm_inv u s t : u ⋷ s⪧t <-> u = s \/ u ⋷ t.
    Proof.
      split.
      + inversion 1; auto.
      + intros [ <- | ]; constructor; auto.
    Qed.

    Notation "s ≾ t" := (forall u, u ⋷ s -> exists v, v ⋷ t /\ u ≈ v).

    Fact bt_rincl_refl s : s ≾ s.
    Proof. intros u; exists u; auto. Qed.

    Fact bt_rincl_trans r s t : r ≾ s -> s ≾ t -> r ≾ t.
    Proof.
      intros H1 H2 u Hu.
      destruct H1 with (1 := Hu) as (v & Hv & H3).
      destruct H2 with (1 := Hv) as (w & ? & ?).
      exists w; split; auto.
      apply bte_trans with v; auto.
    Qed.

    Hint Resolve bt_rincl_refl bt_rincl_trans.

    Lemma bte_rincl s t : s ≈ t -> s ≾ t.
    Proof.
      intros H.
      assert (s ≾ t /\ t ≾ s) as K; [ | apply K ].
      induction H as [ s | s t H IH | r s t H1 [] H2 [] 
                     | s t | s t u | s s' t t' H1 [H2 H3] H4 [H5 H6] ]; 
        auto; try tauto.
      + split; apply bt_rincl_trans with s; auto.
      + split; intros u; rewrite btrm_inv; intros [ <- | ]; exists u; auto.
      + split; intros v; rewrite btrm_inv; intros [ <- | ]; exists v; auto;
          revert H; rewrite btrm_inv; intros [ <- | ]; auto.
      + split.
        * intros u; rewrite btrm_inv.
          intros [ <- | ].
          - exists s'; auto.
          - destruct (H5 _ H) as (v & ? & ?); exists v; auto.
        * intros u; rewrite btrm_inv.
          intros [ <- | ].
          - exists s; auto.
          - destruct (H6 _ H) as (v & ? & ?); exists v; auto.
    Qed.
 
    Fact btrm_btm s t : s ⋷ t -> s ∈ t.
    Proof.
      induction 1 as [ | s t u ]; try (constructor; auto; fail).
      constructor; apply bte_trans with (t⪧s⪧u); auto.
    Qed.

    Hint Resolve btrm_btm.

    Fact btm_congr_l s t u : s ≈ t -> s ∈ u -> t ∈ u.
    Proof.
      intros H1 H2.
      apply bte_trans with (2 := H2); auto.
    Qed.

    Fact btm_congr_r s t u : s ≈ t -> u ∈ s -> u ∈ t.
    Proof.
      intros H1 H2.
      apply bte_trans with (2 := H1),
            bte_trans with (2 := H2); auto.
    Qed.

    Fact btm_inv_0 s : s ∈ ∅ <-> False.
    Proof. split; try tauto; apply bte_discr. Qed.

    Fact btm_inv u s t : u ∈ s⪧t <-> u ≈ s \/ u ∈ t.
    Proof.
      split.
      + intros H.
        destruct (@bte_rincl _ _ H u) as (v & H1 & ?); auto.
        revert H1; rewrite btrm_inv; intros [ <- | ]; auto.
        right; apply bte_trans with (v⪧t); auto.
      + intros [ H | H ].
        * apply btm_congr_l with s; auto.
        * apply bte_trans with (1 := in_bte_comm _ _ _); auto.
    Qed.

  End establishing_membership_inversion.

  Tactic Notation "btm" "simpl" :=
    repeat match goal with
      | |- context[_ ∈ _ ⪧ _] => rewrite btm_inv; auto; try tauto
      | |- context[_ ∈ ∅]    => rewrite btm_inv_0; auto; try tauto
    end.

  Section establishing_decidability.

    Inductive bt_lt : bt -> bt -> Prop :=
      | in_btlt_0 : forall s t,                   ∅ ≺ s⪧t 
      | in_btlt_1 : forall s s' t t', s ≺ s' -> s⪧t ≺ s'⪧t'
      | in_btlt_2 : forall s t t',    t ≺ t' -> s⪧t ≺ s⪧t'
    where "s ≺ t" := (bt_lt s t).

    Hint Constructors bt_lt.

    Fact bt_lt_irrefl s : ~ s ≺ s.
    Proof.
      intros H.
      assert (forall t, s ≺ t -> s <> t) as D; 
        [ | apply D in H; destruct H; auto ].
      clear H; induction 1 as [ s t | s s' t t' H IH | s t t' H IH ]; 
        try discriminate; contradict IH; inversion IH; auto.
    Qed.

    Fact bt_lt_trans r s t : r ≺ s -> s ≺ t -> r ≺ t.
    Proof.
      intros H1; revert H1 t.
      induction 1; inversion 1; auto.
    Qed.
  
    Fact bt_lt_eq_lt_dec s t : { s ≺ t } + { s = t } + { t ≺ s }.
    Proof.
      revert t; induction s as [ | s1 H1 s2 H2 ] using bt_rect; intros [ | t1 t2 ]; auto.
      destruct (H1 t1) as [ [] | ]; auto;
        destruct (H2 t2) as [ [] | ]; subst; auto.
    Qed.

    Fixpoint bt_insert s t : bt :=
      match t with
        | ∅   => s⪧∅
        | t⪧u => match bt_lt_eq_lt_dec s t with
          | inleft (left _)  => s⪧t⪧u
          | inleft (right _) => t⪧u
          | inright _        => t⪧(s→u)
        end
      end
    where "s → t" := (bt_insert s t).

    Fact bt_lt_eq_lt_dec_refl s : exists H, bt_lt_eq_lt_dec s s = inleft (right H).
    Proof.
      destruct (bt_lt_eq_lt_dec s s) as [ [ C | H ] | C ].
      1,3: exfalso; revert C; apply bt_lt_irrefl.
      exists H; auto.
    Qed.

    Ltac bt_lt_eq H := 
      match goal with 
        |- context [bt_lt_eq_lt_dec ?x ?x] 
             => destruct (bt_lt_eq_lt_dec_refl x) as (H & ->)
      end.

    Fact bt_insert_leaf s : s→∅ = s⪧∅.
    Proof. reflexivity. Qed.

    Fact bt_insert_eq s t : s→s⪧t = s⪧t.
    Proof. simpl; bt_lt_eq H; auto. Qed.

    Fact bt_insert_lt s t u : s ≺ t -> s→t⪧u = s⪧t⪧u.
    Proof.
      intros H; simpl.
      destruct (bt_lt_eq_lt_dec s t) as [ [C|C] | C ]; auto.
      + contradict H; subst; apply bt_lt_irrefl.
      + destruct (@bt_lt_irrefl s); apply bt_lt_trans with t; auto.
    Qed.

    Fact bt_insert_gt s t u : t ≺ s -> s→t⪧u = t⪧(s→u).
    Proof.
      intros H; simpl.
      destruct (bt_lt_eq_lt_dec s t) as [ [C|C] | C ]; auto.
      + destruct (@bt_lt_irrefl s); apply bt_lt_trans with t; auto.
      + contradict H; subst; apply bt_lt_irrefl.
    Qed.

    Fact bt_insert_equiv s t : s→t ≈ s⪧t.
    Proof.
      induction t as [ | t u Hu ] using bt_rect'; simpl; auto.
      destruct (bt_lt_eq_lt_dec s t) as [ [] | ]; subst; auto.
      apply bte_trans with (t⪧s⪧u); auto.
    Qed.

    Fixpoint bt_norm t :=
      match t with
        | ∅   => ∅
        | s⪧t => s† → t†
      end
    where "t †" := (bt_norm t).

    Hint Resolve bt_insert_equiv.
  
    Fact bt_norm_eq t : t† ≈ t.
    Proof.
      induction t as [ | s ? t ? ]; simpl; auto.
      apply bte_trans with (s†⪧t†); auto.
    Qed.

    Opaque bt_insert.

    Tactic Notation "rew" "bt" "insert" := 
      repeat match goal with 
        |             |- context[_→∅]     => rewrite bt_insert_leaf
        |             |- context[?x→?x⪧_] => rewrite bt_insert_eq
        | H : ?x ≺ ?y |- context[?x→?y⪧_] => rewrite bt_insert_lt with (1 := H)
        | H : ?x ≺ ?y |- context[?y→?x⪧_] => rewrite bt_insert_gt with (1 := H)
      end.

    Tactic Notation "bt" "insert" "case" hyp(x) hyp(y) :=
      destruct (bt_lt_eq_lt_dec x y) as [ [|] | ]; subst; rew bt insert; auto.

    Tactic Notation "bt" "lt" "trans" constr(t) := apply bt_lt_trans with t; auto.

    Tactic Notation "bt" "lt" "cycle" :=
      match goal with
        | H1 : ?x ≺ ?x |- _  => destruct (@bt_lt_irrefl x); auto
        | H1 : ?x ≺ ?y, 
          H2 : ?y ≺ ?x |- _  => destruct (@bt_lt_irrefl x); bt lt trans y
        | H1 : ?x ≺ ?y,
          H2 : ?y ≺ ?z,
          H3 : ?z ≺ ?x |- _  => destruct (@bt_lt_irrefl x); bt lt trans y; bt lt trans z
      end.

    Fact bt_insert_cntr s t : s→s→t = s→t.
    Proof.
      induction t as [ | t1 t2 IH2 ] using bt_rect'; rew bt insert; auto.
      bt insert case s t1; f_equal; auto.
    Qed.

    Fact bt_insert_comm s t u : s→t→u = t→s→u.
    Proof.
      induction u as [ | u1 u2 IH ] using bt_rect'. 
      + rew bt insert; bt insert case s t.
      + bt insert case t u1; 
        bt insert case s u1; 
        bt insert case s t; 
        try bt lt cycle; 
        f_equal; auto.
    Qed.

    Hint Resolve bt_insert_cntr bt_insert_comm bt_norm_eq.

    Theorem bte_norm_iff s t : s ≈ t <-> s† = t†.
    Proof.
      split.
      + induction 1; simpl; auto.
        * transitivity s†; auto.
        * f_equal; auto.
      + intros H.
        apply bte_trans with s †; auto.
        rewrite H; auto.
    Qed.

    Theorem bt_norm_idem s : s†† = s†.
    Proof. apply bte_norm_iff; auto. Qed.

    Theorem bte_dec s t : { s ≈ t } + { s ≉ t }.
    Proof.
      destruct (bt_eq_dec s† t†) as [ H | H ];
      rewrite <- bte_norm_iff in H; auto.
    Qed.

  End establishing_decidability.

  Corollary btm_dec s t : { s ∈ t } + { s ∉ t }.
  Proof. apply bte_dec. Qed.

  Section more_decidability.

    Section btm_ex_dec.
  
      Variable (P : bt -> Prop) (HP : forall s t, s ≈ t -> P s -> P t).

      (** Exist. quantification over subsets *)

      Theorem btm_ex_dec t : (forall x, x ∈ t -> { P x } + { ~ P x })
                       -> { s | s ∈ t /\ P s } + { forall s, s ∈ t -> ~ P s }.
      Proof.
        induction t as [ | s t IHt ] using bt_rect'; intros Ht.
        + right; intros ?; btm simpl.
        + destruct (Ht s) as [ H | H ]; auto.
          * left; exists s; auto.
          * destruct IHt as [ (x & H1 & H2) | H1 ].
            - intros x Hx; apply Ht; btm simpl.
            - left; exists x; btm simpl.
            - right; intros x; btm simpl.
              intros [ | ]; auto.
              contradict H; revert H; apply HP; auto.
      Qed.

    End btm_ex_dec.

    (** Univ. quantification of subsets *)

    Corollary btm_fa_dec (P : _ -> Prop) t : 
                             (forall s t, s ≈ t -> P s -> P t)
                          -> (forall x, x ∈ t -> { P x } + { ~ P x })
                          -> { s | s ∈ t /\ ~ P s } + { forall s, s ∈ t -> P s }.
    Proof.
      intros H1 H2.
      destruct btm_ex_dec with (P := fun x => ~ P x) (t := t)
        as [ H | H ]; auto.
      + intros u v G1 G2; contradict G2; revert G2; apply H1; auto.
      + intros x Hx; specialize (H2 _ Hx); tauto.
      + right; intros s Hs; specialize (H _ Hs).
        destruct (H2 _ Hs); tauto.
    Qed.

    (** Decidable separation *)

    Definition btm_select (P : _ -> Prop) t :
                             (forall s t, s ≈ t -> P s -> P t)
                          -> (forall x, x ∈ t -> { P x } + { ~ P x })
                          -> { s | forall x, x ∈ s <-> x ∈ t /\ P x }.
    Proof.
      intros HP0.
      induction t as [ | s t Ht ] using bt_rect'; intros HP.
      + exists ∅; intros s; btm simpl.
      + destruct Ht as (t' & H').
        * intros x Hx; apply HP; btm simpl.
        * destruct (HP s) as [ H | H ]; auto.
          - exists (s⪧t'); intros x; btm simpl.
            rewrite H'.
            split; try tauto.
            intros [ H1 | (H1 & H2) ]; auto.
            split; auto.
            revert H; apply HP0; auto.
          - exists t'; intros x; rewrite H'; btm simpl.
            split; try tauto.
            intros ([H1|H1] & H2); split; auto.
            contradict H; revert H2; apply HP0; auto.
    Qed.

    (** When x ∈ s, one can compute t st s = {x} U t /\ x ∉ t *)
  
    Definition btm_partition x s : x ∈ s -> { t | s ≈ x⪧t /\ x ∉ t }.
    Proof.
      induction s as [ | y s IHs ] using bt_rect'.
      + intros H; exfalso; revert H; btm simpl.
      + intros H; rewrite btm_inv in H.
        destruct (bte_dec x y) as [ H1 | H1 ]; 
        destruct (btm_dec x s) as [ H2 | H2 ]; try (exfalso; tauto). 
        * destruct (IHs H2) as (t & H3 & H4).
          exists t; split; auto.
          apply bte_trans with (y⪧x⪧t); auto.
          btm simpl.
        * exists s; auto.
        * destruct (IHs H2) as (t & H3 & H4).
          exists (y⪧t); split; auto.
          - apply bte_trans with (y⪧x⪧t); auto.
          - contradict H4; revert H4; btm simpl.
    Qed.

  End more_decidability.

  Notation "∈-chain" := (chain (fun s t => s ∈ t)).
  Notation "∈-chain_list" := (chain_list (fun s t => s ∈ t)).

  Section bte_depth_and_chains.

    Opaque max.

    (** Well-foundness *)

    Fact bte_depth_eq s t : s ≈ t -> ⌞s⌟ = ⌞t⌟.
    Proof.
      induction 1; simpl; auto.
      + transitivity ⌞s⌟; auto.
      + rewrite max_assoc, max_idempotent; auto.
      + rewrite max_assoc, (max_comm (S _)), max_assoc; auto.
    Qed.

    Fact btm_depth s t : s ∈ t -> ⌞s⌟ < ⌞t⌟.
    Proof.
      intros H; apply bte_depth_eq in H. 
      rewrite <- H; simpl.
      apply lt_le_trans with (1 := lt_n_Sn _).
      apply le_max_l.
    Qed.

    (** bt is well-founded for ∈ *)

    Theorem btm_wf : well_founded (fun s t => s ∈ t).
    Proof.
      apply wf_incl with (1 := btm_depth),
            wf_inverse_image, lt_wf.
    Qed.

    Fact btm_chain_depth n s t : ∈-chain n s t -> n+⌞s⌟ <= ⌞t⌟.
    Proof.
      induction 1 as [ | n s t u H1 H2 IH2 ]; auto.
      apply le_trans with (2 := IH2).
      apply btm_depth in H1; lia.
    Qed.

    Fact btm_chain_congr_r n s t t' : t ≈ t' -> ∈-chain (S n)  s t -> ∈-chain (S n) s t'.
    Proof.
      intros H1 H2.
      apply chain_snoc_inv in H2.
      destruct H2 as (y & H2 & H3).
      apply chain_snoc with y; auto.
      revert H3; apply btm_congr_r; auto.
    Qed.

    Fact btm_chain_list_comp u l s t : l <> nil
                              -> ∈-chain_list l s t
                              -> ∈-chain_list l s (u⪧t).
    Proof.
      rewrite <- (rev_involutive l).
      generalize (rev l); clear l; intros l Hl.
      destruct l as [ | x l ].
      { destruct Hl; auto. }
      clear Hl.
      simpl; intros H.
      apply chain_list_app_inv in H.
      destruct H as (v & H1 & H2).
      apply chain_list_app with v; auto.
      apply chain_list_cons_inv in H2.
      destruct H2 as (-> & k & H2 & H3).
      apply chain_list_nil_inv in H3; subst k.
      constructor 2 with (u⪧t); auto.
      + btm simpl.
      + constructor.
    Qed.

    Fact btm_chain_comp n u s t : ∈-chain (S n) s t -> ∈-chain (S n) s (u⪧t).
    Proof.
      intros H.
      apply chain_chain_list in H.
      destruct H as (l & H1 & H2).
      rewrite H2. 
      apply chain_list_chain.
      apply btm_chain_list_comp; auto.
      destruct l; discriminate.
    Qed.

    Fact btm_depth_chain t : { l | ∈-chain_list l ∅ t /\ length l = ⌞t⌟ }.
    Proof.
      induction t as [ | s (ls & H1 & H2) t (lt & H3 & H4) ].
      + exists nil; simpl; split; auto; constructor.
      + destruct (le_lt_dec (S ⌞s⌟) ⌞t⌟) as [ H | H ].
        * exists lt; simpl; split.
          - apply btm_chain_list_comp; auto.
            destruct lt; try discriminate; simpl in *; lia.
          - rewrite max_r; auto.
        * exists (ls++s::nil); split.
          - apply chain_list_app with (1 := H1).
            constructor 2 with (s⪧t); auto.
            constructor.
          - rewrite app_length; simpl.
            rewrite max_l; lia.
    Qed.

    Fact bt_chain_inv_0 n x : ∈-chain n x ∅ -> n = 0 /\ x = ∅.
    Proof.
      assert (forall y, ∈-chain n x y -> y = ∅ -> n = 0 /\ x = ∅) as H.
      { induction 1 as [ | n x y z H1 H2 IH2 ]; auto.
        intros ->; destruct IH2 as (_ & ->); auto.
        apply bte_discr in H1; tauto. }
      intros G; apply (H _ G); auto.
    Qed.

  End bte_depth_and_chains.

  (** Very important to build the finite HF-model 

      Up to ≈, membership in t is finite *)

  Theorem btm_finite_t t : { l | forall s, s ∈ t <-> exists s', s ≈ s' /\ In s' l }.
  Proof.
    induction t as [ | s (ls & Hs) t (lt & Ht) ].
    + exists nil; intros s; btm simpl; simpl; firstorder.
    + exists (s::lt); intros u; btm simpl; simpl.
      rewrite Ht; split.
      * intros [ H | (s' & H1 & H2) ].
        - exists s; auto.
        - exists s'; auto.
      * intros (s' & H1 & [ H2 | H2 ]); subst; auto.
        right; exists s'; auto.
  Qed.

  Notation "x ⊆ y" := (forall u, u ∈ x -> u ∈ y) (at level 70).

  Fact bti_inv_0 x : x ⊆ ∅ <-> x = ∅.
  Proof.
    split; intros H; subst; auto.
    destruct x as [ | s t ]; auto.
    specialize (H s); revert H; btm simpl.
    intros []; auto.
  Qed.

  Fact bti_refl x : x ⊆ x.
  Proof. auto. Qed.

  Fact bti_trans x y z : x ⊆ y -> y ⊆ z -> x ⊆ z.
  Proof. intros H1 H2 k Hx; apply H2, H1; auto. Qed.

  Fact bti_comp s t : t ⊆ s⪧t.
  Proof. intro; rewrite btm_inv; auto. Qed.

  Fact bti_mono_r x s t : s ⊆ t -> x⪧s ⊆ x⪧t.
  Proof. intros ? ?; btm simpl; intros []; auto. Qed.

  Fact bte_bti s t : s ≈ t -> s ⊆ t.
  Proof. intros ? ?; apply btm_congr_r; auto. Qed.

  Fact btm_bti x s : x ∈ s -> x⪧s ⊆ s.
  Proof. intro; apply bte_bti; auto. Qed.

  Fact bti_congr_l x y t : x ≈ y -> x ⊆ t-> y ⊆ t.
  Proof.
    intros H1 H2 z Hz.
    apply H2; revert Hz; apply btm_congr_r; auto.
  Qed.

  Fact bti_congr_r x s t : s ≈ t -> x ⊆ s -> x ⊆ t.
  Proof.
    intros H1 H2 z Hz.
    generalize (H2 _ Hz); apply btm_congr_r; auto.
  Qed.

  Hint Resolve bti_refl bti_comp bti_mono_r.

  Lemma bti_dec s t : { s ⊆ t } + { ~ s ⊆ t }.
  Proof.
    destruct btm_fa_dec with (P := fun x => x ∈ t) (t := s)
      as [ (x & H1 & H2) | H1 ]; auto.
    + intros ? ?; apply btm_congr_l.
    + intros ? ?; apply btm_dec.
  Qed.

  (* I wonder whether the proof of this important result could
     be split 

     The proof can be done by generalising seteq.v
     to contraction under an equivalence (instead of @eq)
     This would avoid using decidable equality and would
     allow for the development of HF-Sets with UR-elements
     over a non-decidable type

   *)

  Lemma bti_equiv s t : s ⊆ t -> t ⊆ s -> s ≈ t.
  Proof.
    revert t; induction s as [ | x s Hs ] using bt_rect'.
    + intros t _ Ht.
      destruct t as [ | y t ]; auto.
      generalize (Ht y); btm simpl.
      intros []; auto.
    + induction t as [ | y _ t Ht ].
      * intros H _; generalize (H x).
        btm simpl; intros []; auto.
      * intros H1 H2.
        destruct (btm_dec x s) as [ H3 | H3 ].
        - apply bte_trans with s; auto.
          apply Hs.
          ++ apply bti_trans with (2 := H1); auto.
          ++ apply bti_trans with (1 := H2), btm_bti; auto.
        - assert (x ∈ y⪧t) as H4 by (apply H1; auto).
          destruct btm_partition with (1 := H4)
            as (u & H5 & H6).
          assert (s ≈ u) as H7.
          { apply Hs.
            + intros z Hz.
              assert (z ∈ x⪧u) as H7.
              { apply btm_congr_r with (1 := H5), H1, btm_inv; auto. }
              apply btm_inv in H7; destruct H7 as [ H7 | ]; auto.
              contradict H3; revert Hz; apply btm_congr_l; auto.
            + intros z Hz.
              assert (z ∈ x⪧s) as H7.
              { apply H2, btm_congr_r with (1 := in_bte_sym H5), btm_inv; auto. }
              apply btm_inv in H7; destruct H7 as [ H7 | ]; auto.
              contradict H6; revert Hz; apply btm_congr_l; auto. }
          apply bte_trans with (x⪧u); auto.
  Qed.

  Fact bte_incl_equiv s t : s ≈ t <-> s ⊆ t /\ t ⊆ s.
  Proof.
    split.
    + intro; split; apply bte_bti; auto.
    + intros []; apply bti_equiv; auto.
  Qed.

  Fact bte_ext s t : s ≈ t <-> forall x, x ∈ s <-> x ∈ t.
  Proof. rewrite bte_incl_equiv; firstorder. Qed.

  Fact bti_inv x s t : x ⊆ s⪧t <-> x ⊆ t \/ exists y, y ⊆ t /\ x ≈ s⪧y.
  Proof.
    split.
    + intros H.
      destruct (btm_dec s x) as [ H1 | H1 ].
      * destruct btm_partition with (1 := H1)
          as (y & H2 & H3).
        right; exists y; split; auto.
        intros z Hz.
        assert (z ∈ s⪧t) as C.
        { apply H.
          apply btm_congr_r with (1 := in_bte_sym H2), btm_inv; auto. }
        apply btm_inv in C; destruct C as [C|]; auto.
        contradict H3; revert Hz; apply btm_congr_l; auto.
      * left.
        intros y Hy.
        specialize (H _ Hy).
        apply btm_inv in H.
        destruct H as [ H | ]; auto.
        contradict H1.
        revert Hy; apply btm_congr_l; auto.
    + intros [ H | (y & H1 & H2) ].
      * apply bti_trans with (1 := H); auto.
      * intros z Hz.
        apply bti_congr_r with (1 := H2) in Hz; auto.
        revert Hz; btm simpl; intros []; auto.
  Qed.

  (** Set union *)

  Fixpoint bt_cup s t := 
    match s with 
      | ∅   => t
      | x⪧s => x⪧(s ∪ t)
    end
  where "s ∪ t" := (bt_cup s t).

  Theorem bt_cup_spec x s t : x ∈ s ∪ t <-> x ∈ s \/ x ∈ t.
  Proof.
    revert x; induction s as [ | y s Hs ] using bt_rect'; 
      intros x; simpl; btm simpl.
    rewrite Hs; tauto.
  Qed.

  Fact bt_cup_left s t : s ⊆ s ∪ t.
  Proof. intro; rewrite bt_cup_spec; auto. Qed.

  Fact bt_cup_right s t : t ⊆ s ∪ t.
  Proof. intro; rewrite bt_cup_spec; auto. Qed.

  Hint Resolve bt_cup_left bt_cup_right.

  Fact bt_cup_mono s s' t t' : s ≈ s' -> t ≈ t' -> s ∪ t ≈ s' ∪ t'.
  Proof.
    do 3 rewrite bte_ext; intros H1 H2 x.
    do 2 rewrite bt_cup_spec.
    rewrite H1, H2; tauto.
  Qed.
 
  Fact bt_cup_incl s t x : s ∪ t ⊆ x <-> s ⊆ x /\ t ⊆ x.
  Proof.
    split.
    + intros H; split; apply bti_trans with (2 := H); auto.
    + intros [] z; rewrite bt_cup_spec; intros []; auto.
  Qed.
   
  (** We compute the transitive closure *)

  Definition bt_transitive t := forall u v, u ∈ v -> v ∈ t -> u ∈ t.

  Fixpoint bt_tc t := 
    match t with 
      | ∅   => ∅
      | s⪧t => s⪧(↓s ∪ ↓t)
    end
  where "↓ t" := (bt_tc t).

  Fact bt_tc_congr_l u v t : u ≈ v -> u ∈ ↓t -> v ∈ ↓t.
  Proof.
    revert u v; induction t using bt_rect'; simpl; intros ? ? ?; apply btm_congr_l; auto.
  Qed.

  Fact bt_tc_congr_r u s t : s ≈ t -> u ∈ ↓s <-> u ∈ ↓t.
  Proof.
    intros H; revert H u. 
    induction 1 as [ | s t | r s t H1 IH1 H2 IH2 | s t | s t u 
                   | s s' t t' H1 IH1 H2 IH2 ]; intros v; try tauto.
    + symmetry; auto.
    + rewrite IH1; auto.
    + simpl; repeat (btm simpl || rewrite bt_cup_spec); tauto.
    + simpl; repeat (btm simpl || rewrite bt_cup_spec); tauto.
    + simpl; repeat (btm simpl || rewrite bt_cup_spec).
      rewrite IH1, IH2; split; intros [ H | [] ]; auto; left.
      * apply bte_trans with s; auto.
      * apply bte_trans with s'; auto.
  Qed.

  (** The transitive closure is composed of the x st x ∈ ... ∈ t *)

  Theorem bt_tc_spec t x : x ∈ ↓t <-> exists n, ∈-chain (S n) x t.
  Proof.
    revert x; induction t as [ | s Hs t Ht ]; intros x; simpl.
    + btm simpl; split; try tauto.
      intros (n & Hn).
      apply chain_inv_S in Hn.
      destruct Hn as (y & H1 & H2).
      apply bt_chain_inv_0 in H2.
      destruct H2 as (_ & ->).
      apply bte_discr in H1; tauto.
    + rewrite btm_inv, bt_cup_spec, Hs, Ht.
      split.
      * intros [ H | [ (n & H) | (n & H) ] ].
        - exists 0.
          constructor 2 with (s⪧t).
          ++ btm simpl.
          ++ constructor.
        - exists (S n).
          apply chain_snoc with s; auto.
        - exists n; apply btm_chain_comp; auto.
      * intros (n & H).
        apply chain_snoc_inv in H.
        destruct H as (y & H1 & H2).
        apply btm_inv in H2.
        destruct H2 as [ H2 | H2 ].
        - destruct n as [ | n ].
          ++ apply chain_inv_0 in H1; subst; auto.
          ++ right; left; exists n.
             revert H1; apply btm_chain_congr_r; auto.
        - right; right; exists n.
          apply chain_snoc with y; auto.
  Qed.

  Fact bt_tc_incr t : t ⊆ ↓t.
  Proof.
    intro; induction t; simpl; auto; btm simpl.
    rewrite bt_cup_spec; tauto.
  Qed.

  Fact bt_tc_mono s t : s ⊆ t -> ↓s ⊆ ↓t.
  Proof.
    intros H x.
    do 2 rewrite bt_tc_spec.
    intros (n & Hn).
    apply chain_snoc_inv in Hn.
    destruct Hn as (y & H1 & H2).
    exists n; apply chain_snoc with y; auto.
  Qed.

  Hint Resolve bt_tc_incr bt_tc_mono.
 
  Theorem bt_tc_trans t : bt_transitive ↓t.
  Proof.
    induction t as [ | s Hs t Ht ]; simpl; intros u v H1; btm simpl; intros H2.
    rewrite bt_cup_spec in H2.
    rewrite bt_cup_spec.
    destruct H2 as [ H2 | [ H2 | H2 ] ].
    + right; left; apply bt_tc_congr_r with (1 := H2); auto.
    + right; left; revert H2; apply Hs; auto.
    + right; right; revert H2; apply Ht; auto.
  Qed.

  Hint Resolve bt_tc_trans.

  Fact bt_trans_chain n x y t : bt_transitive t -> ∈-chain n x y -> y ∈ t -> x ∈ t. 
  Proof.
    intros Ht; induction 1 as [ | n x y z H1 H2 IH2 ]; auto.
    intros H; apply Ht with (1 := H1); auto.
  Qed.

  Hint Resolve bt_trans_chain.

  Fact bt_tc_idem t : ↓(↓t) ⊆ ↓t.
  Proof.
    intros x; rewrite bt_tc_spec.
    intros (n & Hn).
    apply chain_snoc_inv in Hn.
    destruct Hn as (y & H1 & H2).
    revert H1 H2.
    apply bt_trans_chain; auto.
  Qed.

  (*  (** Is this really needed *)
 
  Fixpoint bt_bcup x t :=
    match t with
      | ∅   => ∅ 
      | s⪧t => (x⪧s) ∪ (bt_bcup x t)
    end.

  Fact bt_bcup_spec x t u : u ∈ bt_bcup x t <-> exists k, u ∈ x⪧k /\ k ∈ t.
  Proof.
    revert u; induction t as [ | s t Ht ] using bt_rect'; intros u; simpl.
    + rewrite btm_inv_0; split; try tauto.
      intros (k & _ & Hk); revert Hk; rewrite btm_inv_0; auto.
    + rewrite btm_inv, bt_cup_spec; split.
      * intros [ H | [ H | H ] ].
        - exists s; split; auto.
          apply btm_congr_l with x; auto.
        - exists s; split; auto.
        - rewrite Ht in H.
          destruct H as (k & ? & ?).
          exists k; split; auto.
      * intros (k & H1 & H2); revert H1 H2.
        rewrite btm_inv, btm_inv.
        intros [H1|H1] [H2|H2]; auto.
        - right; left; revert H1; apply btm_congr_r; auto.
        - right; right; apply Ht; exists k.
          rewrite btm_inv; auto.
  Qed.

  *)

  (** Computes x {t1,...,tk} => {{x} ∪ t1,...,{x} ∪ tk **)

  Fixpoint bt_mcomp x t :=
    match t with
      | ∅   => ∅ 
      | s⪧t => (x⪧s) ⪧ (bt_mcomp x t)
    end.

  Fact bt_mcomp_spec x t u : u ∈ bt_mcomp x t <-> exists k, k ∈ t /\ u ≈ x⪧k.
  Proof.
    revert u; induction t as [ | s t Ht ] using bt_rect'; intros u; simpl.
    + rewrite btm_inv_0; split; try tauto.
      intros (k & Hk & _); revert Hk; rewrite btm_inv_0; auto.
    + rewrite btm_inv; split.
      * intros [ H | H ].
        - exists s; split; auto.
        - rewrite Ht in H.
          destruct H as (k & ? & ?).
          exists k; split; auto.
      * intros (k & H1 & H2); revert H1 H2.
        rewrite btm_inv, Ht.
        intros [H2|H2] H1; auto.
        - left; apply bte_trans with (1 := H1); auto.
        - right; exists k; auto.
  Qed.

  (** Powerset bti_inv x ⊆ s⪧t <-> x ⊆ t \/ exists y, y ⊆ t /\ x ≈ s⪧y *)

  Fixpoint bt_pow t :=
    match t with
      | ∅   => ∅⪧∅ 
      | x⪧t => bt_pow t ∪ bt_mcomp x (bt_pow t)
    end.

  Fact bt_pow_spec t x : x ∈ bt_pow t <-> x ⊆ t.
  Proof.
    revert x; induction t as [ | s t Ht ] using bt_rect'; intros x; simpl.
    + rewrite btm_inv, btm_inv_0, bti_inv_0, bte_inv_0; tauto.
    + rewrite bti_inv, bt_cup_spec, bt_mcomp_spec, Ht.
      split; intros [ | (y & H) ]; auto; right; exists y; 
        revert H; rewrite Ht; auto.
  Qed.

  (** Powerset of transitive is transitive *)

  Fact bt_pow_transitive t : bt_transitive t -> bt_transitive (bt_pow t).
  Proof.
    intros H x y H1.
    do 2 rewrite bt_pow_spec.
    intros H2 z Hz.
    apply H2 in H1.
    revert Hz H1; apply H.
  Qed.

  (** We start workin with pairs *)

  Fact bt_sg_inv x y : x⪧∅ ≈ y⪧∅ <-> x ≈ y.
  Proof.
    split; auto.
    rewrite bte_ext.
    intros H; specialize (H x).
    do 2 rewrite btm_inv, btm_inv_0 in H.
    apply proj1 in H; destruct H; try tauto; auto.
  Qed.

  Fact bt_sg_db_inv a x y : a⪧∅ ≈ x⪧y⪧∅ <-> a ≈ x /\ a ≈ y.
  Proof.
    split.
    + intros H.
      rewrite bte_ext in H.
      generalize (proj2 (H x)) (proj2 (H y)).
      btm simpl; intros [|[]] [|[]]; auto.
    + intros [].
      apply bte_trans with (a⪧a⪧∅); auto.
  Qed.

  Fact bt_db_inv a b x y : a⪧b⪧∅ ≈ x⪧y⪧∅ <-> a ≈ x /\ b ≈ x /\ x ≈ y
                                          \/ a ≈ x /\ b ≈ y
                                          \/ a ≈ y /\ b ≈ x.
  Proof.
    split.
    + intros H.
      rewrite bte_ext in H.
      generalize (proj1 (H a)) (proj1 (H b)) (proj2 (H x)) (proj2 (H y)).
      btm simpl; intros [|[|[]]] [|[|[]]] [|[|[]]] [|[|[]]]; auto.
    + intros [ (H1&H2&H3) | [ (H1&H2) | (H1&H2) ] ]; auto.
      * do 2 (apply in_bte_cngr; auto).
        apply bte_trans with x; auto.
      * apply bte_trans with (1 := in_bte_comm _ _ _).
        do 2 (apply in_bte_cngr; auto).
  Qed.

  (** pairs   (x,y) = { {x},{x,y} } *)

  Definition bt_pair s t := (s⪧∅)⪧(s⪧t⪧∅)⪧∅.

  Notation "⟬ s , t ⟭" := (bt_pair s t).

  Fact bt_pair_spec x s t : x ∈ ⟬ s,t⟭ <-> x ≈ s⪧∅ \/ x ≈ s⪧t⪧∅.
  Proof. unfold bt_pair; btm simpl. Qed.

  Fact bt_pair_equiv s t s' t' : ⟬s,t⟭ ≈⟬s',t'⟭  <-> s≈s' /\ t≈t'.
  Proof.
    split.
    2: intros []; unfold bt_pair; auto.
    intros H; rewrite bte_ext in H.
    assert (forall x, (x ≈ s⪧∅ \/ x ≈ s⪧t⪧∅) <-> (x ≈ s'⪧∅ \/ x ≈ s'⪧t'⪧∅)) as H'.
    { intros x; generalize (H x); do 2 rewrite bt_pair_spec; tauto. }
    clear H; revert H'; intros H.
    generalize (proj1 (H _) (or_introl (in_bte_refl _))) 
               (proj1 (H _) (or_intror (in_bte_refl _)))
               (proj2 (H _) (or_introl (in_bte_refl _))) 
               (proj2 (H _) (or_intror (in_bte_refl _))).
    repeat rewrite bt_db_inv.
    do 2 rewrite (bte_sym (_⪧_⪧_)).
    repeat rewrite bt_sg_inv.
    repeat rewrite bt_sg_db_inv.
    intros.
    repeat match goal with 
      | H : _ /\ _ |- _ => destruct H
      | H : _ \/ _ |- _ => destruct H
    end; split; auto; 
    try (apply bte_trans with s); auto;
    try (apply bte_trans with s'); auto.
  Qed.

  (** FOL encoding a triples belonging to a set *)
 
  Fact bt_enc_equiv s t : s ≈ t <-> forall x, x ∈ s <-> x ∈ t.
  Proof. apply bte_ext. Qed.

  Fact bt_enc_empty s : s ≈ ∅ <-> forall x, ~ x ∈ s.
  Proof.
    rewrite bte_ext; apply forall_equiv; intro; btm simpl.
  Qed.

  Fact bt_enc_sg s t : s ≈ t⪧∅ <-> forall x, x ∈ s <-> x ≈ t.
  Proof.
    rewrite bte_ext; apply forall_equiv; intro; btm simpl.
  Qed.

  Fact bt_enc_db u s t : u ≈ s⪧t⪧∅ <-> forall x, x ∈ u <-> x ≈ s \/ x ≈ t.
  Proof.
    rewrite bte_ext; apply forall_equiv; intros; btm simpl.
  Qed.
 
  Fact bt_enc_pair p s t : p ≈ ⟬s,t⟭  <-> (forall x, x ∈ p <-> x ≈ s⪧∅ \/ x ≈ s⪧t⪧∅).
  Proof.
    rewrite bte_ext; apply forall_equiv; intro.
    rewrite bt_pair_spec; tauto.
  Qed.

  Fact bt_enc_triple p r s t : p ≈ ⟬r,⟬s,t⟭⟭   <-> exists a, p ≈ ⟬r,a⟭ /\ a ≈ ⟬s,t⟭ .
  Proof.
    split.
    + exists ⟬s,t⟭; auto.
    + intros (a & H1 & H2).
      apply bte_trans with (1 := H1).
      apply bt_pair_equiv; auto.
  Qed.

  Fact bt_enc_rel3 a b c t : ⟬a,⟬b,c⟭⟭  ∈ t <-> exists p, p ≈ ⟬a,⟬b,c⟭⟭ /\ p ∈ t.
  Proof.
    split.
    + exists ⟬a,⟬b,c⟭⟭ ; auto.
    + intros (p & H1 & H2).
      revert H2; apply btm_congr_l; auto.
  Qed.

  Fixpoint tuple (l : list bt) :=
    match l with 
      | nil  => ∅ 
      | x::l => ⟬x,tuple l⟭
    end.

  Fact bt_enc_tuple_0 p : p ≈ tuple nil <-> p ≈ ∅.
  Proof. simpl; tauto. Qed.

  Fact bt_enc_tuple p x l : p ≈ tuple (x::l) <-> exists a, p ≈ ⟬x,a⟭ /\ a ≈ tuple l.
  Proof.
    simpl; split.
    + exists (tuple l); auto; split; auto.
    + intros (a & H1 & H2).
      apply bte_trans with (1 := H1).
      apply bt_pair_equiv; auto.
  Qed.

  Fact btm_pair_PP x y t : x ∈ t -> y ∈ t -> ⟬x,y⟭  ∈ bt_pow (bt_pow t).
  Proof.
    rewrite bt_pow_spec.
    intros Hx Hy p.
    rewrite bt_pair_spec.
    intros [H|H]; apply bte_sym in H;
    apply btm_congr_l with (1 := H); apply bt_pow_spec.
    + intros z; btm simpl; intros [ Hz | [] ].
      revert Hx; apply btm_congr_l; auto.
    + intros z; btm simpl; intros [ Hz | [ Hz | [] ] ];
        [ revert Hx | revert Hy ]; apply btm_congr_l; auto.
  Qed.
    

  (** Now how to encode the model given by k-ary relation over a finite
      set of cardinal n

      A finite set (pos n) and a k-ary relation R : (pos n)^k -> Prop
      
      1) Find a transitive btree t such that pos n injects into t
         For this, it is enough that its depth is greater that n
    
      2) forall x, y in t, both {x} and {x,y} belong to P(t)
         hence <x,y> belongs to P(P(t))

      3) and <x1,...,xk> belongs to P^2k(t) for any x1,...,xk in t 
         So P^2k(t) contains any k-ary tuple if the image of (pos n).
        
      4) Hence X = P^{2k+1}(t) contains all unary relations over k-ary 
         tuple hence all the k-ary relations over t.

      5) So we can encode R into the transitive set X = P^{2k+1}(t). 
         
      6) In the logic, we have a globally existentially quantified X_R 
         and we replace any 
      
               R (v1,...,vk) by <x1,...,xk> in X_R

         encoded according to the above description

         Perhaps follow the H10 technique to establish FOL encodability 
         into the Σ(0,2) signature

      *)

  (** We have computed the transitive closure, spec'ed and proved finite *)  

  Section HF_struct.

    (** this is not needed and relates to ITP 2016 *)

    Fact HF_cntr s t : s⪧s⪧t ≈ s⪧t.
    Proof. auto. Qed.

    Fact HF_comm s t u : s⪧t⪧u ≈ t⪧s⪧u. 
    Proof. auto. Qed.

    Fact HF_empty s t : s⪧t ≉ ∅. 
    Proof. apply bte_discr. Qed.

    Fact HF_choice s t u : s⪧t⪧u ≈ t⪧u -> s ≈ t \/ s⪧u ≈ u.
    Proof. apply btm_inv. Qed.

    Variable P : bt -> Type.

    Hypothesis (HP0 : forall s t, s ≈ t -> P s -> P t)
               (HP1 : P ∅)
               (HP2 : forall s t, P s -> P t -> P (s⪧t)).

    Theorem HF_rect : forall t, P t.
    Proof. apply bt_rect; auto. Qed.

  End HF_struct.

  Check btm_depth.
  Check btm_finite_t.
  Print bt_transitive.
  Check bt_tc_trans.
  Check bt_pow_transitive.

  Check bt_enc_equiv.
  Check bt_enc_empty.
  Check bt_enc_sg.
  Check bt_enc_db.
  Check bt_pair_equiv. 
  Check bt_enc_pair.
  Check bt_enc_triple.
  Check bt_enc_rel3. 
 
  Print tuple.
  Check bt_enc_tuple_0.
  Check bt_enc_tuple.

End btree.
