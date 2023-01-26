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

From Undecidability.FOL.TRAKHTENBROT
  Require Import notations fol_ops fo_sig fo_terms fo_logic.

Import fol_notations.

Set Implicit Arguments.

Local Notation ø := vec_nil.
Local Infix "∊" := In (at level 70, no associativity).
Local Infix "⊑" := incl (at level 70, no associativity). 

(* * The first order theory of membership *)

Section membership.

  (* We develop a theory of finitary and computable and 
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

  Definition mb_transitive t := forall x y, x ∈ y -> y ∈ t -> x ∈ t.

  Fact mb_incl_refl x : x ⊆ x.
  Proof. red; auto. Qed.

  Fact mb_incl_trans x y z : x ⊆ y -> y ⊆ z -> x ⊆ z.
  Proof. unfold mb_incl; auto. Qed.

  Fact mb_equiv_eq x y : x ≈ y <-> x ⊆ y /\ y ⊆ x.
  Proof. firstorder. Qed.

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

  Hint Resolve mb_equiv_refl mb_equiv_sym : core.

  (* The only FOL axiom: sets are characterized by their elements *)

  Definition mb_member_ext := forall x y z, x ≈ y -> x ∈ z -> y ∈ z.

  Variable (mb_axiom_ext : mb_member_ext).

  Fact mb_equiv_mem x y : x ≈ y -> forall z, x ∈ z <-> y ∈ z.
  Proof using mb_axiom_ext. split; apply mb_axiom_ext; auto. Qed.
  
   Add Parametric Morphism: (mem) with signature 
     (mb_equiv) ==> (mb_equiv) ==> (iff) as mb_mem_congruence.
  Proof using mb_axiom_ext.
    intros x y H1 a b H2; red in H1, H2; split;
     rewrite <- H2; apply mb_axiom_ext; auto.
  Qed.

  Add Parametric Morphism: (fun x y => x ⊆ y) with signature 
     (mb_equiv) ==> (mb_equiv) ==> (iff) as mb_incl_congruence.
  Proof using mb_axiom_ext.
    intros x y H1 a b H2; split; intros H z.
    + rewrite <- H1, <- H2; auto.
    + rewrite H1, H2; auto.
  Qed.

  Reserved Notation "p ≋ ⦃ a , b ⦄" (at level 70, format "p  ≋  ⦃ a , b ⦄").
  Reserved Notation "p ≋ ⦅ a , b ⦆" (at level 70, format "p  ≋  ⦅ a , b ⦆").
  Reserved Notation "t ≋ ⦉ v ⦊" (at level 70, format "t  ≋  ⦉ v ⦊").

  Definition mb_is_pair p x y := forall a, a ∈ p <-> a ≈ x \/ a ≈ y.

  Notation "p ≋ ⦃ a , b ⦄" := (mb_is_pair p a b).

  Fact mb_is_pair_comm p x y : p ≋ ⦃x,y⦄ -> p ≋ ⦃y,x⦄.
  Proof. unfold mb_is_pair; fol equiv fa; intro; tauto. Qed.

  Add Parametric Morphism: (mb_is_pair) with signature 
     (mb_equiv) ==> (mb_equiv) ==> (mb_equiv) ==> (iff) as mb_is_pair_congruence.
  Proof using mb_axiom_ext.
    intros p q H1 x x' H2 y y' H3.
    fol equiv fa; intro.
    rewrite H1, H2, H3; tauto.
  Qed.

  Fact mb_is_pair_fun p q x y : p ≋ ⦃x,y⦄ -> q ≋ ⦃x,y⦄ -> p ≈ q.
  Proof. intros H1 H2; red in H1, H2; intro; rewrite H1, H2; tauto. Qed.

  (* Many cases here, automation helps !! *)

  Fact mb_is_pair_inj p x y x' y' : 
         p ≋ ⦃x,y⦄  
      -> p ≋ ⦃x',y'⦄ 
      -> x ≈ x' /\ y ≈ y'
      \/ x ≈ y' /\ y ≈ x'.
  Proof.
    unfold mb_is_pair; intros H1 H2.
    generalize (proj1 (H2 x)) (proj1 (H2 y)); rewrite H1, H1, mb_equiv_refl_True, mb_equiv_refl_True.
    generalize (proj1 (H1 x')) (proj1 (H1 y')); rewrite H2, H2, mb_equiv_refl_True, mb_equiv_refl_True.
    intros [] [] [] []; auto.
  Qed.

  Fact mb_is_pair_inj' p x y : p ≋ ⦃x,x⦄ -> p ≋ ⦃y,y⦄ -> x ≈ y.
  Proof. intros H1 H2; generalize (mb_is_pair_inj H1 H2); tauto. Qed.

  (* Ordered pairs (x,y) := {{x},{x,y}}, Kuratowski encoding *)

  Definition mb_is_opair p x y := exists a b, a ≋ ⦃x,x⦄ /\ b ≋ ⦃x,y⦄ /\ p ≋ ⦃a,b⦄.

  Notation "p ≋ ⦅ a , b ⦆" := (mb_is_opair p a b).

  Add Parametric Morphism: (mb_is_opair) with signature 
     (mb_equiv) ==> (mb_equiv) ==> (mb_equiv) ==> (iff) as mb_is_opair_congruence.
  Proof using mb_axiom_ext.
    intros p q H1 x x' H2 y y' H3.
    do 2 (fol equiv ex; intro).
    rewrite H1, H2, H3; tauto.
  Qed.

  Fact mb_is_opair_fun p q x y : p ≋ ⦅x,y⦆ -> q ≋ ⦅x,y⦆  -> p ≈ q.
  Proof using mb_axiom_ext.
    intros (a & b & H1 & H2 & H3) (u & v & G1 & G2 & G3).
    generalize (mb_is_pair_fun H1 G1) (mb_is_pair_fun H2 G2); intros E1 E2.
    rewrite E1, E2 in H3.
    revert H3 G3; apply mb_is_pair_fun.
  Qed.

  Fact mb_is_opair_inj p x y x' y' : p ≋ ⦅x,y⦆  -> p ≋ ⦅x',y'⦆ -> x ≈ x' /\ y ≈ y'.
  Proof using mb_axiom_ext.
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
 
  (* n-tuples *)

  Fixpoint mb_is_tuple t n (v : vec X n) :=
    match v with 
      | vec_nil => forall z, z ∉ t
      | x##v    => exists t', t ≋ ⦅x,t'⦆ /\ t' ≋ ⦉v⦊
    end
  where "t ≋ ⦉ v ⦊" := (mb_is_tuple t v).

  Fact mb_is_tuple_congr p q n (v : vec X n) : p ≈ q -> p ≋ ⦉v⦊ -> q ≋ ⦉v⦊ .
  Proof using mb_axiom_ext.
    revert p q; induction v as [ | n x v IHv ]; intros p q.
    + simpl; intros E H x; rewrite <- E; auto.
    + intros E (t & H1 & H2); exists t; split; auto.
      rewrite <- E; auto.
  Qed.

  Fact mb_is_tuple_fun p q n (v : vec _ n) : p ≋ ⦉v⦊  -> q ≋ ⦉v⦊  -> p ≈ q.
  Proof using mb_axiom_ext.
    revert p q; induction v as [ | n x v IHv ]; intros p q.
    + simpl; intros H1 H2.
      apply mb_equiv_eq; split.
      * intros z Hz; apply H1 in Hz; tauto.
      * intros z Hz; apply H2 in Hz; tauto.
    + intros (p' & H1 & H2) (q' & H3 & H4).
      generalize (IHv _ _ H2 H4); intros E.
      rewrite E in H1.
      revert H1 H3; apply mb_is_opair_fun.
  Qed.

  Fact mb_is_tuple_inj t n (v w : vec _ n) p : 
         t ≋ ⦉v⦊  -> t ≋ ⦉w⦊  -> vec_pos v p ≈ vec_pos w p.
  Proof using mb_axiom_ext.
    intros H1 H2; revert t w H1 H2 p; induction v as [ | n x v IHv ]; intros t w.
    + intros _ _ p; invert pos p.
    + vec split w with y.
      intros (p & H1 & H2) (q & H3 & H4).
      destruct (mb_is_opair_inj H1 H3) as (E1 & E2).
      apply mb_is_tuple_congr with (1 := E2) in H2.
      specialize (IHv _ _ H2 H4).
      intros j; invert pos j; auto.
  Qed.

  (* mb_has_* from elements in l *)

  Definition mb_has_pairs (l : X) :=
     forall x y, x ∈ l -> y ∈ l -> exists p, p ≋ ⦃x,y⦄ .

  Definition mb_has_tuples (l : X) n :=
    forall v : vec _ n, (forall p, vec_pos v p ∈ l) -> exists t, t ≋ ⦉v⦊.

  Definition mb_is_tuple_in r n (v : vec _ n) :=
    exists t, t ≋ ⦉v⦊ /\ t ∈ r.

  Notation "t ∋ ⦉ v ⦊" := (mb_is_tuple_in t v) (at level 70, format "t  ∋  ⦉ v ⦊").

  Fact mb_is_tuple_in_congr x y n (v : vec _ n) : y ≈ x -> x ∋ ⦉v⦊ -> y ∋ ⦉v⦊ .
  Proof using mb_axiom_ext.
    intros E (t & H1 & H2); exists t; split; auto.
    rewrite  E; auto.
  Qed.

  (* mb total and functional *)

  Definition mb_is_tot n (l s : X) :=
    forall v, (forall p : pos n, vec_pos v p ∈ l) 
            -> exists x p t, x ∈ l /\ p ∈ s /\ p ≋ ⦅x,t⦆  /\ t ≋ ⦉v⦊.

  Definition mb_is_fun (l s : X) :=
    forall p q x x' y, x ∈ l -> x' ∈ l 
                    -> p ∈ s -> q ∈ s
                    -> p ≋ ⦅x,y⦆ 
                    -> q ≋ ⦅x',y⦆
                    -> x ≈ x'.

  (* Meta-level properties on the model *)

  Variable (Rdec : forall x y, { x ∈ y } + { x ∉ y }) 
           (Xfin : finite_t X).

  Local Definition lX : list X := proj1_sig Xfin.
  Local Definition HX : forall x, In x lX := proj2_sig Xfin.

  Hint Resolve HX : core.

  Fact mb_incl_choose x y : { z | z ∈ x /\ z ∉ y } + { x ⊆ y }.
  Proof using Xfin Rdec.
    set (P z := z ∈ x /\ z ∉ y).
    set (Q z := z ∈ x -> z ∈ y).
    destruct list_dec with (P := P) (Q := Q) (l := lX)
      as [ (z & _ & H2 & H3) | H ]; unfold P, Q in *; clear P Q.
    + intros z; destruct (Rdec z x); destruct (Rdec z y); tauto.
    + left; exists z; auto.
    + right; intros z; apply H; auto.
  Qed.  

  Fact mb_incl_dec x y : { x ⊆ y } + { ~ x ⊆ y }.
  Proof using Xfin Rdec.
    destruct (mb_incl_choose x y) as [ (?&?&?) |]; auto.
  Qed.

  Fact mb_equiv_dec x y : { x ≈ y } + { x ≉ y }.
  Proof using Xfin Rdec.
    destruct (mb_incl_dec x y); [ destruct (mb_incl_dec y x) | ].
    1: left; apply mb_equiv_eq; auto. 
    all: right; rewrite mb_equiv_eq; tauto.
  Qed.

  Hint Resolve mb_equiv_dec : core.

  Fact mb_is_pair_dec p x y : { p ≋ ⦃x,y⦄ } + { ~ p ≋ ⦃x,y⦄ }.
  Proof using Xfin Rdec.
    unfold mb_is_pair.
    apply (fol_quant_sem_dec fol_fa); auto; intros u.
    apply fol_equiv_dec; auto.
    apply (fol_bin_sem_dec fol_disj); auto.
  Qed.

  Hint Resolve mb_is_pair_dec : core.

  Fact mb_is_opair_dec p x y : { p ≋ ⦅x,y⦆  } + { ~ p ≋ ⦅x,y⦆  }.
  Proof using Xfin Rdec.
    unfold mb_is_opair.
    do 2 (apply (fol_quant_sem_dec fol_ex); auto; intro).
    repeat (apply (fol_bin_sem_dec fol_conj); auto).
  Qed.

  Hint Resolve mb_is_opair_dec : core.

  Fact mb_is_tuple_dec t n (v : vec _ n) : { t ≋ ⦉v⦊  } + { ~ t ≋ ⦉v⦊  }.
  Proof using Xfin Rdec.
    revert t; induction v as [ | x n v IHv ]; intros t.
    + apply (fol_quant_sem_dec fol_fa); auto; intro.
      apply (fol_bin_sem_dec fol_imp); auto.
    + simpl; apply (fol_quant_sem_dec fol_ex); auto; intro.
      apply (fol_bin_sem_dec fol_conj); auto.
  Qed.

  Hint Resolve mb_is_tuple_dec : core.

  Fact mb_is_tuple_in_dec r n (v : vec _ n) : { r ∋ ⦉v⦊  } + { ~ r ∋ ⦉v⦊  }.
  Proof using Xfin Rdec.
    apply (fol_quant_sem_dec fol_ex); auto; intro.
    apply (fol_bin_sem_dec fol_conj); auto.
  Qed.

End membership.

Section FOL_encoding.

  (* First order encoding here *)

  (* Maybe we can redo the whole devel here with fo_definable.v *)

  Notation Σ2 := (Σrel 2).
  Variable (Y : Type) (M2 : fo_model Σ2 Y).

  Let mem a b := fom_rels M2 tt (a##b##ø).
  Infix "∈ₘ" := mem (at level 59, no associativity).

  Definition Σ2_mem x y := @fol_atom Σ2 tt (£x##£y##ø).
  Infix "∈" := Σ2_mem.

  Definition Σ2_non_empty l := ∃ 0 ∈ (1+l). 
  Definition Σ2_incl x y := ∀ 0 ∈ (S x) ⤑ 0 ∈ (S y).
  Definition Σ2_equiv x y := ∀ 0 ∈ (S x) ↔ 0 ∈ (S y).

  Infix "⊆" := Σ2_incl.
  Infix "≈" := Σ2_equiv.

  Definition Σ2_transitive t := ∀∀ 1 ∈ 0 ⤑ 0 ∈ (2+t) ⤑ 1 ∈ (2+t).

  Definition Σ2_extensional := ∀∀∀ 2 ≈ 1 ⤑ 2 ∈ 0 ⤑ 1 ∈ 0.

  Definition Σ2_is_pair p x y := ∀ 0 ∈ (S p) ↔ 0 ≈ S x ⟇ 0 ≈ S y.

  Definition Σ2_is_opair p x y := 
         ∃∃   Σ2_is_pair 1    (2+x) (2+x)
            ⟑ Σ2_is_pair 0    (2+x) (2+y)
            ⟑ Σ2_is_pair (2+p) 1     0.

  Fact Σ2_is_opair_vars p x y : fol_vars (Σ2_is_opair p x y) ⊑ p::x::y::nil.
  Proof. cbv; tauto. Qed.

  (* A 0-tuple <> is the empty set
     A (1+n)-tuple <x##v> is a pair (x,k) where k is the n-tuple <v>
   *)

  Fixpoint Σ2_is_tuple t n : vec nat n -> fol_form Σ2 :=
    match n with 
      | 0       => fun _ => ∀ 0 ∈ (S t) ⤑ ⊥
      | S n     => fun v => ∃ Σ2_is_opair (S t) (S (vec_head v)) 0 
                            ⟑ Σ2_is_tuple 0 (vec_map S (vec_tail v))
    end.

  Fact Σ2_is_tuple_vars t n v : fol_vars (@Σ2_is_tuple t n v) ⊑ t::vec_list v.
  Proof.
    revert t v; induction n as [ | n IHn ]; intros t v.
    + vec nil v; cbv; tauto.
    + vec split v with x; simpl Σ2_is_tuple.
      intros i; rewrite fol_vars_quant, in_flat_map.
      intros (j & H1 & H2).
      rewrite fol_vars_bin, in_app_iff in H1.
      destruct H1 as [ H1 | H1 ].
      * apply Σ2_is_opair_vars in H1.
        destruct H1 as [ | [ | [ | [] ] ] ]; subst j; simpl in *; tauto.
      * apply IHn in H1.
        destruct H1 as [ <- | H1 ].
        - simpl in *; tauto.
        - rewrite vec_list_vec_map, in_map_iff in H1.
          destruct H1 as (y & <- & H1); simpl in *.
          destruct H2 as [ -> | [] ]; tauto.
  Qed.

  (* v is n-tuple belonging to r *) 

  Definition Σ2_is_tuple_in r n v := ∃ @Σ2_is_tuple 0 n (vec_map S v) ⟑ 0 ∈ (S r).

  Fact Σ2_is_tuple_in_vars r n v : fol_vars (@Σ2_is_tuple_in r n v) ⊑ r::vec_list v.
  Proof.
    unfold Σ2_is_tuple_in.
    intros x; rewrite fol_vars_quant, in_flat_map.
    intros (y & H1 & H2).
    rewrite fol_vars_bin, in_app_iff in H1.
    destruct H1 as [ H1 | H1 ].
    + apply Σ2_is_tuple_vars in H1.
      simpl in H1; rewrite vec_list_vec_map, in_map_iff in H1.
      destruct H1 as [ <- | (z & <- & H1) ]; simpl in *; try tauto.
      destruct H2 as [ <- | [] ]; auto.
    + simpl in H1.
      destruct H1 as [ <- | [ <- | [] ] ]; simpl in *; tauto.
  Qed.

  Definition Σ2_has_tuples l n :=
       fol_mquant fol_fa n ( (fol_vec_fa (vec_set_pos (fun p : pos n => pos2nat p ∈ (l+n))))
                                         ⤑ ∃ Σ2_is_tuple 0 (vec_set_pos (fun p : pos n => S (pos2nat p)))).

  Definition Σ2_is_tot n l s :=
       fol_mquant fol_fa n ( (fol_vec_fa (vec_set_pos (fun p : pos n => pos2nat p ∈ (l+n))))
                                         ⤑ ∃∃∃ 2 ∈ ((3+l)+n) ⟑ 1 ∈ ((3+s)+n) ⟑ Σ2_is_opair 1 2 0 ⟑ @Σ2_is_tuple 0 n (vec_set_pos (fun p : pos n => 3+pos2nat p)) ).

  Definition Σ2_is_fun l s :=
    ∀∀∀∀∀ 2 ∈ (5+l) ⤑ 1 ∈ (5+l) ⤑
          4 ∈ (5+s) ⤑ 3 ∈ (5+s) ⤑
          Σ2_is_opair 4 2 0 ⤑
          Σ2_is_opair 3 1 0 ⤑
          2 ≈ 1.

  Definition Σ2_list_in l lv := fol_lconj (map (fun x => x ∈ l) lv).

  Notation "⟪ A ⟫" := (fun ψ => fol_sem M2 ψ A).

  Section semantics.

    Fact Σ2_transitive_spec t ψ : ⟪Σ2_transitive t⟫ ψ = mb_transitive mem (ψ t).
    Proof. reflexivity. Qed.
 
    Fact Σ2_non_empty_spec l ψ : ⟪Σ2_non_empty l⟫ ψ = exists x, x ∈ₘ ψ l.
    Proof. reflexivity. Qed.

    Fact Σ2_incl_spec x y ψ : ⟪Σ2_incl x y⟫ ψ = mb_incl mem (ψ x) (ψ y).
    Proof. reflexivity. Qed.

    Fact Σ2_equiv_spec x y ψ : ⟪Σ2_equiv x y⟫ ψ = mb_equiv mem (ψ x) (ψ y).
    Proof. reflexivity. Qed. 

    Fact Σ2_extensional_spec ψ : ⟪Σ2_extensional⟫ ψ = mb_member_ext mem.
    Proof. reflexivity. Qed.

    Fact Σ2_is_pair_spec p x y ψ : ⟪Σ2_is_pair p x y⟫ ψ = mb_is_pair mem (ψ p) (ψ x) (ψ y).
    Proof. reflexivity. Qed.

    Fact Σ2_is_opair_spec p x y ψ : ⟪Σ2_is_opair p x y⟫ ψ = mb_is_opair mem (ψ p) (ψ x) (ψ y).
    Proof. reflexivity. Qed.

    Fact Σ2_is_tuple_spec t n v ψ : ⟪@Σ2_is_tuple t n v⟫ ψ <-> mb_is_tuple mem (ψ t) (vec_map ψ v).
    Proof.
      induction n as [ | n IHn ] in t, v, ψ |- *.
      + vec nil v; reflexivity.
      + vec split v with x.
        simpl Σ2_is_tuple.
        simpl mb_is_tuple.
        rewrite fol_sem_quant_fix.
        fol equiv ex; intros y.
        rewrite fol_sem_bin_fix.
        fol equiv conj.
        * reflexivity.
        * rewrite IHn, vec_map_map; reflexivity. 
    Qed.

    Fact Σ2_is_tuple_in_spec r n v ψ : ⟪@Σ2_is_tuple_in r n v⟫ ψ <-> mb_is_tuple_in mem (ψ r) (vec_map ψ v).
    Proof.
      simpl; fol equiv ex; intro; fol equiv conj.
      + rewrite Σ2_is_tuple_spec, vec_map_map; simpl; reflexivity.
      + reflexivity.
    Qed.

    Fact Σ2_has_tuples_spec l n ψ : ⟪Σ2_has_tuples l n⟫ ψ <-> mb_has_tuples mem (ψ l) n.
    Proof.
      unfold Σ2_has_tuples.
      rewrite fol_sem_mforall.
      fol equiv fa; intros v.
      rewrite fol_sem_bin_fix.
      fol equiv imp.
      + rewrite fol_sem_vec_fa.
        fol equiv; intros p.
        rew vec; simpl.
        now rewrite env_vlift_fix0, env_vlift_fix1.
      + rewrite fol_sem_quant_fix.
        fol equiv ex; intros x.
        rewrite Σ2_is_tuple_spec; simpl.
        fol equiv rel.
        apply vec_pos_ext; intros p.
        rew vec; simpl.
        rewrite env_vlift_fix0; auto.
    Qed.

    Fact Σ2_is_fun_spec l s ψ : ⟪Σ2_is_fun l s⟫ ψ = mb_is_fun mem (ψ l) (ψ s).
    Proof. reflexivity. Qed.

    Fact Σ2_is_tot_spec n l s ψ : ⟪Σ2_is_tot n l s⟫ ψ <-> mb_is_tot mem n (ψ l) (ψ s).
    Proof. 
      unfold Σ2_is_tot, mb_is_tot.
      rewrite fol_sem_mforall.
      fol equiv; intros v.
      rewrite fol_sem_bin_fix.
      fol equiv imp.
      + rewrite fol_sem_vec_fa.
        fol equiv; intros p.
        rew vec; simpl. 
        rewrite env_vlift_fix0, env_vlift_fix1; tauto.
      + rewrite fol_sem_quant_fix; fol equiv ex; intros x.
        rewrite fol_sem_quant_fix; fol equiv ex; intros p.
        rewrite fol_sem_quant_fix; fol equiv ex; intros t.
        do 3 (rewrite fol_sem_bin_fix).
        repeat fol equiv conj.
        * simpl; rewrite env_vlift_fix1; tauto.
        * simpl; rewrite env_vlift_fix1; tauto.
        * rewrite Σ2_is_opair_spec; simpl; tauto.
        * rewrite Σ2_is_tuple_spec; simpl.
          fol equiv.
          apply vec_pos_ext; intros q; rew vec.
          simpl; rewrite env_vlift_fix0; auto.
    Qed.

    Fact Σ2_list_in_spec l lv ψ : ⟪Σ2_list_in l lv⟫ ψ <-> forall x, x ∊ lv -> ψ x ∈ₘ ψ l.
    Proof.
      unfold Σ2_list_in; rewrite fol_sem_lconj.
      split.
      + intros H x Hx.
        apply (H (_ ∈ _)), in_map_iff.
        exists x; auto.
      + intros H f; rewrite in_map_iff.
        intros (x & <- & ?); apply H; auto.
    Qed.

  End semantics.

End FOL_encoding. 
