(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Bool Lia.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import wf_finite.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops fo_terms fo_logic.

Set Implicit Arguments.

Local Notation ø := vec_nil.

Definition Σrel (n : nat) : fo_signature.
Proof.
  exists Empty_set unit.
  + intros [].
  + exact (fun _ => n).
Defined.

Section Sig3_Sig2.

  Reserved Notation "x ∈ y" (at level 59, no associativity).
  Reserved Notation "x ≈ y" (at level 59, no associativity).
  Reserved Notation "x ⊆ y" (at level 59, no associativity).

  Notation Σ2 := (Σrel 2).
  Notation Σ3 := (Σrel 3).
 
  Variable M2 : fo_model Σ2.
  Variable M3 : fo_model Σ3.

  Check fol_atom Σ2 tt.

  Notation "x ∈ y" := (fol_atom Σ2 tt (£x##£y##ø)).
 
  Definition Σ2_incl x y := ∀ 0 ∈ (S x) ⤑ 0 ∈ (S y).
  Definition Σ2_equiv x y := ∀ 0 ∈ (S x) ↔ 0 ∈ (S y).

  Infix "≈" := Σ2_equiv.
  Infix "⊆" := Σ2_incl.

  (* is_otriple t x y z := exists p, is_opair p x y /\ is_opair t p z. *)

  Definition Σ2_is_pair p x y : fol_form Σ2 := ∀ 0 ∈ (S p) ↔ 0 ≈ S x ⟇ 0 ≈ S y.

  Definition Σ2_is_opair p x y := ∃∃ Σ2_is_pair 1    (2+x) (2+x)
                                   ⟑ Σ2_is_pair 0    (2+x) (2+y)
                                   ⟑ Σ2_is_pair (2+p) 1     0.

  Definition Σ2_is_otriple p x y z := ∃ Σ2_is_opair 0     (S x) (S y)
                                      ⟑ Σ2_is_opair (S p)  0    (S z).

  Definition Σ2_is_triple_in r x y z := ∃ Σ2_is_otriple 0 (S x) (S y) (S z) ⟑ 0 ∈ (S r).
 

  Definition Σ3_var : fo_term nat (ar_syms Σ3) -> nat.
  Proof.
    intros [ n | [] ]; exact n.
  Defined.

  Fixpoint Σ3_Σ2 (l r : nat) (A : fol_form Σ3) : fol_form Σ2 :=
    match A with
      | ⊥              => ⊥
      | fol_atom _ _ v => Σ2_is_triple_in r (Σ3_var (vec_head v)) 
                                            (Σ3_var (vec_head (vec_tail v)))
                                            (Σ3_var (vec_head (vec_tail (vec_tail v))))
      | fol_bin b A B  => fol_bin b (Σ3_Σ2 l r A) (Σ3_Σ2 l r B)
      | fol_quant fol_fa A  => ∀ 0 ∈ (S l) ⤑ Σ3_Σ2 (S l) (S r) A
      | fol_quant fol_ex A  => ∃ 0 ∈ (S l) ⟑ Σ3_Σ2 (S l) (S r) A
     end.

  Notation P := (fun x y z => fom_rels M3 tt (x##y##z##ø)).

  Variable R : M3 -> M2 -> Prop.

  (** R represent for M3 = { x | x in l } and M2 the relation 

           fun x y => proj1_sig x ≈ y  *)

  Definition HR1 (l r : M2) := forall x, exists y, fom_rels M2 tt (y##l##ø) /\ R x y.
  Definition HR2 (l r : M2) := forall y, fom_rels M2 tt (y##l##ø) -> exists x, R x y.
  Definition HR4 (l r : M2) := forall a b c a' b' c' ψ,
                                               R a a'
                                            -> R b b'
                                            -> R c c' 
                                            -> fom_rels M3 tt (a##b##c##ø)
                                           <-> fol_sem M2 ψ↑r↑a'↑b'↑c' (Σ2_is_triple_in 3 2 1 0).

  Theorem Σ3_Σ2_correct (A : fol_form Σ3) l r φ ψ :
            HR1 (ψ l) (ψ r) -> HR2 (ψ l) (ψ r) -> HR4 (ψ l) (ψ r)
        -> (forall x, In x (fol_vars A) -> R (φ x) (ψ x))
        -> fol_sem M3 φ A <-> fol_sem M2 ψ (Σ3_Σ2 l r A).
  Proof.
    revert l r φ ψ.
    induction A as [ | [] | b A HA B HB | [] A HA ]; intros l r phi psy H1 H2 H4 H.
    1: simpl; tauto.
    2: { simpl; apply fol_bin_sem_ext.
         + apply HA; intros; auto; apply H, in_or_app; simpl; auto.
         + apply HB; intros; auto; apply H, in_or_app; simpl; auto. }
    2: { simpl; split.
         + intros (x & Hx).
           destruct (H1 x) as (y & G1 & G2).
           exists y; split.
           * rew fot; simpl; auto.
           * revert Hx; apply HA; auto.
             intros [ | n ]; simpl; auto.
             intros; apply H; simpl; apply in_flat_map; exists (S n); simpl; auto.
         + intros (y & G1 & G2); revert G1 G2; rew fot; simpl; intros G1 G2.
           destruct (H2 _ G1) as (x & G3).
           exists x; revert G2; apply HA; auto.
           intros [ | n ]; simpl; auto.
           intros; apply H; simpl; apply in_flat_map; exists (S n); simpl; auto. } 
  2: { simpl; split.
       + intros G1 y; rew fot; simpl; intros G2.
         destruct (H2 _ G2) as (x & G3).
         generalize (G1 x); apply HA; auto.
         intros [ | n ]; simpl; auto.
         intros; apply H; simpl; apply in_flat_map; exists (S n); simpl; auto.
       + intros G1 x.
         destruct (H1 x) as (y & G2 & G3).
         generalize (G1 _ G2); apply HA; auto.
         intros [ | n ]; simpl; auto.
         intros; apply H; simpl; apply in_flat_map; exists (S n); simpl; auto. }
  1: { revert H.
       vec split v with a; vec split v with b; vec split v with c; vec nil v; clear v.
       revert a b c; intros [ a | [] ] [ b | [] ] [ c | [] ] H; simpl in H.
       split.
       + intros G1; simpl in G1; revert G1; rew fot; intros G1.
         unfold Σ3_Σ2; simpl Σ3_var.
         red in H4.
         rewrite (@H4 _ _ _ (psy a) (psy b) (psy c) psy) in G1; auto.
       + unfold Σ3_Σ2; simpl Σ3_var; intros G1.
         simpl; rew fot.
         rewrite (@H4 _ _ _ (psy a) (psy b) (psy c) psy); auto. }
  Qed.

End Sig3_Sig2.
