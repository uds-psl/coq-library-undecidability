(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Bool.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_list finite fin_quotient fin_dec utils_decidable.

From Undecidability.TRAKHTENBROT
  Require Import notations utils decidable.

Set Implicit Arguments.

Local Infix "∊" := In (at level 70, no associativity).

Section discernable.

  Variable (X : Type).

  Definition discernable x y := exists δ : X -> bool, δ x <> δ y.

  Infix "≢" := discernable (at level 70, no associativity).

  Fact discernable_equiv1 x y : x ≢ y <-> exists δ, δ x = true /\ δ y = false.
  Proof.
    split.
    + intros (f & Hf).
      case_eq (f x); intros Hx.
      * exists f; split; auto.
        now rewrite Hx in Hf; destruct (f y).
      * exists (fun x => negb (f x)).
        rewrite Hx in *; split; auto.
        now destruct (f y).
    + intros (f & E1 & E2); exists f.
      now rewrite E1, E2.
  Qed.

  Definition undiscernable x y := forall δ : X -> bool, δ x = δ y.

  Infix "≡" := undiscernable (at level 70, no associativity).

  Fact discernable_undiscernable x y : x ≢ y -> x ≡ y -> False.
  Proof. intros (f & Hf) H; apply Hf, H. Qed.

  Fact undiscernable_spec x y : x ≡ y <-> ~ x ≢ y.
  Proof.
    split.
    + intros H1 H2; revert H2 H1; apply discernable_undiscernable.
    + intros H f.
      destruct (bool_dec (f x) (f y)); auto.
      destruct H; exists f; auto.
  Qed.

  Fact undiscernable_refl x : x ≡ x.
  Proof. red; auto. Qed.

  Fact undiscernable_sym x y : x ≡ y -> y ≡ x.
  Proof. red; auto. Qed.

  Fact undiscernable_trans x y z : x ≡ y -> y ≡ z -> x ≡ z.
  Proof. unfold undiscernable; eauto. Qed.

  Fact undiscernable_discrete D (δ : X -> D) x y : discrete D -> x ≡ y -> δ x = δ y.
  Proof.
    intros d H.
    set (g z := if d (δ x) (δ z) then true else false).
    specialize (H g); unfold g in H.
    destruct (d (δ x) (δ x)) as [ _ | [] ]; auto.
    destruct (d (δ x) (δ y)) as [ | ]; easy.
  Qed.

  Fact discrete_undiscernable_implies_equal x y : discrete X -> x ≡ y -> x = y.
  Proof. intro; now apply undiscernable_discrete with (δ := fun x => x). Qed.

  Fact undiscernable_Prop_dec x y : x ≡ y -> forall P, (forall x, decidable (P x)) -> P x <-> P y.
  Proof.
    intros H P HP.
    set (f x := if HP x then true else false).
    specialize (H f); unfold f in H.
    destruct (HP x); destruct (HP y); try tauto; easy.
  Qed.

  Hypothesis (H2 : forall x y, decidable (x ≢ y)).

  Fact discernable_dec_undiscernable_dec x y : decidable (x ≡ y).
  Proof using H2.
    destruct (H2 x y); [ right | left ]; rewrite undiscernable_spec; tauto.
  Qed.

  Hint Resolve discernable_dec_undiscernable_dec : core.

  (* There is a simultaneously discerning function for a list l *)

  Definition discriminable_list l := 
    { D & { _ : discrete D & { _ : finite_t D & { δ : X -> D 
             | forall x y, x ∊ l -> y ∊ l -> x ≡ y <-> δ x = δ y } } } }.

  Hint Resolve undiscernable_refl undiscernable_sym undiscernable_trans : core.

  Theorem discernable_discriminable_list l : discriminable_list l. 
  Proof using H2.
    apply DEC_PER_list_proj_finite_discrete with (l := l) (R := undiscernable).
    + split; eauto.
    + red; apply discernable_dec_undiscernable_dec.
    + intros; auto.
  Qed.

  (* There is a simultaneously discerning function for a type *)

  Definition discriminable_type := 
    { D & { _ : discrete D & { _ : finite_t D & { δ : X -> D 
             | forall x y, x ≡ y <-> δ x = δ y } } } }.

  Hypothesis (H1 : finite_t X).

  (* undiscernable is equivalent to a equality after mapping on some finite datatype *)

  Theorem finite_discernable_discriminable_type : discriminable_type. 
  Proof using H1 H2.
    destruct H1 as (l & Hl).
    destruct discernable_discriminable_list with l
      as (D & D1 & D2 & f & Hf).
    exists D, D1, D2, f; intros; eauto.
  Qed.

End discernable.
